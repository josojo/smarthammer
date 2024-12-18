import sys
from hammer.api.logging import LogStreamHandler
from hammer.lean.server import LeanServer
from hammer.proof.proof import ProofSearchState, Hypothesis
from hammer.api.claude.client import Client
from hammer.proof.retry import retry_until_success
from rq import get_current_job
import logging

logger = logging.getLogger(__name__)


def iterate_until_valid_proof(
    proof_state: ProofSearchState,
    hyptotheses_number,
    client: Client,
    lean_client: LeanServer,
    max_iteration=1,
    max_correction_iteration=1,
    verbose=False,
):
    cnt = 0
    starting_code = ""
    while cnt < max_iteration:
        proof_candidate = proof_state.generate_proof_candidate_for_hypotheses(
            client, hyptotheses_number, starting_code, verbose
        )
        if proof_candidate:
            code = proof_state.hypothesis_as_code(hyptotheses_number) + proof_candidate
            result = lean_client.run_code(code, 0, verbose)
            if isinstance(result, dict) and (
                "messages" not in result
                or not any(
                    msg.get("severity") == "error" for msg in result.get("messages", [])
                )
            ):
                return proof_candidate
            else:
                proof = retry_until_success(
                    client,
                    lean_client,
                    proof_state.previous_code,
                    proof_state.hypothesis_as_code(hyptotheses_number),
                    proof_candidate,
                    result,
                    max_correction_iteration,
                    verbose,
                )
                if proof:
                    return proof
        cnt += 1
    return None


def iterate_until_valid_final_proof(
    proof_state: ProofSearchState,
    client: Client,
    lean_client: LeanServer,
    max_iteration=1,
    max_correction_iteration=1,
    verbose=False,
):
    cnt = 0
    starting_code = ""
    while cnt < max_iteration:
        proof_candidate = proof_state.generate_final_proof(
            client, starting_code, verbose
        )
        if proof_candidate:
            code = proof_state.get_theorem_code() + proof_candidate
            result = lean_client.run_code(code, 0, verbose)
            if isinstance(result, dict) and (
                "messages" not in result
                or not any(
                    msg.get("severity") == "error" for msg in result.get("messages", [])
                )
            ):
                return proof_candidate
            else:
                proof = retry_until_success(
                    client,
                    lean_client,
                    proof_state.previous_code,
                    proof_state.get_theorem_code(),
                    proof_candidate,
                    result,
                    max_correction_iteration,
                    verbose,
                )
                if proof:
                    return proof
        cnt += 1
    return None


def prove_theorem_via_hypotheses_search(
    proof_state: ProofSearchState,
    api_client: Client,
    lean_client: LeanServer,
    max_iteration_hypotheses_proof=1,
    max_correction_iteration_hypotheses_proof=1,
    verbose=False,
):
    proof_state.add_hypotheses(api_client, verbose)
    logger.debug("Added hypotheses")
    logger.debug(f"Theoretical hypotheses: {proof_state.theoretical_hypotheses}")

    # Try to generate proofs for different numbers of hypotheses
    valid_proofs = []
    not_valid_formulations = []
    for i in range(len(proof_state.theoretical_hypotheses)):
        try:
            proof = iterate_until_valid_proof(
                proof_state,
                i,
                api_client,
                lean_client,
                max_iteration_hypotheses_proof,
                max_correction_iteration_hypotheses_proof,
                verbose,
            )
            if proof:
                proof_state.proven_hypotheses.append(
                    Hypothesis(
                        "p" + str(len(proof_state.proven_hypotheses)),
                        proof_state.theoretical_hypotheses[i],
                        proof,
                    )
                )
                valid_proofs.append(i)
        except Exception as e:
            logger.error(f"Error while proving hypothesis: {e}")
            not_valid_formulations.append(i)
    # Remove the valid proofs from the list
    # Combine valid and invalid indices and sort in reverse order to safely remove from list
    indices_to_remove = sorted(valid_proofs + not_valid_formulations, reverse=True)
    for i in indices_to_remove:
        proof_state.theoretical_hypotheses.pop(i)
    logger.info(
        f"In total {len(proof_state.proven_hypotheses)} hypotheses proven from initially "
        f"{len(proof_state.theoretical_hypotheses) + len(proof_state.proven_hypotheses)} available ones"
    )
    return proof_state


def find_final_proof(
    proof_state: ProofSearchState,
    api_client,
    lean_client,
    max_iteration_final_proof=1,
    max_iternation_correction_proof=1,
    verbose=False,
):
    proof = iterate_until_valid_final_proof(
        proof_state,
        api_client,
        lean_client,
        max_iteration_final_proof,
        max_iternation_correction_proof,
        verbose,
    )
    if proof:
        proof_state.proof = proof_state.build_final_proof(proof)
    return proof_state.proof


def prove_theorem(**kwargs):
    task_id = kwargs.pop("task_id", None)

    # Set up logging handler for this task if task_id is provided
    if task_id:
        # Set root logger to DEBUG level
        root_logger = logging.getLogger()
        root_logger.setLevel(logging.DEBUG)

        # Create and configure the LogStreamHandler
        log_handler = LogStreamHandler(task_id)
        log_handler.setLevel(logging.DEBUG)

        # Create formatter and add it to the handler
        formatter = logging.Formatter("%(message)s")
        log_handler.setFormatter(formatter)

        # Add handler to root logger
        root_logger.addHandler(log_handler)

        logger.debug(f"Starting proof for task {task_id}")

    name = kwargs["name"]
    hypotheses = kwargs["hypotheses"]
    codeEnv0 = kwargs["code_for_env_0"]
    goal = kwargs["goal"]
    max_iteration_hypotheses_proof = kwargs["max_iteration_hypotheses_proof"]
    max_correction_iteration_hypotheses_proof = kwargs[
        "max_correction_iteration_hypotheses_proof"
    ]
    max_iteration_final_proof = kwargs["max_iteration_final_proof"]
    max_correction_iteration_final_proof = kwargs[
        "max_correction_iteration_final_proof"
    ]
    verbose = kwargs["verbose"]

    lean_client = LeanServer(kwargs["code_for_env_0"])
    proof_state = ProofSearchState(name, hypotheses, codeEnv0, goal)
    claude_client = Client()

    prove_theorem_via_hypotheses_search(
        proof_state,
        claude_client,
        lean_client,
        max_iteration_hypotheses_proof,
        max_correction_iteration_hypotheses_proof,
        verbose=verbose,
    )
    find_final_proof(
        proof_state,
        claude_client,
        lean_client,
        max_iteration_final_proof,
        max_correction_iteration_final_proof,
        verbose,
    )

    # Remove log capture handling at the end since logs are streamed in real-time
    return proof_state


def main(name, hypothesis, goal):
    """Main entry point for the theorem prover."""

    try:
        # proof_state = prove_theorem(name, hypothesis, goal, 1,1,1,1, True)
        proof_state = prove_theorem(name, hypothesis, goal, 2, 3, 3, 4, True)
        if proof_state.proof:
            print(f"Proof found for theorem {name}:")
            print(proof_state.proof)
        else:
            print(f"Could not find proof for theorem {name}")
    except Exception as e:
        print(f"Error while proving theorem: {e}")
        sys.exit(1)


if __name__ == "__main__":
    name = "thm1"
    hypotheses = ["(n : ℕ)", "(oh0 : 0 < n)"]
    goal = "Nat.gcd (21*n + 4) (14*n + 3) = 1"
    main(name, hypotheses, goal)
