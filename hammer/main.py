import sys
from hammer.api.logging import LogStreamHandler, ContextualLoggerAdapter
from hammer.lean.server import LeanServer
from hammer.proof.proof import ProofSearchState, Hypothesis
from hammer.api.claude.client import Client as ClaudeClient
from hammer.api.deepseek.client import Client as DeepSeekClient
from hammer.api.base_client import AIClient
from hammer.proof.retry import retry_until_success
from rq import get_current_job
import logging
from dotenv import load_dotenv
import os

load_dotenv()
deepseek_url = os.getenv("DEEPSEEK_URL")
logger = logging.getLogger(__name__)
contextual_logger = ContextualLoggerAdapter(logger, {"step": "Starting Proof"})


def iterate_until_valid_proof(
    proof_state: ProofSearchState,
    hyptotheses_number,
    client: AIClient,
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
    client: AIClient,
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
                try:
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
                except Exception as e:
                    logger.error(f"Error while proving final proof: {e}")
        cnt += 1
    return None


def prove_theorem_via_hypotheses_search(
    proof_state: ProofSearchState,
    api_client_for_hypothesis_search: AIClient,
    api_client_for_proofing: list[AIClient],
    lean_client: LeanServer,
    max_iteration_hypotheses_proof=1,
    max_correction_iteration_hypotheses_proof=1,
    verbose=False,
    log_handler: LogStreamHandler = None,
):

    if not log_handler:
        log_handler = LogStreamHandler("")
    logger.debug("Searching for hypotheses:")
    proof_state.add_hypotheses(api_client_for_hypothesis_search, verbose)
    logger.debug("Added hypotheses")
    logger.debug(f"Theoretical hypotheses: {proof_state.theoretical_hypotheses}")

    # Try to generate proofs for different numbers of hypotheses
    valid_proofs = []
    not_valid_formulations = []
    for i in range(len(proof_state.theoretical_hypotheses)):
        log_handler.set_step(f"Proofing Hypotheses {i}")
        logger.debug(f"Searching proof for hypothesis {i}")
        for api_client in api_client_for_proofing:
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

    # Count occurrences of each index in not_valid_formulations
    not_valid_counts = {
        i: not_valid_formulations.count(i) for i in set(not_valid_formulations)
    }

    # Determine indices to remove based on the number of appearances in not_valid_formulations
    indices_to_remove = [
        i
        for i in not_valid_counts
        if not_valid_counts[i] == len(api_client_for_proofing)
    ]

    # Sort in reverse order to safely remove from list
    indices_to_remove = sorted(indices_to_remove, reverse=True)

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

        contextual_logger.extra["step"] = "Starting Proof"
        contextual_logger.debug(f"Starting proof for task {task_id}")

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

    max_iteration_hypotheses_proof = 3
    max_correction_iteration_hypotheses_proof = 4
    lean_client = LeanServer(kwargs["code_for_env_0"])
    proof_state = ProofSearchState(name, hypotheses, codeEnv0, goal)
    claude_client = ClaudeClient()
    deepSeek_client = DeepSeekClient(base_url=deepseek_url)
    api_client_for_proofing = [claude_client, deepSeek_client]
    api_client_for_proofing = [deepSeek_client]
    api_client_for_hypothesis_search = claude_client

    log_handler.set_step("Adding Hypotheses")
    prove_theorem_via_hypotheses_search(
        proof_state,
        api_client_for_hypothesis_search,
        api_client_for_proofing,
        lean_client,
        max_iteration_hypotheses_proof,
        max_correction_iteration_hypotheses_proof,
        verbose=verbose,
        log_handler=log_handler,
    )

    log_handler.set_step("Building Final Proof")
    find_final_proof(
        proof_state,
        deepSeek_client,
        lean_client,
        max_iteration_final_proof,
        max_correction_iteration_final_proof,
        verbose,
    )

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
