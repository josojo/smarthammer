import sys
import time
from hammer.api.logging import LogStreamHandler, ContextualLoggerAdapter
from hammer.lean.server import LeanServer
from hammer.proof.proof import ProofSearchState, Hypothesis
from hammer.api.claude.client import Client as ClaudeClient
from hammer.api.deepseek.client import Client as DeepSeekClient
from hammer.api.openai.client import Client as OpenAIClient
from hammer.api.mock.mock_client import Client as MockClient
from hammer.api.base_client import AIClient
from hammer.proof.retry import retry_until_success
from rq import get_current_job
import logging
from dotenv import load_dotenv
import os
from hammer.api.types import AIForHypothesesProof
import psutil

api_output_1 = """
Natural language proof:
We want to show that \gcd(21n + 4, 14n + 3) = 1 for any natural number n with 0 < n. We use the fact that \gcd(a, b) = \gcd(a - b, b). Substituting a = 21n + 4 and b = 14n + 3, we get:

\[
\gcd(21n + 4,\, 14n + 3)
= \gcd\bigl((21n + 4) - (14n + 3),\, 14n + 3\bigr)
= \gcd(7n + 1,\, 14n + 3).
\]

Next, we apply the same gcd property again but now we subtract twice (7n + 1):

\[
\gcd(7n + 1,\, 14n + 3)
= \gcd\bigl(7n + 1,\,(14n + 3) - 2(7n + 1)\bigr)
= \gcd(7n + 1,\, 1).
\]

Since the gcd of any number and 1 is always 1, we conclude


\gcd(7n + 1,\, 1) = 1.


Hence,


\gcd(21n + 4,\, 14n + 3) = 1.

           ```lean
lemma lem1 : ∀ a b : ℕ, Nat.gcd a b = Nat.gcd (a - b) b ```,           

```lean
lemma lem2 : ∀ n : ℕ, Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (7 * n + 1) (14 * n + 3)```,           
```lean
lemma lem3 : ∀ n : ℕ, Nat.gcd (7 * n + 1) (14 * n + 3) = Nat.gcd (7 * n + 1) 1 ```, 
```lean
lemma lem4 : ∀ x : ℕ, Nat.gcd x 1 = 1 ```, 
```lean
lemma lem5 : 14 * n + 3 - 2 * (7 * n + 1) = 1 
 """

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
    try:
        # Add memory monitoring
        process = psutil.Process()
        initial_memory = process.memory_info().rss
        memory_usage_mb = initial_memory / (1024 * 1024)  # Convert bytes to MB

        task_id = kwargs.pop("task_id", None)

        # Set up logging
        if task_id:
            root_logger = logging.getLogger()
            root_logger.setLevel(logging.DEBUG)
            log_handler = LogStreamHandler(task_id)
            log_handler.setLevel(logging.DEBUG)
            formatter = logging.Formatter("%(message)s")
            log_handler.setFormatter(formatter)
            root_logger.addHandler(log_handler)

            contextual_logger.extra["step"] = "Starting Proof"
            contextual_logger.debug(f"Starting proof for task {task_id}")

        # Get current RQ job if exists
        current_job = get_current_job()
        if current_job:
            # Set a shorter job timeout to allow for retries
            current_job.timeout = 1500  # seconds
            current_job.meta["memory_usage"] = memory_usage_mb
            current_job.save_meta()

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

        ai_for_hypotheses_generation = kwargs["ai_for_hypotheses_generation"]
        ai_for_hyptheses_proof = kwargs["ai_for_hyptheses_proof"]
        ai_for_final_proof = kwargs["ai_for_final_proof"]

        # Remove hardcoded values
        lean_client = LeanServer(kwargs["code_for_env_0"])
        proof_state = ProofSearchState(name, hypotheses, codeEnv0, goal)

        # Initialize the appropriate AI clients based on the parameters
        if ai_for_hypotheses_generation == AIForHypothesesProof.CLAUDE:
            api_client_for_hypothesis_search = ClaudeClient()
        elif ai_for_hypotheses_generation == AIForHypothesesProof.DEEPSEEK_1_5:
            api_client_for_hypothesis_search = DeepSeekClient(base_url=deepseek_url)
        elif ai_for_hypotheses_generation == AIForHypothesesProof.OPENAI_O1:
            api_client_for_hypothesis_search = MockClient(
            [
                api_output_1,
            ]
        )
            # api_client_for_hypothesis_search = OpenAIClient("o1")
        elif ai_for_hypotheses_generation == AIForHypothesesProof.OPENAI_4O:
            api_client_for_hypothesis_search = OpenAIClient("gpt-4o")
        else:
            raise ValueError(f"Unknown AI client type: {ai_for_hypotheses_generation}")

        # Initialize the proof client based on parameter
        if ai_for_hyptheses_proof == AIForHypothesesProof.CLAUDE:
            api_client_for_proofing = [ClaudeClient()]
        elif ai_for_hyptheses_proof == AIForHypothesesProof.DEEPSEEK_1_5:
            api_client_for_proofing = [DeepSeekClient(base_url=deepseek_url)]
        elif ai_for_hyptheses_proof == AIForHypothesesProof.OPENAI_O1:
            api_client_for_proofing = [OpenAIClient("o1")]
        elif ai_for_hyptheses_proof == AIForHypothesesProof.OPENAI_4O:
            api_client_for_proofing = [OpenAIClient("gpt-4o")]
        else:
            raise ValueError(f"Unknown AI client type: {ai_for_hyptheses_proof}")

        # Initialize the final proof client
        if ai_for_final_proof == AIForHypothesesProof.CLAUDE:
            final_proof_client = ClaudeClient()
        elif ai_for_final_proof == AIForHypothesesProof.DEEPSEEK_1_5:
            final_proof_client = DeepSeekClient(base_url=deepseek_url)
        elif ai_for_final_proof == AIForHypothesesProof.OPENAI_O1:
            final_proof_client = OpenAIClient("o1")
        elif ai_for_final_proof == AIForHypothesesProof.OPENAI_4O:
            final_proof_client = OpenAIClient("gpt-4o")
        else:
            raise ValueError(f"Unknown AI client type: {ai_for_final_proof}")

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
            final_proof_client,  # Use the selected final proof client
            lean_client,
            max_iteration_final_proof,
            max_correction_iteration_final_proof,
            verbose,
        )

        return proof_state

    except MemoryError:
        logger.critical("Out of memory error occurred")
        raise
    except Exception as e:
        logger.critical(f"Critical error in prove_theorem: {str(e)}", exc_info=True)
        raise
    finally:
        # Clean up resources
        if "log_handler" in locals():
            root_logger.removeHandler(log_handler)


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
