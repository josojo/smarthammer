import sys
from hammer.api.logging import LogStreamHandler, ContextualLoggerAdapter
from hammer.proof.proof import ProofSearchState

from hammer.proof.proofsteps.final_proof_assembly import find_final_proof
from hammer.proof.proofsteps.hypothesis_proving import (
    prove_theorem_via_hypotheses_search,
)
from hammer.proof.proofsteps.hypothesis_search import find_hypotheses
from hammer.proof.proofsteps.hypothesis_validity_check import check_hypotheses_validity
from rq import get_current_job  # type: ignore
import logging
from dotenv import load_dotenv  # type: ignore
from hammer.proof.proof import ProofSearchState
import psutil
from hammer.api.config import get_solver_configs, validate_inputs


load_dotenv()
logger = logging.getLogger(__name__)
contextual_logger = ContextualLoggerAdapter(logger, {"step": "Starting Proof"})


def prove_theorem(**kwargs):
    try:
        validate_inputs(kwargs, logger)  # Validate inputs at the start

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

        config = get_solver_configs(kwargs)

        proof_state = ProofSearchState(
            config["name"], config["hypotheses"], config["code_env_0"], config["goal"]
        )

        for i in range(config["number_of_proving_cycles"]):

            log_handler.set_step(f"Adding Hypotheses round {i}")
            find_hypotheses(
                proof_state,
                config["api_client_for_hypothesis_search"],
                verbose=config["verbose"],
                log_handler=log_handler,
            )

            log_handler.set_step(f"Checking Hypotheses Validity round {i}")
            check_hypotheses_validity(
                proof_state,
                config["lean_client"],
                verbose=config["verbose"],
            )

            prove_theorem_via_hypotheses_search(
                proof_state,
                config["hypothesis_proof_client"],
                config["library_search_client"],
                config["lean_client"],
                config["max_iteration_hypotheses_proof"],
                config["max_correction_iteration_hypotheses_proof"],
                verbose=config["verbose"],
                log_handler=log_handler,
            )

            log_handler.set_step(f"Building Final Proof round {i}")
            find_final_proof(
                proof_state,
                config["final_proof_client"],  # Use the selected final proof client'],
                config["library_search_client"],
                config["lean_client"],
                config["max_iteration_final_proof"],
                config["max_correction_iteration_final_proof"],
                config["verbose"],
            )
            if proof_state.proof:
                logger.debug(f"Proof found for theorem {proof_state.name}")
                break

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
