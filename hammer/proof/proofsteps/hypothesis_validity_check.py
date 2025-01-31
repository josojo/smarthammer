from hammer.api.logging import LogStreamHandler
from hammer.lean.server import LeanServer
from hammer.proof.proof import Hypothesis, ProofSearchState
import logging
from dotenv import load_dotenv
from hammer.proof.proof import ProofSearchState


load_dotenv()
logger = logging.getLogger(__name__)


def check_hypotheses_validity(
    proof_state: ProofSearchState,
    lean_client: LeanServer,
    verbose=False,
):
    i = 0
    while i < len(proof_state.theoretical_hypotheses):
        logger.debug(f"Checking validity for hypothesis {i}")

        # Create the lean code for the hypothesis with tactic omega
        code = proof_state.hypothesis_as_code(i) + "\n omega"
        print(code)
        logger.debug(f"Code for hypothesis {i}: {code}")

        # Send the code to the Lean environment
        result = lean_client.run_code(code, 0, verbose)
        print(result)
        logger.debug(f"Result for hypothesis {i}: {result}")
        # Check for errors in the hypothesis section
        error_messages = [
            msg for msg in result.get("messages", []) if msg.get("severity") == "error"
        ]
        first_error = error_messages[0] if error_messages else None
        if first_error:
            line_number = first_error.get("pos", {}).get("line", None)

            hypothesis_lines = proof_state.hypothesis_as_code(i).count("\n") + 1

            if (
                line_number is not None
                and line_number <= hypothesis_lines
                and not first_error.get("data", "").startswith("unsolved goals")
            ):
                logger.error(
                    f"Error occurred for {i}-th hyptheses: {proof_state.theoretical_hypotheses[i]}! In section (line {line_number}), we got the following {first_error} cannot fix"
                )
                proof_state.remove_hypotheses(i)
                # Do not increment i, as the list has shrunk
            else:
                logger.info(
                    f"Hypothesis {i}: {proof_state.theoretical_hypotheses[i]} is valid"
                )
                i += 1
        else:
            proof_state.proven_hypotheses.append(
                Hypothesis(
                    "p" + str(len(proof_state.proven_hypotheses)),
                    proof_state.theoretical_hypotheses[i],
                    "omega",
                )
            )
            proof_state.theoretical_hypotheses.pop(i)
