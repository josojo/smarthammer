from hammer.lean.server import LeanServer
from hammer.proof.proof import ProofSearchState

from hammer.api.base_client import AIClient
from hammer.proof.retry import retry_until_success
from hammer.proof.utils import get_code_for_simulation
import logging
from dotenv import load_dotenv  # type: ignore
from hammer.proof.proof import ProofSearchState
from hammer.api.moogle.client import Client as MoogleClient

load_dotenv()
logger = logging.getLogger(__name__)


def iterate_until_valid_final_proof(
    proof_state: ProofSearchState,
    client: AIClient,
    moogle_client: MoogleClient,
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
            code = get_code_for_simulation(
                "",
                proof_state.get_theorem_code(),
                proof_candidate,
            )
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
                        moogle_client,
                        moogle_helper_info="",
                        verbose=verbose,
                    )
                    if proof:
                        return proof
                except Exception as e:
                    logger.error(f"Error while proving final proof: {e}")
                    if "cannot fix" in str(e):
                        logger.warning(
                            "Encountered unfixable error, stopping proof attempts"
                        )
                        return None
        cnt += 1
    return None


def find_final_proof(
    proof_state: ProofSearchState,
    api_client: AIClient,
    moogle_client: MoogleClient,
    lean_client,
    max_iteration_final_proof=1,
    max_iternation_correction_proof=1,
    verbose=False,
):
    proof = iterate_until_valid_final_proof(
        proof_state,
        api_client,
        moogle_client,
        lean_client,
        max_iteration_final_proof,
        max_iternation_correction_proof,
        verbose,
    )
    if proof:
        proof_state.proof = proof_state.build_final_proof(proof)
    return proof_state.proof
