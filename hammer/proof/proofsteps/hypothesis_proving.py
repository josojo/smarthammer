from hammer.api.logging import LogStreamHandler
from hammer.lean.server import LeanServer
from hammer.proof.proof import MathStatement, ProofSearchState
from hammer.api.base_client import AIClient
from hammer.api.moogle.client import Client as MoogleClient
from hammer.proof.proofsteps.enriching_with_thm_names import getMoogleEnrichmentMsg
from hammer.proof.retry import retry_until_success
import logging
from dotenv import load_dotenv  # type: ignore
from hammer.proof.proof import ProofSearchState
from hammer.proof.utils import get_code_for_simulation


load_dotenv()
logger = logging.getLogger(__name__)


def iterate_until_valid_proof(
    proof_state: ProofSearchState,
    hyptotheses_number,
    client: AIClient,
    lean_client: LeanServer,
    max_iteration=1,
    max_correction_iteration=1,
    moogle_client: MoogleClient = None,
    moogle_helper_info="",
    verbose=False,
):
    cnt = 0
    starting_code = ""
    while cnt < max_iteration:
        proof_candidate = proof_state.generate_proof_candidate_for_hypotheses(
            client, hyptotheses_number, starting_code, moogle_helper_info, verbose
        )
        if proof_candidate:
            code = get_code_for_simulation(
                "", proof_state.hypothesis_as_code(hyptotheses_number), proof_candidate
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
                proof = retry_until_success(
                    client,
                    lean_client,
                    proof_state.previous_code,
                    proof_state.hypothesis_as_code(hyptotheses_number),
                    proof_candidate,
                    result,
                    max_correction_iteration,
                    moogle_client,
                    moogle_helper_info,
                    verbose,
                )
                if proof:
                    return proof
        cnt += 1
    return None


def prove_theorem_via_hypotheses_search(
    proof_state: ProofSearchState,
    api_client_for_proofing: list[AIClient],
    moogle_client: MoogleClient,
    lean_client: LeanServer,
    max_iteration_hypotheses_proof=1,
    max_correction_iteration_hypotheses_proof=1,
    verbose=False,
    log_handler: LogStreamHandler = None,
):
    if not log_handler:
        log_handler = LogStreamHandler("")
    # Try to generate proofs for different numbers of hypotheses
    valid_proofs = []
    not_valid_formulations = []
    for i in range(len(proof_state.theoretical_hypotheses)):
        log_handler.set_step(f"Proofing Hypotheses {i}")
        logger.debug(f"Searching proof for hypothesis {i}")
        for api_client in api_client_for_proofing:
            moogle_helper_info = ""
            if moogle_client:
                moogle_output = getMoogleEnrichmentMsg(
                    proof_state, api_client, moogle_client, i, False, verbose
                )
                moogle_helper_info = (
                    "\n\n Consider using the following lean4 defintions as a helper to find the proof: \n "
                    + moogle_output
                )
            try:
                proof = iterate_until_valid_proof(
                    proof_state,
                    i,
                    api_client,
                    lean_client,
                    max_iteration_hypotheses_proof,
                    max_correction_iteration_hypotheses_proof,
                    moogle_client,
                    moogle_helper_info,
                    verbose,
                )
                if proof:
                    proof_state.proven_hypotheses.append(
                        MathStatement(
                            "p" + str(len(proof_state.proven_hypotheses)),
                            proof_state.theoretical_hypotheses[i].assumptions,
                            proof_state.theoretical_hypotheses[i].statement,
                            proof,
                        )
                    )
                    valid_proofs.append(i)
                    break
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
