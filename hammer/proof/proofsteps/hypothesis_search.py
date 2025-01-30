from hammer.api.logging import LogStreamHandler
from hammer.proof.proof import ProofSearchState
from hammer.api.base_client import AIClient
import logging
from dotenv import load_dotenv
from hammer.proof.proof import ProofSearchState


load_dotenv()
logger = logging.getLogger(__name__)


def find_hypotheses(
    proof_state: ProofSearchState,
    api_client_for_hypothesis_search: AIClient,
    verbose=False,
    log_handler: LogStreamHandler = None,
):

    logger.debug("Searching for hypotheses:")
    proof_state.add_hypotheses(api_client_for_hypothesis_search, verbose)
    logger.debug("Added hypotheses")
    logger.debug(f"Theoretical hypotheses: {proof_state.theoretical_hypotheses}")
