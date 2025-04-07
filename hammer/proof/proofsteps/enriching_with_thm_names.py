from hammer.proof.proof import ProofSearchState
from hammer.api.base_client import AIClient
import logging
from dotenv import load_dotenv  # type: ignore
from hammer.proof.proof import ProofSearchState
from hammer.api.moogle.client import Client as MoogleClient

load_dotenv()
logger = logging.getLogger(__name__)


def extract_search_blocks(text: str) -> list[str]:
    """Extract search terms from blocks marked with ```search ... ```."""
    blocks = []
    parts = text.split("```search")

    # Handle case where there's only one block without search prefix
    if len(parts) == 1 and "```" in parts[0]:
        code = parts[0].split("```")[0].strip()
        blocks.append(code)

    # Handle normal cases with ```search prefix
    for part in parts[1:]:
        if "```" in part:
            code = part.split("```")[0].strip()
            blocks.append(code)

    return blocks


def getMoogleEnrichmentMsg(
    proof_state: ProofSearchState,
    ai_client: AIClient,
    moogle_client: MoogleClient,
    hypotheses_number,
    use_keyword_finder=False,
    verbose=False,
):
    """Get the message to send to Moogle for enrichment."""
    # Get the hypotheses as code
    if use_keyword_finder:
        hypotheses_code = proof_state.hypothesis_as_code(hypotheses_number)
        msg = f"""
        we want to query an RAG system for lean4 to proof the following lemma
        ```lean
        {hypotheses_code}
        ```
        Please find short search keywords such that the RAG will likely find helpful theroems that help proving the theorem. Put the search keywords as a string into ```search ``` box
        """
        response = ai_client.send(msg, verbose)
    else:
        response = proof_state.hypothesis_as_goal(hypotheses_number)
        response = "```search" + response + "```"

    # parse the ```search ``` box from the response
    search_keywords = extract_search_blocks(response)
    if search_keywords == []:
        raise Exception("No search keywords found in the response")
    else:
        search_keywords = search_keywords[0]
    # Send the search keywords to Moogle
    moogle_response = moogle_client.send(search_keywords, verbose)
    return moogle_response


def get_simulation_error_line(error_messages, previous_code, theorem_code, ans_code):
    ### parse the error message for the first line number of the error
    first_error = error_messages[0] if error_messages else None
    if first_error is None:
        return None
    ## if the error starts with unsolved goals, return the error message
    if first_error["data"].startswith("unsolved goals"):
        return None
    if first_error["data"].startswith("omega"):
        return None
    if first_error["data"].startswith("linarith"):
        return None
    line_number = first_error.get("pos", {}).get("line", None)
    ## get the line of the error
    error_line = (theorem_code + ans_code).split("\n")[line_number - 1]
    return error_line


def enrich_error_with_moogle(
    error_messages, moogle_client, previous_code, theorem_code, ans_code, verbose
):
    error_line = get_simulation_error_line(
        error_messages, previous_code, theorem_code, ans_code
    )
    if error_line is None:
        return None
    ## send the error line to moogle
    moogle_response = moogle_client.send(error_line, verbose)
    output = (
        "\n Maybe the following defintions and theorems can help you: \n"
        + moogle_response
    )
    return output
