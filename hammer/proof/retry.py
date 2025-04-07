import logging
from hammer.proof.proofsteps.enriching_with_thm_names import enrich_error_with_moogle
from hammer.proof.utils import extract_proof_from_text, get_code_for_simulation
from hammer.api.moogle.client import Client as MoogleClient
from hammer.api.base_client import AIClient
from hammer.lean.server import LeanServer

logger = logging.getLogger(__name__)


def prompt_with_error_message(
    previous_code, theorem_code, ans_code, error_messages, moogle_helper_info=""
) -> str:
    prompt = (
        f"The following proof \n```lean4 \n{previous_code}\n {theorem_code}{ans_code}\n ```\n failed with error: \n {error_messages}. \n Please propose a complete lean proof that corrects this error and proves the theorem. Put your proof into a new ```lean ``` block."
        + moogle_helper_info
    )
    return prompt


def prompt_with_previous_code_and_cutoff(
    previous_code, theorem_code, ans_code, error_messages
) -> tuple[str, str]:
    # Filter error messages to only include those with severity "error"
    severe_errors = [msg for msg in error_messages if msg.get("severity") == "error"]
    if severe_errors[0]["data"].startswith("unsolved goals"):
        return [
            prompt_with_error_message(
                previous_code, theorem_code, ans_code, error_messages
            ),
            "",
        ]
    # Parse the line number from the first severe error
    first_severe_error = (
        severe_errors[0].get("pos", {}).get("line", None) if severe_errors else None
    )

    line_to_cut = first_severe_error - theorem_code.count("\n") - 1
    if line_to_cut > 0:
        ans_code = "\n".join(ans_code.split("\n")[:line_to_cut])
    prompt = f"Finish the following proof \n```lean4 \n{previous_code}\n {theorem_code}{ans_code}\n "
    return [prompt, ans_code]


def retry_until_success(
    api_client: AIClient,
    lean_client: LeanServer,
    previous_code,
    theorem_code,
    ans_code,
    result,
    max_correction_iteration=1,
    library_search_client: MoogleClient = None,
    moogle_helper_info="",
    verbose=False,
):
    if not hasattr(api_client, "send"):
        raise ValueError(
            f"Invalid API client provided: {type(api_client)}. Expected an object with 'send' method."
        )
    # Count lines in hypothesis code
    hypothesis_lines = theorem_code.count("\n") + 1
    for i in range(0, max_correction_iteration):
        error_messages = [
            msg for msg in result.get("messages", []) if msg.get("severity") == "error"
        ]
        first_error = error_messages[0] if error_messages else None
        line_number = first_error.get("pos", {}).get("line", None)

        # Check if error line is in hypothesis section
        if (
            line_number is not None
            and line_number <= hypothesis_lines
            and not first_error.get("data", "").startswith("unsolved goals")
        ):
            raise Exception(
                f"Error occurred in hypothesis section (line {line_number}), cannot fix"
            )
        previous_ans_code = ""
        if api_client.name == "DeepSeekProver1.5":
            prompt, previous_ans_code = prompt_with_previous_code_and_cutoff(
                previous_code, theorem_code, ans_code, error_messages
            )
        else:
            moogle_info = moogle_helper_info
            if library_search_client is not None:
                moogle_helper_for_error = enrich_error_with_moogle(
                    error_messages,
                    library_search_client,
                    previous_code,
                    theorem_code,
                    ans_code,
                    verbose,
                )
                if moogle_helper_for_error:
                    moogle_info = moogle_helper_for_error
            prompt = prompt_with_error_message(
                previous_code, theorem_code, ans_code, error_messages, moogle_info
            )
        response = api_client.send(prompt, verbose)
        ans_code = extract_proof_from_text(theorem_code, response)[0]
        code = get_code_for_simulation("", theorem_code, ans_code)
        result = lean_client.run_code(code, 0, verbose)
        if isinstance(result, dict) and (
            "messages" not in result
            or not any(
                msg.get("severity") == "error" for msg in result.get("messages", [])
            )
        ):
            if verbose:
                logger.debug(f"Proof successfully corrected after {i} iterations")
            return ans_code
        else:
            if verbose:
                logger.debug(
                    f"The proof contains the following error/simulation output:\n {result}"
                )

    return None
