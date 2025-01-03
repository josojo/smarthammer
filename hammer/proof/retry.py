from hammer.proof.utils import extract_proof_from_text


def retry_until_success(
    api_client,
    lean_client,
    previous_code,
    theorem_code,
    ans_code,
    result,
    max_correction_iteration=1,
    verbose=False,
):
    # Count lines in hypothesis code
    hypothesis_lines = theorem_code.count("\n") + 1
    for _ in range(0, max_correction_iteration):
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
        prompt = f"The following proof \n```lean4 \n{previous_code}\n {theorem_code}{ans_code}\n ```\n failed with error: \n {error_messages}. \n Please propose a complete lean proof that corrects this error and proves the theorem. Put your proof into a new ```lean ``` block."
        response = api_client.send(prompt, verbose)
        ans_code = extract_proof_from_text(response)[0]
        code = theorem_code + "\n" + ans_code
        result = lean_client.run_code(code, 0, verbose)
        if isinstance(result, dict) and (
            "messages" not in result
            or not any(
                msg.get("severity") == "error" for msg in result.get("messages", [])
            )
        ):
            return ans_code

    return None
