from hammer.proof.utils import extract_proof_from_text


def retry_until_success(api_client, lean_client, theorem_code, ans_code, result, max_correction_iteration=1, verbose=False):
    for _ in range(0, max_correction_iteration):
                    error_messages = [msg for msg in result.get("messages", []) if msg.get("severity") == "error"]
                    first_error = error_messages[0] if error_messages else None
                    prompt = f"The following proof \n```lean4 \n {theorem_code}{ans_code}\n ```\n failed with error: \n {first_error}. \n Please propose a complete lean proof that corrects this error and proves the theorem. Put your proof into a new ```lean ``` block."
                    response = api_client.send(prompt, verbose)
                    ans_code = extract_proof_from_text(response)[0]
                    code = theorem_code + ans_code
                    result = lean_client.run_code(code, 0, verbose)
                    if isinstance(result, dict) and (
                        "messages" not in result
                        or not any(
                            msg.get("severity") == "error" for msg in result.get("messages", [])
                        )
                    ):
                        return ans_code
                    error_messages = [msg for msg in result.get("messages", []) if msg.get("severity") == "error"]
                    first_error = error_messages[0] if error_messages else None
                    line_number = first_error.get("pos", {}).get("line", None)
                    # Count lines in hypothesis code
                    hypothesis_lines = theorem_code.count('\n') + 1
                    
                    # Check if error line is in hypothesis section
                    if line_number is not None and line_number < hypothesis_lines:
                        raise Exception(f"Error occurred in hypothesis section (line {line_number}), cannot fix")
                    print(f"Proof candidate: {code} failed with the error {first_error}")
    return None