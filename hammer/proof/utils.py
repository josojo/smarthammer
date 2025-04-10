def unicode_escape(input_str):
    """
    Converts all non-ASCII characters in the input string to their Unicode escape sequences.
    """
    out_str = input_str.encode("raw_unicode_escape").decode("unicode_escape")

    return out_str


def extract_lean_blocks(text: str) -> list[str]:
    """Extract code from lean code blocks marked with ```lean ... ``` or ```lean4 ... ```."""
    blocks = []

    # Determine which marker to use based on the presence of `lean4`
    if "```lean4" in text:
        parts = text.split("```lean4")
    else:
        parts = text.split("```lean")

    if len(parts) == 1 and "```" in parts[0]:
        code = parts[0].split("```")[0]
        blocks.append("\n" + code)
    for part in parts[1:]:  # Skip first part before any ```lean or ```lean4
        if "```" in part:
            code = part.split("```")[0]
            blocks.append(code)
    return blocks


def extract_proof_from_lean_code(goal_end_code: str, lean_code: str) -> str:
    """
    Extracts just the proof part from lean code that may include the theorem definition.
    If the code starts with 'theorem', removes the theorem definition and returns only the proof.
    Otherwise returns the original code.
    """
    # Split everything by the last theorem definition, as this will contain our proof:
    if "theorem" in lean_code:
        lean_code = "theorem " + lean_code.split("theorem")[-1]
    # Split on := by to get everything after the theorem definition
    if lean_code.strip().startswith("theorem"):
        # parts = lean_code.split(
        #     f"{goal_end_code[-4:]} := by", 1
        # )  # Split only on first occurrence
        parts = lean_code.split(":= by", 1)  # Split only on first occurrence
        if len(parts) > 1:
            return "\n" + parts[1]
    return lean_code


def extract_proof_from_text(goal_end_code: str, text: str) -> list[str]:
    """
    Extracts lean code blocks from text and returns just the proof parts.
    Combines extract_lean_blocks() and extract_proof_from_lean_code().

    Args:
        text: String containing lean code blocks marked with ```lean ... ```

    Returns:
        List of proof strings extracted from the lean code blocks
    """
    lean_blocks = extract_lean_blocks(text)
    # Remove Lean comments (lines starting with --) from each block
    cleaned_blocks = []
    for block in lean_blocks:
        # Split by lines, filter out comments, and rejoin
        lines = block.split("\n")
        non_comment_lines = [
            line for line in lines if not line.strip().startswith("--")
        ]
        cleaned_blocks.append("\n".join(non_comment_lines))

    proofs = [
        extract_proof_from_lean_code(goal_end_code, block) for block in cleaned_blocks
    ]
    return proofs


def get_code_for_simulation(
    previous_ans_code: str, theorem_code: str, ans_code: str
) -> str:
    return theorem_code + "\n" + previous_ans_code + ans_code
