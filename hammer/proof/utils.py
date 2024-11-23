def unicode_escape(input_str):
    """
    Converts all non-ASCII characters in the input string to their Unicode escape sequences.
    """
    out_str = input_str.encode("raw_unicode_escape").decode("unicode_escape")

    return out_str


def extract_lean_blocks(text: str) -> list[str]:
    """Extract code from lean code blocks marked with ```lean ... ```."""
    blocks = []
    parts = text.split("```lean")
    for part in parts[1:]:  # Skip first part before any ```lean
        if "```" in part:
            code = part.split("```")[0].strip()
            blocks.append(code)
    return blocks
