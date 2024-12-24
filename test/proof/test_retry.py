import pytest
from unittest.mock import Mock
from hammer.proof.retry import retry_until_success


def test_retry_exception_on_hypothesis_error():
    # Mock API client
    api_client = Mock()
    api_client.send.return_value = "```lean\nsome proof```"

    # Mock Lean client
    lean_client = Mock()
    lean_client.run_code.return_value = {
        "messages": [
            {
                "severity": "error",
                "pos": {"line": 2, "column": 13},
                "endPos": {"line": 2, "column": 15},
                "data": "failed to synthesize\n  Neg ℕ\nAdditional diagnostic information may be available using the `set_option diagnostics true` command.",
            },
            {
                "severity": "error",
                "pos": {"line": 6, "column": 22},
                "endPos": {"line": 6, "column": 24},
                "data": "failed to synthesize\n  Neg ℕ\nAdditional diagnostic information may be available using the `set_option diagnostics true` command.",
            },
            {
                "severity": "info",
                "pos": {"line": 6, "column": 44},
                "endPos": {"line": 6, "column": 48},
                "data": "Try this: ring_nf",
            },
            {
                "severity": "error",
                "pos": {"line": 6, "column": 41},
                "endPos": {"line": 6, "column": 48},
                "data": "unsolved goals\nn : ℕ\noh0 : 0 < n\n⊢ sorry",
            },
        ]
    }

    # Test inputs
    previous_code = "previous code\n"
    theorem_code = "theorem testy (n : \u2115) (oh0 : 0 < n) : \n (21*n + 4)*(-2) + (14*n + 3)*3 = 1 :="  # 3 lines, error occurs on line 2
    ans_code = "some proof"
    result = lean_client.run_code.return_value

    # Test that exception is raised
    with pytest.raises(Exception) as exc_info:
        retry_until_success(
            api_client, lean_client, previous_code, theorem_code, ans_code, result
        )

    assert (
        str(exc_info.value)
        == "Error occurred in hypothesis section (line 2), cannot fix"
    )
