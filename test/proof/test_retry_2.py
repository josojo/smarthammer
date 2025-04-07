import pytest
from hammer.lean.server import LeanServer
from hammer.proof.retry import get_code_for_simulation, retry_until_success
from unittest.mock import MagicMock


class MockAPIClient:
    def __init__(self, name="TestClient"):
        self.name = name
        self.send = MagicMock(return_value="by\n  exact rfl")


class MockMoogleClient:
    def __init__(self):
        # self.send = MagicMock(return_value="Some theorems that might help...")
        self.last_query = None

    def send(self, query, verbose=False):
        self.last_query = query
        return "Some theorems that might help..."


def test_retry_until_success_with_error_line():
    # Initialize clients
    lean_client = LeanServer()
    api_client = MockAPIClient()
    moogle_client = MockMoogleClient()

    # Setup a theorem that will fail with a specific error line
    previous_code = "import Mathlib"
    theorem_code = """theorem test_theorem (n : Nat) : n = n := by"""
    initial_proof = """
  have h : n ≠ n := by cauchySchwarz  -- # This line will cause an error
  exact rfl
"""

    # First attempt will fail, second attempt will succeed
    api_client.send.side_effect = [
        # initial_proof,  # First attempt - will fail
        "```lean exact rfl```"  # Second attempt - will succeed
    ]

    # Run the retry function
    result = retry_until_success(
        api_client=api_client,
        lean_client=lean_client,
        previous_code=previous_code,
        theorem_code=theorem_code,
        ans_code=initial_proof,
        result=lean_client.run_code(theorem_code + initial_proof),
        max_correction_iteration=2,
        moogle_client=moogle_client,
        verbose=True,
    )

    # Verify that the error line was sent to Moogle
    assert (
        moogle_client.last_query
        == "  have h : n ≠ n := by cauchySchwarz  -- # This line will cause an error"
    ), "Moogle client should receive the error line"

    # Verify that we got a successful result
    assert result == " exact rfl", "Should get a successful proof"

    # Verify API client was called once
    assert api_client.send.call_count == 1, "API client should be called once"


def test_retry_until_success_with_hypothesis_error():
    # Initialize clients
    lean_client = LeanServer()
    api_client = MockAPIClient()
    moogle_client = MockMoogleClient()

    # Setup a theorem where error occurs in hypothesis
    previous_code = "import Mathlib"
    theorem_code = (
        """theorem test_bad_hypothesis (n : Nat) (h : n ≠ n) : n =≠ n := by"""
    )
    initial_proof = "exact rfl"

    # Run the retry function and expect it to raise an exception
    with pytest.raises(Exception, match="Error occurred in hypothesis section"):
        retry_until_success(
            api_client=api_client,
            lean_client=lean_client,
            previous_code=previous_code,
            theorem_code=theorem_code,
            ans_code=initial_proof,
            result=lean_client.run_code(
                get_code_for_simulation(
                    "",
                    theorem_code,
                    initial_proof,
                )
            ),
            max_correction_iteration=2,
            moogle_client=moogle_client,
            verbose=True,
        )
