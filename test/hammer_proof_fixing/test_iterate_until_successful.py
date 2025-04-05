import json
import unittest
from hammer.lean.server import LeanServer
from hammer.proof.proof import MathStatement, ProofSearchState
from hammer.api.mock.mock_client import Client
from hammer.proof.retry import retry_until_success


class TestIterateUntilValidProof(unittest.TestCase):
    def setUp(self):
        # Setup common test data
        self.lean_client = LeanServer()

    def test_iterate_until_valid_proof(self):
        # Mock objects
        name = "thm1"
        hypotheses = ["(n : ℕ)", "(oh0 : 0 < n)"]
        goal = "Nat.gcd (21*n + 4) (14*n + 3) = 1"
        previous_lean_code = "import Mathlib\n"
        # Create a proof state
        proof_state = ProofSearchState(name, hypotheses, previous_lean_code, goal)
        proof_state.theoretical_hypotheses = [
            MathStatement("lem1", [], "∀ a b g : ℕ, g ∣ a → g ∣ b → g ∣ (a - b)", None)
        ]

        proof_candidate = """
intros a b g hga hgb
by_cases h : a > b
· exact Nat.dvd_sub h hga hgb
· simp [Nat.sub_eq_zero_of_le (le_of_not_ge h)]
"""
        lean_result = json.loads(
            """{
            "messages": [{
                "severity": "error",
                "pos": {"line": 14, "column": 2},
                "endPos": {"line": 14, "column": 3},
                "data": "unsolved goals\\nn : ℕ\\noh0 : 0 < n\\na b g k1 : ℕ\\nhk1 : a = g * k1\\nk2 : ℕ\\nhk2 : b = g * k2\\n⊢ g * k1 - g * k2 = g * (k1 - k2)"
            }],
            "env": 5
        }"""
        )
        api_output_1 = """
        ```lean
intros a b g hga hgb
by_cases h : a > b
· exact Nat.dvd_sub h hga hgb
· simp [Nat.sub_eq_zero_of_le (le_of_not_ge h)]
        ```
        """
        api_output_2 = """
```lean
intros a b g hga hgb
by_cases h : a >= b
· exact Nat.dvd_sub h hga hgb
· simp [Nat.sub_eq_zero_of_le (le_of_not_ge h)]
```
        """

        # Configure mock responses
        client = Client([api_output_1, api_output_2])

        # Test successful case
        result = retry_until_success(
            client,
            self.lean_client,
            "import Mathlib",
            proof_state.hypothesis_as_code(0),
            proof_candidate,
            lean_result,
            2,
            verbose=True,
        )
        expected_result = """
intros a b g hga hgb
by_cases h : a >= b
· exact Nat.dvd_sub h hga hgb
· simp [Nat.sub_eq_zero_of_le (le_of_not_ge h)]
"""
        assert result == expected_result

        # Test unsuccessful case
        client = Client([api_output_1, api_output_2])
        with self.assertRaises(Exception) as context:
            new_theorem_code = proof_state.hypothesis_as_code(0).replace(":=", ",-")
            print(new_theorem_code)
            ans = retry_until_success(
                client,
                self.lean_client,
                "import Mathlib",
                new_theorem_code,
                proof_candidate,
                lean_result,
                2,
                verbose=True,
            )
            print(ans)
        print(context.exception)
        self.assertTrue(
            "Error occurred in hypothesis section" in str(context.exception)
        )
