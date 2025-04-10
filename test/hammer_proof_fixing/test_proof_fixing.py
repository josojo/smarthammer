import unittest
from hammer.api.mock.mock_client import Client
from hammer.lean.server import LeanServer
from hammer.proof.proof import MathStatement, ProofSearchState
from hammer.proof.proofsteps.hypothesis_proving import iterate_until_valid_proof


class TestIterateUntilValidProof(unittest.TestCase):
    def setUp(self):
        # Setup common test data
        self.lean_client = LeanServer()

    def test_iterate_until_valid_proof_successful(self):
        name = "thm1"
        hypotheses = ["(n : ℕ)", "(oh0 : 0 < n)"]
        goal = "Nat.gcd (21*n + 4) (14*n + 3) = 1"
        # Mock API outputs
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

        # Create a proof state
        previous_lean_code = "import Mathlib\n"

        proof_state = ProofSearchState(name, hypotheses, previous_lean_code, goal)
        proof_state.theoretical_hypotheses = [
            MathStatement("ab", [], "∀ a b g : ℕ, g ∣ a → g ∣ b → g ∣ (a - b)", None)
        ]
        # Create mock client
        client = Client([api_output_1, api_output_2])

        # Test the function
        proof_candidate = iterate_until_valid_proof(
            proof_state,
            0,
            client,
            self.lean_client,
            max_iteration=1,
            max_correction_iteration=2,
            verbose=True,
        )
        assert proof_candidate is not None

        # Check if a valid proof candidate was returned
        self.assertIsNotNone(proof_candidate)
        print("Proof candidate:", proof_candidate)


if __name__ == "__main__":
    unittest.main()
