import unittest
import pytest
from hammer.api.claude.client import Client
from hammer.main import iterate_until_valid_final_proof
from hammer.lean.server import LeanServer
from hammer.proof.proof import Hypothesis, ProofSearchState


class TestIterateUntilValidProofWithRealClient(unittest.TestCase):
    def setUp(self):
        # Setup common test data
        self.lean_client = LeanServer(initiate_mathlib=True)

    @pytest.mark.manual
    def test_iterate_until_valid_proof_successful(self):
        name = "thm1"
        hypotheses = ["(n : ℕ)", "(oh0 : 0 < n)"]
        goal = "Nat.gcd (21*n + 4) (14*n + 3) = 1"

        # Create a proof state
        proof_state = ProofSearchState(name, hypotheses, goal)
        proof_state.proven_hypotheses = [
            Hypothesis("h0", "∀ a b g : ℕ, g ∣ a → g ∣ b → g ∣ (a - b)", None),
            Hypothesis("h1", "(21*n + 4) - (14*n + 3) = 7*n + 1", None),
            Hypothesis("h2", "3*(14*n + 3) - 2*(21*n + 4) = 1", None),
            Hypothesis("h3", "∀ g : ℕ, g ∣ (21*n + 4) → g ∣ (14*n + 3) → g ∣ 1", None),
            Hypothesis("h4", "∀ g : ℕ, g ∣ 1 → g = 1", None),
        ]
        # Create mock client
        client = Client()

        # Test the function
        proof_candidate = iterate_until_valid_final_proof(
            proof_state,
            client,
            self.lean_client,
            max_iteration=1,
            max_correction_iteration=1,
            verbose=True,
        )
        assert proof_candidate is not None

        # Check if a valid proof candidate was returned
        self.assertIsNotNone(proof_candidate)


if __name__ == "__main__":
    unittest.main()
