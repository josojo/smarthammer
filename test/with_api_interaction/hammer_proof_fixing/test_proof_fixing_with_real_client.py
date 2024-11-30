import pytest
import unittest
from hammer.api.claude.client import Client
from hammer.main import iterate_until_valid_proof
from hammer.lean.server import LeanServer
from hammer.proof.proof import ProofSearchState


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
        proof_state.theoretical_hypotheses = [
            "∀ a b g : ℕ, g ∣ a → g ∣ b → g ∣ (a - b)",
        ]
        # Create mock client
        client = Client()

        # Test the function
        proof_candidate = iterate_until_valid_proof(
            proof_state,
            0,
            client,
            self.lean_client,
            max_iteration=1,
            max_correction_iteration=4,
            verbose=True,
        )
        assert proof_candidate is not None

        # Check if a valid proof candidate was returned
        self.assertIsNotNone(proof_candidate)


if __name__ == "__main__":
    unittest.main()