import unittest
from hammer.proof.proofsteps.hypothesis_validity_check import check_hypotheses_validity
from hammer.proof.proof import MathStatement, ProofSearchState
from hammer.lean.server import LeanServer
from hammer.api.logging import LogStreamHandler


class TestCheckAssumptionsValidity(unittest.TestCase):
    def setUp(self):
        # Initialize the ProofSearchState with required arguments
        self.proof_state = ProofSearchState(
            name="TestProof",
            hypotheses=["(n : ℕ)"],
            previous_code="import Mathlib\n",
            goal="Nat.gcd (21*n + 4) (14*n + 3) = 1",
        )
        self.proof_state.theoretical_hypotheses = [
            MathStatement(
                "lem1",
                [],
                "d∣(21*n + 4) → d∣(14*n + 3) → d∣((21*n + 4) - (3*(14*n + 3))÷2)",
                None,
            ),
            MathStatement(
                "lem2", [], "∀ n : N, 23*n + 4 = 2*(7*n + 1) + (7*n + 2)", None
            ),
            MathStatement("lem3", [], "Nat.gcd (7*n + 1) (1) = 1", None),
            MathStatement(
                "lem1", [], "∀ n : N, 21*n + 4 = 2*(7*n + 1) + (7*n + 2)", None
            ),
        ]
        # Initialize the LeanServer
        self.lean_client = LeanServer()

    def test_hypothesis_with_error(self):
        # Run the function
        check_hypotheses_validity(self.proof_state, self.lean_client)

        # Check that the first hypothesis was removed
        self.assertNotIn(
            "d∣(21*n + 4) → d∣(14*n + 3) → d∣((21*n + 4) - (3*(14*n + 3))÷2)",
            self.proof_state.theoretical_hypotheses,
        )
        self.assertNotIn(
            "∀ n : N, 21*n + 4 = 2*(7*n + 1) + (7*n + 2)",
            self.proof_state.theoretical_hypotheses,
        )

    def test_valid_assumptions(self):
        # Run the function
        print(self.proof_state.theoretical_hypotheses)
        check_hypotheses_validity(self.proof_state, self.lean_client, True)
        print(self.proof_state.theoretical_hypotheses)
        # Check that the second hypothesis is still present
        self.assertIn(
            "Nat.gcd (7*n + 1) (1) = 1",
            self.proof_state.theoretical_hypotheses[0].statement,
        )


if __name__ == "__main__":
    unittest.main()
