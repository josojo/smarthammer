import unittest
from hammer.main import prove_theorem_via_hypotheses_search
from hammer.api.mock.mock_client import Client
from hammer.lean.server import LeanServer

from hammer.proof.proof import ProofSearchState


class TestHammer(unittest.TestCase):
    def setUp(self):
        # Setup common test data
        self.name = "p1"
        self.hypotheses = ["(n : ℕ)", "(oh0 : 0 < n)"]
        self.goal = "Nat.gcd (21*n + 4) (14*n + 3) = 1"

        api_output_1 = """
        Let me help formulate a proof for this GCD theorem.

        Natural language proof:
        Let's call g = gcd(21n + 4, 14n + 3). If we show that g divides both numbers and their linear combination, we can find g.
        If g divides both 21n + 4 and 14n + 3, then it also divides any linear combination of them.
        Consider: (21n + 4) - (14n + 3) = 7n + 1
        And: 3(14n + 3) - 2(21n + 4) = 42n + 9 - 42n - 8 = 1

        Therefore g divides 1, which means g = 1.

        Let's break this down into critical Lean4 hypotheses:

        ```lean
        -- if g divides both numbers, it divides their difference
        ∀ a b g : ℕ, g ∣ a → g ∣ b → g ∣ (a - b)
        ```

        ```lean
        -- first linear combination equals 7n + 1
        (21*n + 4) - (14*n + 3) = 7*n + 1
        ```

        ```lean
        -- second linear combination equals 1
        3*(14*n + 3) - 2*(21*n + 4) = 1
        ```

        ```lean
        -- if g divides both original numbers, it divides 1
        ∀ g : ℕ, g ∣ (21*n + 4) → g ∣ (14*n + 3) → g ∣ 1
        ```

        ```lean
        -- only 1 divides 1 in natural numbers
        ∀ g : ℕ, g ∣ 1 → g = 1
        ```

        These hypotheses capture the key steps needed to prove that the GCD must be 1."""

        api_output_2 = """
        ```lean
        omega
        ```
        """
        # Create mock clients
        self.mock_api_client = Client([api_output_1, api_output_2])
        self.mock_lean_client = LeanServer("")

        # Create a ProofSearchState instance
        self.proof_state = ProofSearchState(self.name, self.hypotheses, self.goal)


if __name__ == "__main__":
    unittest.main()
