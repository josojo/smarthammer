import unittest

# from hammer.hammer import prove_theorem_via_hypotheses_search
from hammer.api.mock.mock_client import Client
from hammer.main import find_final_proof, prove_theorem_via_hypotheses_search
from hammer.lean.server import LeanServer

from hammer.proof.proof import ProofSearchState


class TestHammer(unittest.TestCase):
    def setUp(self):
        # Setup common test data
        self.lean_client = LeanServer(initiate_mathlib=True)

        # Create a ProofSearchState instance

    def test_prove_theorem_via_hypotheses_search_successful(self):

        name = "thm1"
        hypotheses = ["(n : ℕ)", "(oh0 : 0 < n)"]
        goal = "Nat.gcd (21*n + 4) (14*n + 3) = 1"
        # Setup mock behaviors
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
        ∀ a b g: ℕ , g ∣ a → g ∣ b → g ∣ (a - b) 
        ```

        ```lean
        -- first linear combination equals 7n + 1
        (21*n + 4) - (14*n + 3) = 7*n + 1
        ```

        ```lean
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
intros a b g hga hgb
by_cases h : a >= b
· exact Nat.dvd_sub h hga hgb
· simp [Nat.sub_eq_zero_of_le (le_of_not_ge h)]
```
        """
        api_output_3 = """
        ```lean
        omega
        ```
        """
        api_output_4 = """
```lean
intro g h1 h2
have h3 : g ∣ (21 * n + 4) - (14 * n + 3) := by
    apply p0
    exact h1
    exact h2
rw [p1] at h3
have h4 : g ∣ 3 * (14 * n + 3) - 2 * (21 * n + 4) := by
    apply p0
    exact dvd_mul_of_dvd_right h2 3
    exact dvd_mul_of_dvd_right h1 2
rw [p2] at h4
have h5 : g ∣ 1 := h4
exact h5
```
        """
        api_output_5 = """
```lean
intro g h
have h1 : g ∣ 1 := h
-- g divides 1, so g must equal 1 (property of divisors of 1)
have h2 : g = 1 := Nat.eq_one_of_dvd_one h1
exact h2
```
"""
        final_proof_api_output = """
```lean
-- Assume gcd is g
let g := Nat.gcd (21 * n + 4) (14 * n + 3)
have h1 : g ∣ (21 * n + 4) := Nat.gcd_dvd_left _ _
have h2 : g ∣ (14 * n + 3) := Nat.gcd_dvd_right _ _
have h3 : g ∣ (21 * n + 4) - (14 * n + 3) := p0 (21 * n + 4) (14 * n + 3) g h1 h2
rw [p1] at h3
have h4 : g ∣ 1 := p3 g h1 h2
have h5 : g = 1 := p4 g h4
exact h5
```
"""

        # create a proof state
        proof_state = ProofSearchState(name, hypotheses, goal)

        # Create mock clients
        client = Client(
            [
                api_output_1,
                api_output_2,
                api_output_3,
                api_output_3,
                api_output_4,
                api_output_5,
                final_proof_api_output,
            ]
        )

        prove_theorem_via_hypotheses_search(
            proof_state, client, self.lean_client, verbose=True
        )
        assert len(proof_state.proven_hypotheses) == 5
        for x in proof_state.proven_hypotheses:
            print(x)
            print("\n")
            print(x.proof)
        final_proof_with_hypotheses = find_final_proof(
            proof_state, client, self.lean_client, 1, verbose=True
        )
        result = self.lean_client.run_code(final_proof_with_hypotheses, 0, True)
        if not (
            isinstance(result, dict)
            and (
                "messages" not in result
                or not any(
                    msg.get("severity") == "error" for msg in result.get("messages", [])
                )
            )
        ):
            assert 2 == 1


if __name__ == "__main__":
    unittest.main()
