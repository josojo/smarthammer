import pytest
from hammer.proof.proof import MathStatement, ProofSearchState


class MockClaudeClient:
    def send(self, prompt, verbose=False):
        return """
Natural language proof: Let's call d = gcd(21n + 4, 14n + 3). Then d divides both numbers, and therefore it also divides any linear combination of them. Let's consider (21n + 4) - 3/2(14n + 3) = -n + -0.5. Since d divides both numbers, it must divide 2(-n + -0.5) = -2n - 1. Similarly, 3(21n + 4) - 2(14n + 3) = 35n + 6. Therefore d must divide both -2n - 1 and 35n + 6. This means d also divides any linear combination of these numbers. In particular, it divides 35n + 6 - (-17.5)(-2n - 1) = 1. Since d is positive (as it's a GCD) and divides 1, we must have d = 1.

Lean4 hypotheses:

```lean
lemma lem1 : ∀ (a b c : ℤ), a ∣ b → a ∣ c → a ∣ (b - c)
```

```lean
lemma lem2 (n : ℕ) : Nat.gcd (21*n + 4) (14*n + 3) ∣ (-2*n - 1)
```

```lean
lemma lem3 (n : ℕ) : Nat.gcd (21*n + 4) (14*n + 3) ∣ (35*n + 6)
```

```lean
lemma lem4 : ∀ (d : ℕ), d > 0 → d ∣ 1 → d = 1
```
"""

    def name() -> str:
        return "MockClaudeClient"


def test_hypothesis_extraction():
    # Create a minimal ProofSearchState
    state = ProofSearchState(
        name="test_theorem",
        hypotheses=["(n : ℕ)"],
        goal="Nat.gcd (21*n + 4) (14*n + 3) = 1",
        previous_code="",
    )

    # Add hypotheses using mock client
    state.add_hypotheses(MockClaudeClient(), verbose=False)

    # Expected hypotheses after extraction
    expected_hypotheses = [
        MathStatement("lem1", [], "∀ (a b c : ℤ), a ∣ b → a ∣ c → a ∣ (b - c)", None),
        MathStatement("lem2", [], "Nat.gcd (21*n + 4) (14*n + 3) ∣ (-2*n - 1)", None),
        MathStatement("lem3", [], "Nat.gcd (21*n + 4) (14*n + 3) ∣ (35*n + 6)", None),
        MathStatement("lem4", [], "∀ (d : ℕ), d > 0 → d ∣ 1 → d = 1", None),
    ]

    # Verify that we got the expected number of hypotheses
    assert len(state.theoretical_hypotheses) == len(
        expected_hypotheses
    ), f"Expected {len(expected_hypotheses)} hypotheses, got {len(state.theoretical_hypotheses)}"

    # Verify each hypothesis matches exactly
    for actual, expected in zip(state.theoretical_hypotheses, expected_hypotheses):
        assert (
            actual.statement.strip() == expected.statement.strip()
        ), f"Hypothesis mismatch:\nExpected: {expected}\nGot: {actual}"
        assert (
            actual.name.strip() == expected.name.strip()
        ), f"Hypothesis name mismatch:\nExpected: {expected}\nGot: {actual}"
