import pytest
from hammer.proof.proof import MathStatement, ProofSearchState


class MockClaudeClient:
    def send(self, prompt, verbose=False):
        return """
 Natural language proof: ...
Lean4 hypotheses:
```lean
lemma lem1 (x y : ℕ → ℝ) (hx : Summable (λ i ↦ x i ^ 2)) (hy : Summable (λ i ↦ y i ^ 2)) : 
  ∑' i, ∑' j, x i ^ 2 * y j ^ 2 = (∑' i, x i ^ 2) * (∑' j, y j ^ 2)
```
```lean
lemma lem2 (x y : ℕ → ℝ) (hx : Summable (λ i ↦ x i ^ 2)) (hy : Summable (λ i ↦ y i ^ 2)) : 
  (∑' i, x i * y i) ^ 2 ≤ (∑' i, x i ^ 2) * (∑' i, y i ^ 2)
```
```lean
lemma lem3 (y : ℕ → ℝ) (hy : Summable (λ i ↦ y i ^ 2)) : 
  ∑' j, y j ^ 2 = ∑' i, y i ^ 2
```

"""

    def name() -> str:
        return "MockClaudeClient"


def test_hypothesis_hypo():
    # Create a minimal ProofSearchState
    state = ProofSearchState(
        name="test_theorem",
        hypotheses=[
            "(x y : ℕ → ℝ)",
            "(hx : Summable (λ i ↦ x i ^ 2))",
            "(hy : Summable (λ i ↦ y i ^ 2))",
        ],
        goal="(∑' i, x i * y i) ^ 2 ≤ ∑' i, ∑' j, x i ^ 2 * y j ^ 2",
        previous_code="",
    )

    # Add hypotheses using mock client
    state.add_hypotheses(MockClaudeClient(), verbose=False)

    # Expected hypotheses after extraction
    expected_hypotheses = [
        MathStatement(
            "lem1",
            [],
            "  ∑' i, ∑' j, x i ^ 2 * y j ^ 2 = (∑' i, x i ^ 2) * (∑' j, y j ^ 2)",
            None,
        ),
        MathStatement(
            "lem2",
            [],
            "(∑' i, x i * y i) ^ 2 ≤ (∑' i, x i ^ 2) * (∑' i, y i ^ 2)",
            None,
        ),
        MathStatement("lem3", ["(y : ℕ → ℝ)"], "∑' j, y j ^ 2 = ∑' i, y i ^ 2", None),
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
        assert (
            actual.assumptions == expected.assumptions
        ), f"Hypothesis name mismatch:\nExpected: {expected}\nGot: {actual}"
