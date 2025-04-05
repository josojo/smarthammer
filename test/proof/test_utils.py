import unittest
from hammer.proof.utils import unicode_escape
from hammer.proof.utils import extract_proof_from_text
from hammer.proof.proof import parse_string_to_hypotheses, MathStatement


class TestUnicodeEscape(unittest.TestCase):
    def test_ascii_characters(self):
        # Test with basic ASCII characters
        input_str = "Hello World"
        self.assertEqual(unicode_escape(input_str), "Hello World")

    # def test_unicode_characters(self):
    #     # Test with Unicode characters
    #     input_str = "Hello 世界"  # Chinese characters
    #     self.assertEqual(unicode_escape(input_str), "Hello \\u4e16\\u754c")

    # def test_special_characters(self):
    #     # Test with special characters
    #     input_str = "π ≤ ∞"  # Mathematical symbols
    #     self.assertEqual(unicode_escape(input_str), "\\u03c0 \\u2264 \\u221e")

    def test_empty_string(self):
        # Test with empty string
        self.assertEqual(unicode_escape(""), "")

    def test_extract_proof_from_text(self):
        # Input text with theorem and proof
        input_text = """### Proof for Theorem `THEROEM123`
        ```lean  
    import Mathlib
    theorem THEROEM123 (n : ℕ) (oh0 : 0 < n) :
    ∀ n, 3(21n + 4) - 5(14n + 3) = -7n - 3 := by
    intro n
    calc
    3 (21 n + 4) - 5 (14 n + 3)
    = 3 21 n + 3 4 - 5 14 n - 5 3 := by rw [mul_add, mul_add]
    = 63 n + 12 - 70 n - 15 := by ring
    = -7 n - 3 := by ring
    ```### Explanation

    1. **Introduction of the Theorem**: The theorem states that for any natural number \( n \) greater than 0, the expression \( 3(21n + 4) - 5(14n + 3) \) simplifies to \( -7n - 3 \).

    2. **Step-by-Step Proof**:
    - We start by introducing the variable  n .
    - We then use the `calc` block to perform a series of algebraic manipulations:
        - Expand the multiplication using the distributive property.
        - Simplify the resulting terms.
        - Combine like terms to achieve the final simplified form.

    3. **Verification**:
    - Each step in the `calc` block is verified using the `rw` tactic to rewrite expressions and the `ring` tactic to simplify algebraic expressions.
    - The final result matches the expected outcome, confirming the theorem.
    """
        expected_proof = """

    intro n
    calc
    3 (21 n + 4) - 5 (14 n + 3)
    = 3 21 n + 3 4 - 5 14 n - 5 3 := by rw [mul_add, mul_add]
    = 63 n + 12 - 70 n - 15 := by ring
    = -7 n - 3 := by ring
    """

        result = extract_proof_from_text("5(14n + 3) = -7n - 3", input_text)
        assert len(result) == 1  # Should only find one proof block
        assert result[0] == expected_proof

        # Test with no lean blocks
        assert extract_proof_from_text("", "No lean blocks here") == []

        # Test with empty lean block
        assert extract_proof_from_text("", "```lean\n```") == ["\n"]

        # Test with lean block but no theorem
        code_without_theorem = "```lean\nfoo := bar\n```"
        assert extract_proof_from_text("", code_without_theorem) == ["\nfoo := bar\n"]
        code_without_theorem_2 = """
```lean
intros a b g hga hgb
by_cases h : a >= b
· exact Nat.dvd_sub h hga hgb
· simp [Nat.sub_eq_zero_of_le (le_of_not_ge h)
```
        """
        assert extract_proof_from_text("", code_without_theorem_2) == [
            """\nintros a b g hga hgb\nby_cases h : a >= b\n· exact Nat.dvd_sub h hga hgb\n· simp [Nat.sub_eq_zero_of_le (le_of_not_ge h)\n"""
        ]
        code_wihtout_theorem_3 = """
```lean
have hg_dvd_2a : g ∣ 2 * (21*n + 4) := Nat.dvd_mul_right _ hg_dvd_a
have h_le : 2 * (21*n + 4) ≤ 3 * (14*n + 3) := by
-- Rewrite the inequality using the given hypotheses p1 and p0.
  rw [p1, p0] -- The goal becomes 42*n + 8 ≤ 42*n + 9
```
        """
        assert extract_proof_from_text("", code_wihtout_theorem_3) == [
            """\nhave hg_dvd_2a : g ∣ 2 * (21*n + 4) := Nat.dvd_mul_right _ hg_dvd_a\nhave h_le : 2 * (21*n + 4) ≤ 3 * (14*n + 3) := by\n  rw [p1, p0] -- The goal becomes 42*n + 8 ≤ 42*n + 9\n"""
        ]


# Add a new test class for the parser function
class TestParseStringToHypotheses(unittest.TestCase):

    def test_simple_lemma(self):
        input_str = "lemma base_case_holds : 12 ∣ 4^(0+1) + 20"
        expected = MathStatement("base_case_holds", [], "12 ∣ 4^(0+1) + 20")
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)
        self.assertEqual(
            result, expected
        )  # Also check overall equality if __eq__ is defined

    def test_lemma_with_params(self):
        input_str = "lemma inductive_step_algebra_nat (k : ℕ) : 4^(k+2) + 20 + 60 = 4 * (4^(k+1) + 20)"
        expected = MathStatement(
            "inductive_step_algebra_nat",
            ["(k : ℕ)"],
            "4^(k+2) + 20 + 60 = 4 * (4^(k+1) + 20)",
        )
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)

    def test_lemma_with_multiple_params(self):
        # Tests if parameters before the colon are correctly ignored by the parser
        input_str = "lem div_preserves_mul (a b c : ℕ) (h : a ∣ b) : a ∣ c * b"
        expected = MathStatement(
            "div_preserves_mul", ["(a b c : ℕ)", "(h : a ∣ b)"], "a ∣ c * b"
        )
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)

    def test_lemma_with_numbered_name(self):
        # Tests if parameters before the colon are correctly ignored by the parser
        input_str = "lem32 div_preserves_mul (a b c : ℕ) (h : a ∣ b) : a ∣ c * b"
        expected = MathStatement(
            "div_preserves_mul", ["(a b c : ℕ)", "(h : a ∣ b)"], "a ∣ c * b"
        )
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)

    def test_lemma_with_whitespace(self):
        input_str = "  lemma   twelve_divides_sixty   :  12 ∣ 60  "
        expected = MathStatement("twelve_divides_sixty", [], "12 ∣ 60")
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)

    def test_lemma_with_forall(self):
        input_str = " lemma lem1 : ∀ (a b c : ℤ), a ∣ b → a ∣ c → a ∣ (b - c)"
        expected = MathStatement(
            "lem1", [], "∀ (a b c : ℤ), a ∣ b → a ∣ c → a ∣ (b - c)"
        )
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)

    def test_theorem_parsing(self):
        input_str = "theorem example_thm (n : ℕ) : n > 0"
        expected = MathStatement("example_thm", ["(n : ℕ)"], "n > 0")
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)

    def test_no_match_fallback(self):
        input_str = "Just some text : not a lemma"
        # Expect fallback behavior: empty name/assumptions, full string as statement
        expected = MathStatement("", [], "Just some text : not a lemma")
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)

    def test_empty_input(self):
        input_str = ""
        # Fallback behavior for empty string
        expected = MathStatement("", [], "")
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)

    def test_lemma_no_colon(self):
        input_str = "lemma my_lemma_no_colon"
        # Fallback behavior if no colon is found after the name/params
        expected = MathStatement("", [], "lemma my_lemma_no_colon")
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)

    def test_lemma_multiline_statement(self):
        # Test parsing when the statement part spans multiple lines
        input_str = """lemma complex_lemma (x y : Nat)
                        (h : x > 0) :
                        ∃ z, x + y = z"""
        expected = MathStatement(
            "complex_lemma", ["(x y : Nat)", "(h : x > 0)"], "∃ z, x + y = z"
        )
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(
            result.statement.strip(), expected.statement.strip()
        )  # Strip whitespace for comparison

    def test_lemma_with_implicit_args(self):
        # Test parsing lemmas with implicit arguments like { }
        input_str = "lemma le_antisymm {a b : Nat} : a ≤ b → b ≤ a → a = b"
        expected = MathStatement(
            "le_antisymm", ["{a b : Nat}"], "a ≤ b → b ≤ a → a = b"
        )
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)

    def test_lemma_with_instance_args(self):
        # Test parsing lemmas with instance arguments like [ ]
        input_str = "lemma add_comm [AddCommSemigroup α] (a b : α) : a + b = b + a"
        expected = MathStatement(
            "add_comm", ["[AddCommSemigroup α]", "(a b : α)"], "a + b = b + a"
        )
        result = parse_string_to_hypotheses(input_str)
        self.assertEqual(result.name, expected.name)
        self.assertEqual(result.assumptions, expected.assumptions)
        self.assertEqual(result.statement, expected.statement)


if __name__ == "__main__":
    unittest.main()
