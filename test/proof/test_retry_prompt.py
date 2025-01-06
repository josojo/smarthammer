import unittest
from hammer.proof.retry import prompt_with_previous_code_and_cutoff


class TestPromptWithPreviousCodeAndCutoff(unittest.TestCase):
    def test_prompt_with_previous_code_and_cutoff(self):
        previous_code = "import Mathlib\n"
        theorem_code = (
            "theorem YourTheoremName2 (n : ℕ) (oh0 : 0 < n) : \n"
            "∀ a b : ℕ, (∃ (x y : ℤ), x*a + y*b = 1) → Nat.gcd a b = 1 := "
        )
        ans_code = (
            "by\n"
            "  intro a b h\n"
            "  rcases h with ⟨x, y, hxy⟩\n"
            "  norm_cast at hxy\n"
            "  have := Nat.gcd_eq_gcd_ab a b\n"
            "  rw [this]\n"
            "  norm_cast\n"
            "  linarith\n"
        )
        error_messages = [
            {
                "severity": "error",
                "pos": {"line": 7, "column": 6},
                "endPos": {"line": 7, "column": 10},
                "data": (
                    "tactic 'rewrite' failed, did not find instance of the pattern in the target expression\n"
                    "  ↑(a.gcd b)\n"
                    "case intro.intro\n"
                    "n : ℕ\n"
                    "oh0 : 0 < n\n"
                    "a b : ℕ\n"
                    "x y : ℤ\n"
                    "hxy : x * ↑a + y * ↑b = 1\n"
                    "this : ↑(a.gcd b) = ↑a * a.gcdA b + ↑b * a.gcdB b\n"
                    "⊢ a.gcd b = 1"
                ),
            }
        ]

        expected_prompt = (
            "Finish the following proof \n```lean4 \n"
            "import Mathlib\n\n"
            " theorem YourTheoremName2 (n : ℕ) (oh0 : 0 < n) : \n"
            "∀ a b : ℕ, (∃ (x y : ℤ), x*a + y*b = 1) → Nat.gcd a b = 1 := by\n"
            "  intro a b h\n"
            "  rcases h with ⟨x, y, hxy⟩\n"
            "  norm_cast at hxy\n"
            "  have := Nat.gcd_eq_gcd_ab a b\n"
        )

        result = prompt_with_previous_code_and_cutoff(
            previous_code, theorem_code, ans_code, error_messages
        )
        self.assertEqual(result[0].strip(), expected_prompt.strip())


if __name__ == "__main__":
    unittest.main()
