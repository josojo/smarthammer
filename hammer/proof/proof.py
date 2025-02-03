from .utils import (
    extract_lean_blocks,
    extract_proof_from_text,
    unicode_escape,
)
import logging

logger = logging.getLogger(__name__)

# Configure logging handler if none exists
if not logger.handlers:
    handler = logging.StreamHandler()
    formatter = logging.Formatter("%(levelname)s - %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.INFO)


def proof_based_on_solver(
    client,
    prompt_part_1,
    prompt_part_2,
    prompt_part_3,
    examples,
    moogle_helper_info="",
    verbose=False,
) -> str:
    max_retries = 3
    for attempt in range(max_retries):
        try:
            total_prompt = prompt_part_1 + prompt_part_2
            if client.name != "DeepSeekProver1.5":
                total_prompt += prompt_part_3 + examples + moogle_helper_info
            logger.debug(f"Talking to {client.name} ")
            response = client.send(total_prompt, verbose)
            if client.name == "DeepSeekProver1.5":
                if "### Final Proof" in response:
                    response = response.split("### Final Proof")[-1]
                first_triple_backtick = response.find("```")
                if first_triple_backtick != -1:
                    if (
                        response[first_triple_backtick : first_triple_backtick + 7]
                        != "```lean"
                    ):
                        response = """```lean\n""" + response
            proofs = extract_proof_from_text(response)
            if not proofs:
                raise IndexError("No proof found in response")
            return proofs[0]
        except (IndexError, Exception) as e:
            if attempt == max_retries - 1:
                logger.error(
                    f"Failed to extract proof after {max_retries} attempts: {str(e)}"
                )
                raise
            logger.warning(f"Attempt {attempt + 1} failed, retrying...")
            continue


class Hypothesis:
    """Represents a mathematical hypothesis with its name, statement, and proof."""

    def __init__(self, name, hypothesis, proof):
        self.name = name
        self.hypothesis = hypothesis
        self.proof = proof

    def add_proof(self, proof):
        """Add or update the proof for this hypothesis."""
        self.proof = proof

    def __str__(self):
        """Convert hypothesis to string format."""
        return f"({self.name} : {self.hypothesis})"

    def __repr__(self):
        """Representation for debugging."""
        return self.__str__()


class ProofSearchState:
    def __init__(self, name, hypotheses, previous_code, goal, nl_proof=None):
        self.name = name
        self.original_hypotheses = hypotheses
        self.previous_code = previous_code
        self.goal = goal
        self.theoretical_hypotheses = []
        self.proven_hypotheses = []
        self.proof = None
        self.nl_proof = nl_proof

    def __repr__(self):
        return f"theorem {self.name}, {self.proof})"

    def __str__(self):
        return f"{self.name}: {self.proof}"

    def add_hypotheses(self, client, verbose=False):
        prompt_part_1 = (
            f"You are a math expert and you want to proof the following lean theorem:\n"
        )
        prompt_part_2 = f"```lean\n theorem {self.name} {' '.join(self.original_hypotheses) + ' '.join(map(str, self.proven_hypotheses))} : \n {self.goal} ```."
        prompt_part_3 = "Using chain of thought formulate a proof of the theorem in natural language and then extract the critical intermediate steps and formulate them as lean4 hypothesis. Put each hypothesis into a new ```lean ``` block. Each hypothesis should start with `lemma`, then the lemma name as in the following examples."
        examples = f"""Examples:
        Example 1:
        Input: {prompt_part_1} ```lean theorem mathd_numbertheory_457_1 (n : ℕ)(h₁ : 80325∣ (n !) ) : 17 ≤ n ```. {prompt_part_3}
        Output: 
            Natural language proof: The number 80325∣ has the factorization 3x3x3x5x5x7x17. The highest prime of this factorization is 17. One also knows that a prime only divides n! if n is bigger than the prime, as otherwise the prime is not part of the product of n!. Hence, 17 ≤ n. \n
            Lean4 hypotheses: ```lean\nlemma lem1 : 80325 = 3*3*3*5*5*7*17```, ```lean\nlemma lem2 : ∀ p : ℕ, Nat.Prime p → p∣(n !) → p ≤ n ``` and ```lean\nlemma lem3 : 17∣(n !) ```.
        Example 2:
        Input: {prompt_part_1} ```lean theorem imo_2019_p1 (f : ℤ → ℤ) (h : ((∀ a b, f (2 * a) + (2 * f b) = f (f (a + b)))) : ((∀ z, f z = 0 )∨ (∃ c, ∀ z, f z = 2 * z + c))) ```. {prompt_part_3}
        Output:
           Natural language proof: Substituting a = 0, b = n + 1 gives f (f (n + 1)) = f (0) + 2 * f (n+1). Substituting
            a = 1, b = n gives f (f (n + 1)) = f (2) + 2 * f (n). Hence, f (n + 1) - f (n) = 1/2 * (f (2) - f (0)). Since this holds for all n, f is linear.
           Writing f (n) = Mn + K for arbitrary constants M and K, we and putting into the equations, we get M =2 and K = f (0).
           Lean4 hypotheses:  \n```lean\n lemma lem1 : ∀ n, f (f (n + 1)) = f (0) + 2 * f (n+1) ```, \n```lean\n lemma lem2 : ∀ n, f (f (n + 1)) = f (2) + 2 * f (n)```, \n```lean\n lemma lem3 : ∀ b, f (b + 1) - f (b) = (f 2 - f 0) / 2 ```, \n```lean\n lemma lem4 : ∀ b, f (b) = (f 2 - f 0) / 2 *b + f 0 ```.
        """
        response = client.send(
            prompt_part_1 + prompt_part_2 + prompt_part_3 + examples, verbose
        )
        hypotheses = []
        for h in extract_lean_blocks(response):
            if (
                h.startswith("\n lemma ")
                or h.startswith("\nlemma ")
                or h.startswith("lemma ")
            ):
                # Find the first colon that's not inside parentheses/brackets
                paren_count = 0
                colon_index = -1
                for i, char in enumerate(h):
                    if char in "([{":
                        paren_count += 1
                    elif char in ")]}":
                        paren_count -= 1
                    elif char == ":" and paren_count == 0:
                        colon_index = i
                        break

                if colon_index != -1:
                    hypothesis = h[colon_index + 1 :].strip()
                else:
                    hypothesis = h
                hypotheses.append(hypothesis)
            else:
                hypotheses.append(h)

        if len(hypotheses) == 0:
            raise Exception("No hypotheses extracted")
        self.theoretical_hypotheses.extend(hypotheses)

    def remove_hypotheses(self, hypothesis_number: int):
        self.theoretical_hypotheses.pop(hypothesis_number)

    def generate_proof_candidate_for_hypotheses(
        self,
        client,
        number_of_hypotheses,
        starting_code,
        moogle_helper_info,
        verbose=False,
    ):
        assert number_of_hypotheses < len(self.theoretical_hypotheses)
        prompt_part_1 = f"You are a math expert and you want to complete the following lean theorem proof:\n"
        prompt_part_2 = (
            "```lean\n"
            + self.previous_code
            + "\n"
            + self.hypothesis_as_code(number_of_hypotheses)
            + f" {starting_code}\n"
        )
        prompt_part_3 = (
            "```.\n"
            + f"Complete the proof and put only the proof into ```lean ``` block."
        )
        examples = f"""
Examples:
Example 1:
Input: {prompt_part_1} ```lean\n theorem p \n (f : ℤ → ℤ)\n   (h0 : (∀ a b, f (2 * a) + (2 * f b) = f (f (a + b))))\n (h1 : (∀ b, f (0) + (2 * f b) = f (f (b) ) :  (∀ a b, f (2 * a) + (2 * f b) = f (f (a + b) := by\n intro a b\n ```. {prompt_part_3} 
Output: 
```lean
-- Apply h to get first equation
have eq1 := h a b
-- Apply h0 to (a + b)
have eq2 := h0 (a + b)
-- From eq1: f(2a) + 2f(b) = f(f(a+b))
-- From eq2: f(0) + 2f(a+b) = f(f(a+b))
-- Therefore: f(2a) + 2f(b) = f(0) + 2f(a+b)
rw [← eq2] at eq1
rw [add_comm (f 0) (2 * f (a + b))] at eq1
exact eq1
```
Example 2:
Input: {prompt_part_1}  ```lean\n theorem exists_infinite_primes2 (n : ℕ) : ∃ p, n ≤ p ∧ Prime p := by\n let p := minFac (n ! + 1) ```. {prompt_part_3} 
Output: 
```lean
have f1 : n ! + 1 ≠ 1 := ne_of_gt <| succ_lt_succ <| factorial_pos _
have pp : Prime p := minFac_prime f1
have np : n ≤ p :=
    le_of_not_ge fun h =>
    have h1 : p ∣ n ! := dvd_factorial (minFac_pos _) h
    have h2 : p ∣ 1 := (Nat.dvd_add_iff_right h1).2 (minFac_dvd _)
    pp.not_dvd_one h2
⟨p, np, pp⟩
```
"""
        proof = proof_based_on_solver(
            client,
            prompt_part_1,
            prompt_part_2,
            prompt_part_3,
            examples,
            moogle_helper_info,
            verbose,
        )
        return proof

    def get_theorem_code(self):
        # code = f"theorem {self.name} {' '.join(self.original_hypotheses)} \n {' \n'.join(map(str, self.proven_hypotheses))} : \n {self.goal} := by\n"
        # Start with the theorem name and original hypotheses
        code = f"theorem {self.name} {' '.join(self.original_hypotheses)}"

        # Add each proven hypothesis on a new line
        if self.proven_hypotheses:
            proven_hyps = "\n".join(f"  {str(h)}" for h in self.proven_hypotheses)
            code += f"\n{proven_hyps}"

        # Add the goal and by
        code += f" : \n{self.goal} := by\n"
        code = unicode_escape(code)
        return code

    def generate_final_proof(self, client, starting_code, verbose=False):

        code = self.get_theorem_code()
        prompt_part_1 = f"You are a math expert and you want to complete the following lean theorem proof:\n"
        prompt_part_2 = (
            "```lean " + self.previous_code + "\n" + code + f" {starting_code}"
        )
        prompt_part_3 = (
            "```\n"
            + f"Complete the proof and put only the proof into ```lean ``` block.\n"
        )
        examples = f"""Examples:
Example 1:
Input: {prompt_part_1} ```lean\n theorem p :\n (f : ℤ → ℤ)\n   (h0 : (∀ a b, f (2 * a) + (2 * f b) = f (f (a + b))))\n (h1 : (∀ b, f (0) + (2 * f b) = f (f (b) ) :  (∀ a b, f (2 * a) + (2 * f b) = f (f (a + b) := by\n intro a b\n ```.\n {prompt_part_3} 
Output: 
```lean
-- Apply h to get first equation
have eq1 := h a b
-- Apply h0 to (a + b)
have eq2 := h0 (a + b)
-- From eq1: f(2a) + 2f(b) = f(f(a+b))
-- From eq2: f(0) + 2f(a+b) = f(f(a+b))
-- Therefore: f(2a) + 2f(b) = f(0) + 2f(a+b)
rw [← eq2] at eq1
rw [add_comm (f 0) (2 * f (a + b))] at eq1
exact eq1
```
Example 2:
Input: {prompt_part_1}  ```lean theorem exists_infinite_primes2 (n : ℕ) : ∃ p, n ≤ p ∧ Prime p := by\n let p := minFac (n ! + 1) ```.\n {prompt_part_3} 
Output: 
```lean
have f1 : n ! + 1 ≠ 1 := ne_of_gt <| succ_lt_succ <| factorial_pos _
have pp : Prime p := minFac_prime f1
have np : n ≤ p :=
    le_of_not_ge fun h =>
    have h1 : p ∣ n ! := dvd_factorial (minFac_pos _) h
    have h2 : p ∣ 1 := (Nat.dvd_add_iff_right h1).2 (minFac_dvd _)
    pp.not_dvd_one h2
⟨p, np, pp⟩
```
"""
        proof = proof_based_on_solver(
            client, prompt_part_1, prompt_part_2, prompt_part_3, examples, "", verbose
        )
        return proof

    def set_proof(self, proof):
        self.proof = proof

    def hypothesis_as_code(self, hypothesis_number: int) -> str:
        """
        Returns the hypothesis as Lean code for a given hypothesis number.

        Args:
            proof_state: The proof search state
            hypothesis_number: The index of the hypothesis to return

        Returns:
            The hypothesis as Lean code
        """
        goal = "\n".join(
            [
                line
                for line in self.theoretical_hypotheses[hypothesis_number].split("\n")
                if not line.strip().startswith("--")
            ]
        )
        if goal.endswith("\n"):
            goal = goal.rstrip("\n")
        code = f"theorem {self.name} {' '.join(self.original_hypotheses)+ ' '.join(map(str, self.proven_hypotheses))} : \n {goal} := by"
        code = unicode_escape(code)
        return code

    def build_final_proof(self, proof):
        initial_part = f"theorem {self.name} {' '.join(self.original_hypotheses)} : \n{self.goal} := by"
        have_statements = "\n".join(
            [
                f"have {h.name} : {h.hypothesis} := by\n"
                + "\n".join("  " + line for line in h.proof.split("\n"))
                for h in self.proven_hypotheses
            ]
        )
        final_proof = f"{initial_part} \n{have_statements} \n{proof}"
        final_proof = unicode_escape(final_proof)
        return final_proof
