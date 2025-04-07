from .utils import (
    extract_lean_blocks,
    extract_proof_from_text,
    unicode_escape,
)
import logging
import re

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
    goal_code,
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
            proofs = extract_proof_from_text(goal_code, response)
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


class MathStatement:
    """Represents a mathematical statement with its name, statement, and proof."""

    def __init__(self, name, assumptions, statement, proof=None):
        self.name = name
        # Ensure assumptions is always a list of strings
        self.assumptions = [str(a).strip() for a in assumptions] if assumptions else []
        self.statement = str(statement).strip() if statement else ""
        self.proof = proof

    def __str__(self):
        """Convert statement to string format."""
        # Format each assumption as (assumption) and join with ' → '
        if self.assumptions:
            formatted_assumptions = [f"({a.strip()})" for a in self.assumptions]
            assumptions_str = " " + " → ".join(formatted_assumptions)
        else:
            assumptions_str = ""

        # Handle potential empty name in fallback case
        name_str = self.name if self.name else ""
        colon_str = ": " if self.statement else ""  # Add colon only if statement exists

        # Combine name, formatted assumptions, colon, and statement
        # Ensure correct spacing when assumptions are present or absent
        return f"({name_str}{assumptions_str}{colon_str}{self.statement})"

    def __repr__(self):
        """Representation for debugging."""
        return f"MathStatement(name='{self.name}', assumptions={self.assumptions}, statement='{self.statement}')"

    def __eq__(self, other):
        """Check equality between two MathStatement objects."""
        if not isinstance(other, MathStatement):
            return NotImplemented
        return (
            self.name == other.name
            and self.assumptions == other.assumptions
            and self.statement == other.statement
        )


def remove_lean_comments(h: str) -> str:
    """
    Removes lines that start with -- (Lean comments) from the input string.

    Args:
        h: Input string potentially containing Lean comments

    Returns:
        String with Lean comment lines removed
    """
    # Split into lines and filter out comment lines
    lines = h.split("\n")
    non_comment_lines = [line for line in lines if not line.strip().startswith("--")]
    return "\n".join(non_comment_lines)


def extract_top_level_blocks(text: str) -> list[str]:
    """
    Extracts top-level blocks enclosed in (), [], or {} from a string,
    correctly handling nesting.
    """
    blocks = []
    balance = 0
    current_block_start = -1
    expected_closer = None
    opener = None  # Track the specific opener '(', '[', or '{'

    for i, char in enumerate(text):
        if current_block_start == -1:  # Looking for start of a block
            if char in "([{":
                current_block_start = i
                opener = char
                if char == "(":
                    expected_closer = ")"
                elif char == "[":
                    expected_closer = "]"
                else:
                    expected_closer = "}"
                balance = 1
        else:  # Inside a block
            if char == opener:  # Nested same opener
                balance += 1
            elif char == expected_closer:  # Corresponding closer
                balance -= 1
                if balance == 0:  # End of top-level block
                    blocks.append(text[current_block_start : i + 1])
                    current_block_start = -1
                    expected_closer = None
                    opener = None  # Reset opener
    return [b.strip() for b in blocks]


def parse_string_to_hypotheses(h: str) -> MathStatement:
    """
    Parses a string (potentially containing a lemma or theorem)
    to create a MathStatement object representing the core statement.
    Recognizes 'lemma', 'theorem', 'lem', or 'lem<number>' as starting keywords.
    Finds the main colon separating the head (name, params) from the body (statement),
    correctly handling nested brackets/braces/parentheses in parameters.
    Extracts top-level parenthesized (...), bracketed [...], and curly-braced {...}
    blocks found between the name and the main colon as assumptions.

    Args:
        h: The input string, expected to contain a lemma or theorem definition.

    Returns:
        MathStatement: An object representing the parsed statement.
                         Returns a fallback statement if parsing fails.
    """
    h = remove_lean_comments(h)
    h = h.strip()

    # Match keyword and name first
    # Allows 'lem' or 'lem' followed by digits. Name stops at whitespace or brackets/colon.
    head_match = re.match(r"^\s*(lemma|theorem|lem\d*)\s+([^\s\(:\{\[\}\]]+)", h)
    if not head_match:
        logger.warning(
            f"Could not parse keyword/name from: '{h[:100]}...'. Treating as simple statement."
        )
        return MathStatement("", [], h)

    keyword = head_match.group(1)
    name = head_match.group(2)
    start_of_params = head_match.end()

    # Scan for the main colon, skipping over balanced pairs '()', '[]', '{}'
    balance = 0
    main_colon_idx = -1
    for i, char in enumerate(h[start_of_params:], start=start_of_params):
        if char in "([{":
            balance += 1
        elif char in ")]}":
            # Ensure balance doesn't go below 0 due to malformed input
            if balance > 0:
                balance -= 1
        elif char == ":" and balance == 0:
            main_colon_idx = i
            break

    if main_colon_idx == -1:
        logger.warning(
            f"Could not find main colon for: '{h[:100]}...'. Treating as simple statement."
        )
        # Fallback: Use the original string as statement, retain parsed name if available
        return MathStatement(name, [], h[start_of_params:].strip())

    assumptions_part = h[start_of_params:main_colon_idx].strip()
    statement = h[main_colon_idx + 1 :].strip()

    # Now extract top-level assumption blocks from assumptions_part using the helper
    assumptions = extract_top_level_blocks(assumptions_part)

    # Ensure statement is not empty string which might cause issues later
    if not statement:
        head_part = h[:main_colon_idx].strip()
        logger.warning(f"Parsed empty statement for head: '{head_part}'")

    return MathStatement(name, assumptions, statement)


class ProofSearchState:
    def __init__(self, name, hypotheses, previous_code, goal, nl_proof=None):
        self.name = name
        self.statement = MathStatement(name, hypotheses, goal)
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
        prompt_part_2 = f"```lean\n theorem {self.name} {' '.join(self.statement.assumptions) + ' '.join(map(str, self.proven_hypotheses))} : \n {self.goal} ```."
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
        given_assumptions_as_set = set()
        for a in self.statement.assumptions:
            given_assumptions_as_set.add(a)
        print("given_assumptions_as_set", given_assumptions_as_set)
        hypotheses = []
        lean_blocks = extract_lean_blocks(response)  # Extract all lean blocks first
        if not lean_blocks:
            logger.warning(f"No Lean blocks extracted from response: {response}")
            # Maintain original behavior of raising exception if no blocks found
            raise Exception("No hypotheses extracted (no Lean blocks found)")

        for block_content in lean_blocks:
            # Parse each extracted block content
            statement = parse_string_to_hypotheses(block_content)
            # filter for assumptions that are not already in the given assumptions
            assumptions = []
            for a in statement.assumptions:
                if a not in given_assumptions_as_set:
                    assumptions.append(a)
                    print("added assumption", a)
            statement.assumptions = assumptions

            # Only add if parsing was successful (i.e., name or statement is not empty)
            # The check for statement ensures the fallback case doesn't add empty statements
            if statement.name or statement.statement:
                hypotheses.append(statement)
            else:
                # This case should ideally not happen with the current fallback logic, but good for safety
                logger.warning(
                    f"Failed to parse a valid statement or name from block: '{block_content[:100]}...'"
                )

        if len(hypotheses) == 0:
            # This check is now more robust, failing only if *no valid* statements were parsed from the blocks found
            raise Exception("No valid hypotheses extracted from the found Lean blocks")
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
            self.theoretical_hypotheses[number_of_hypotheses],
            prompt_part_1,
            prompt_part_2,
            prompt_part_3,
            examples,
            moogle_helper_info,
            verbose,
        )
        return proof

    def get_theorem_code(self):
        # Start with the theorem name and original hypotheses
        code = f"theorem {self.name} {' '.join(self.statement.assumptions)}"

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
            client,
            code,
            prompt_part_1,
            prompt_part_2,
            prompt_part_3,
            examples,
            "",
            verbose,
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
                for line in self.theoretical_hypotheses[
                    hypothesis_number
                ].statement.split("\n")
                if not line.strip().startswith("--")
            ]
        )
        if goal.endswith("\n"):
            goal = goal.rstrip("\n")
        code = f"theorem {self.theoretical_hypotheses[hypothesis_number].name} {' '.join(self.statement.assumptions)+ ' '.join(map(str, self.proven_hypotheses))+ ' '.join(map(str, self.theoretical_hypotheses[hypothesis_number].assumptions))} : \n {goal} := by"
        code = unicode_escape(code)
        return code

    def hypothesis_as_goal(self, hypothesis_number: int) -> str:
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
                for line in self.theoretical_hypotheses[
                    hypothesis_number
                ].statement.split("\n")
                if not line.strip().startswith("--")
            ]
        )
        if goal.endswith("\n"):
            goal = goal.rstrip("\n")
        return goal

    def build_final_proof(self, proof):
        initial_part = f"theorem {self.name} {' '.join(self.statement.assumptions)} : \n{self.goal} := by"
        have_statements = "\n".join(
            [
                f"have {h.name} : {h.statement} := by\n"
                + "\n".join("  " + line for line in h.proof.split("\n"))
                for h in self.proven_hypotheses
            ]
        )
        final_proof = f"{initial_part} \n{have_statements} \n{proof}"
        final_proof = unicode_escape(final_proof)
        return final_proof
