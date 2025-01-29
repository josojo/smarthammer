from pydantic import BaseModel
from typing import List
import os
from hammer.api.types import AIForHypothesesProof
from hammer.api.deepseek_official.client import Client as DeepSeekOfficialClient
from hammer.api.gemini.client import Client as GeminiClient
from hammer.api.claude.client import Client as ClaudeClient
from hammer.api.deepseek.client import Client as DeepSeekClient
from hammer.api.openai.client import Client as OpenAIClient
from hammer.api.mock.mock_client import Client as MockClient
from hammer.lean.server import LeanServer

api_output_1 = """
Natural language proof:
We want to show that \gcd(21n + 4, 14n + 3) = 1 for any natural number n with 0 < n. We use the fact that \gcd(a, b) = \gcd(a - b, b). Substituting a = 21n + 4 and b = 14n + 3, we get:

\[
\gcd(21n + 4,\, 14n + 3)
= \gcd\bigl((21n + 4) - (14n + 3),\, 14n + 3\bigr)
= \gcd(7n + 1,\, 14n + 3).
\]

Next, we apply the same gcd property again but now we subtract twice (7n + 1):

\[
\gcd(7n + 1,\, 14n + 3)
= \gcd\bigl(7n + 1,\,(14n + 3) - 2(7n + 1)\bigr)
= \gcd(7n + 1,\, 1).
\]

Since the gcd of any number and 1 is always 1, we conclude


\gcd(7n + 1,\, 1) = 1.


Hence,


\gcd(21n + 4,\, 14n + 3) = 1.

           ```lean
lemma lem1 : ∀ a b : ℕ, Nat.gcd a b = Nat.gcd (a - b) b ```,           

```lean
lemma lem2 : ∀ n : ℕ, Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (7 * n + 1) (14 * n + 3)```,           
```lean
lemma lem3 : ∀ n : ℕ, Nat.gcd (7 * n + 1) (14 * n + 3) = Nat.gcd (7 * n + 1) 1 ```, 
```lean
lemma lem4 : ∀ x : ℕ, Nat.gcd x 1 = 1 ```, 
```lean
lemma lem5 : 14 * n + 3 - 2 * (7 * n + 1) = 1 
 """

class SolverLimits(BaseModel):
    # Iteration limits
    max_iteration_hypotheses_proof: int = 10
    max_correction_iteration_hypotheses_proof: int = 10
    max_iteration_final_proof: int = 10
    max_correction_iteration_final_proof: int = 10

    # Allowed AI configurations
    allowed_hypothesis_generation_models: List[AIForHypothesesProof] = [
        AIForHypothesesProof.GEMINI,
        AIForHypothesesProof.CLAUDE,
        AIForHypothesesProof.DEEPSEEK_1_5,
        AIForHypothesesProof.OPENAI_O1,  # Currently mocked
        AIForHypothesesProof.OPENAI_4O,
        AIForHypothesesProof.DEEPSEEK_R1,
    ]

    allowed_hypothesis_proof_models: List[AIForHypothesesProof] = [
        AIForHypothesesProof.DEEPSEEK_1_5,
        AIForHypothesesProof.CLAUDE,
        AIForHypothesesProof.GEMINI,
    ]

    allowed_final_proof_models: List[AIForHypothesesProof] = [
        AIForHypothesesProof.DEEPSEEK_1_5,
        AIForHypothesesProof.CLAUDE,
        AIForHypothesesProof.GEMINI,
    ]


# Global configuration instance
SOLVER_LIMITS = SolverLimits()

def validate_inputs(kwargs, logger):
    """Validate input parameters to ensure they are within acceptable limits."""
    # Validate iteration limits
    if (
        kwargs.get("max_iteration_hypotheses_proof", 0)
        >= SOLVER_LIMITS.max_iteration_hypotheses_proof
    ):
        raise ValueError(
            f"max_iteration_hypotheses_proof should be less than {SOLVER_LIMITS.max_iteration_hypotheses_proof}"
        )
    if (
        kwargs.get("max_correction_iteration_hypotheses_proof", 0)
        >= SOLVER_LIMITS.max_correction_iteration_hypotheses_proof
    ):
        raise ValueError(
            f"max_correction_iteration_hypotheses_proof should be less than {SOLVER_LIMITS.max_correction_iteration_hypotheses_proof}"
        )
    if (
        kwargs.get("max_iteration_final_proof", 0)
        >= SOLVER_LIMITS.max_iteration_final_proof
    ):
        raise ValueError(
            f"max_iteration_final_proof should be less than {SOLVER_LIMITS.max_iteration_final_proof}"
        )
    if (
        kwargs.get("max_correction_iteration_final_proof", 0)
        >= SOLVER_LIMITS.max_correction_iteration_final_proof
    ):
        raise ValueError(
            f"max_correction_iteration_final_proof should be less than {SOLVER_LIMITS.max_correction_iteration_final_proof}"
        )

    # Validate AI model selections
    if (
        kwargs.get("ai_for_hypotheses_generation")
        not in SOLVER_LIMITS.allowed_hypothesis_generation_models
    ):
        raise ValueError(
            f"Invalid AI model for hypothesis generation. Allowed models: {SOLVER_LIMITS.allowed_hypothesis_generation_models}"
        )

    if (
        kwargs.get("ai_for_hyptheses_proof")
        not in SOLVER_LIMITS.allowed_hypothesis_proof_models
    ):
        raise ValueError(
            f"Invalid AI model for hypothesis proof. Allowed models: {SOLVER_LIMITS.allowed_hypothesis_proof_models}"
        )

    if kwargs.get("ai_for_final_proof") not in SOLVER_LIMITS.allowed_final_proof_models:
        raise ValueError(
            f"Invalid AI model for final proof. Allowed models: {SOLVER_LIMITS.allowed_final_proof_models}"
        )

    # Special warning for mocked models
    if kwargs.get("ai_for_hypotheses_generation") in [AIForHypothesesProof.OPENAI_O1]:
        logger.warning("o1 is currently only mocked.")


def get_solver_configs(kwargs) -> dict:
    deepseek_url = os.getenv("DEEPSEEK_URL")

    # Create config object to store all variables
    config = {
        'name': kwargs["name"],
        'hypotheses': kwargs["hypotheses"], 
        'code_env_0': kwargs["code_for_env_0"],
        'goal': kwargs["goal"],
        'max_iteration_hypotheses_proof': kwargs["max_iteration_hypotheses_proof"],
        'max_correction_iteration_hypotheses_proof': kwargs["max_correction_iteration_hypotheses_proof"],
        'max_iteration_final_proof': kwargs["max_iteration_final_proof"], 
        'max_correction_iteration_final_proof': kwargs["max_correction_iteration_final_proof"],
        'verbose': kwargs["verbose"]
    }

    # Initialize lean client and proof state
    config['lean_client'] = LeanServer(config['code_env_0'])
    

    # Initialize hypothesis search client based on parameter
    ai_for_hypotheses_generation = kwargs["ai_for_hypotheses_generation"]
    if ai_for_hypotheses_generation == AIForHypothesesProof.CLAUDE:
        config['api_client_for_hypothesis_search'] = ClaudeClient()
    elif ai_for_hypotheses_generation == AIForHypothesesProof.DEEPSEEK_1_5:
        config['api_client_for_hypothesis_search'] = DeepSeekClient(base_url=deepseek_url)
    elif ai_for_hypotheses_generation == AIForHypothesesProof.GEMINI:
        config['api_client_for_hypothesis_search'] = GeminiClient()
    elif ai_for_hypotheses_generation == AIForHypothesesProof.DEEPSEEK_R1:
        config['api_client_for_hypothesis_search'] = DeepSeekOfficialClient()
    elif ai_for_hypotheses_generation == AIForHypothesesProof.MOCK:
        config['api_client_for_hypothesis_search'] = MockClient([api_output_1])
    elif ai_for_hypotheses_generation == AIForHypothesesProof.OPENAI_O1:
        config['api_client_for_hypothesis_search'] = OpenAIClient("o1")
    elif ai_for_hypotheses_generation == AIForHypothesesProof.OPENAI_4O:
        config['api_client_for_hypothesis_search'] = OpenAIClient("gpt-4o")
    else:
        raise ValueError(f"Unknown AI client type: {ai_for_hypotheses_generation}")

    # Initialize proof client based on parameter
    ai_for_hyptheses_proof = kwargs["ai_for_hyptheses_proof"]
    if ai_for_hyptheses_proof == AIForHypothesesProof.CLAUDE:
        config['api_client_for_proofing'] = [ClaudeClient()]
    elif ai_for_hyptheses_proof == AIForHypothesesProof.GEMINI:
        config['api_client_for_proofing'] = [GeminiClient()]
    elif ai_for_hyptheses_proof == AIForHypothesesProof.DEEPSEEK_R1:
        config['api_client_for_proofing'] = [DeepSeekOfficialClient()]
    elif ai_for_hyptheses_proof == AIForHypothesesProof.DEEPSEEK_1_5:
        config['api_client_for_proofing'] = [DeepSeekClient(base_url=deepseek_url)]
    elif ai_for_hyptheses_proof == AIForHypothesesProof.OPENAI_O1:
        config['api_client_for_proofing'] = [OpenAIClient("o1")]
    elif ai_for_hyptheses_proof == AIForHypothesesProof.OPENAI_4O:
        config['api_client_for_proofing'] = [OpenAIClient("gpt-4o")]
    else:
        raise ValueError(f"Unknown AI client type: {ai_for_hyptheses_proof}")

    # Initialize final proof client
    ai_for_final_proof = kwargs["ai_for_final_proof"]
    if ai_for_final_proof == AIForHypothesesProof.CLAUDE:
        config['final_proof_client'] = ClaudeClient()
    elif ai_for_final_proof == AIForHypothesesProof.GEMINI:
        config['final_proof_client'] = GeminiClient()
    elif ai_for_final_proof == AIForHypothesesProof.DEEPSEEK_R1:
        config['final_proof_client'] = DeepSeekOfficialClient()
    elif ai_for_final_proof == AIForHypothesesProof.DEEPSEEK_1_5:
        config['final_proof_client'] = DeepSeekClient(base_url=deepseek_url)
    elif ai_for_final_proof == AIForHypothesesProof.OPENAI_O1:
        config['final_proof_client'] = OpenAIClient("o1")
    elif ai_for_final_proof == AIForHypothesesProof.OPENAI_4O:
        config['final_proof_client'] = OpenAIClient("gpt-4o")
    else:
        raise ValueError(f"Unknown AI client type: {ai_for_final_proof}")

    return config