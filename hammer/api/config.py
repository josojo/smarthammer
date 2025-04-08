from pydantic import BaseModel
from typing import List
import os
from hammer.api.types import AIForHypothesesProof
from hammer.api.openrouter.client import Client as OpenRouterClient
from hammer.api.deepseek.client import Client as DeepSeekClient
from hammer.api.openai.client import Client as OpenAIClient
from hammer.api.mock.mock_client import Client as MockClient
from hammer.api.gemini.client import Client as GeminiClient
from hammer.api.lean_search.client import Client as LeanSearchClient
from hammer.lean.cache import LeanServerCache

api_output_1 = """
  Natural language proof:
We want to show that the greatest common divisor of 21n + 4 and 14n + 3 is 1. We can use the Euclidean algorithm.  First, let's try to eliminate the 'n' term. Multiply the second term by 3 and the first term by 2 to get 42n + 8 and 42n+ 9. Subtract the first term from the second and we get 1. Since 1 divides any number we can conclude that the gcd must be 1.

Lean4 hypotheses:
```lean
lemma lem1 : 3 * (14*n + 3) = 42 * n + 9
```
```lean
lemma lem2 : 2 * (21*n + 4) = 42 * n + 8
```
```lean
lemma lem3 : (42*n + 9) - (42*n + 8) = 1
```
```lean
lemma lem5 : Nat.gcd (21*n + 4) (14*n + 3) = Nat.gcd (21*n + 4) (1)
```
```lean
lemma lem6 : Nat.gcd (a : N) 1 = 1
```
 """


class SolverLimits(BaseModel):
    # Iteration limits
    max_iteration_hypotheses_proof: int = 6
    max_correction_iteration_hypotheses_proof: int = 6
    max_iteration_final_proof: int = 6
    max_correction_iteration_final_proof: int = 6
    max_number_of_proving_cycles: int = 3

    # Allowed AI configurations
    allowed_hypothesis_generation_models: List[AIForHypothesesProof] = [
        # AIForHypothesesProof.MOCK,
        AIForHypothesesProof.GEMINI_2,
        AIForHypothesesProof.GEMINI_2_PAID,
        # AIForHypothesesProof.CLAUDE_37_THINKING,
        # AIForHypothesesProof.GEMINI,
        # AIForHypothesesProof.CLAUDE,
        # AIForHypothesesProof.DEEPSEEK_1_5,
        # AIForHypothesesProof.DEEPSEEK_R1,
        # AIForHypothesesProof.OPENAI_4O,
        # AIForHypothesesProof.OPENAI_O3_mini,
        # AIForHypothesesProof.OPENAI_O3_mini,
        # AIForHypothesesProof.OPENAI_O1,
    ]

    allowed_hypothesis_proof_models: List[AIForHypothesesProof] = [
        # AIForHypothesesProof.GEMINI_20,
        AIForHypothesesProof.GEMINI_2,
        AIForHypothesesProof.GEMINI_2_PAID,
        # AIForHypothesesProof.CLAUDE_37_THINKING,
        # # AIForHypothesesProof.OPENAI_O3_mini,
        # AIForHypothesesProof.DEEPSEEK_V3,
        # AIForHypothesesProof.DEEPSEEK_R1,
        # AIForHypothesesProof.DEEPSEEK_1_5,
        # AIForHypothesesProof.CLAUDE,
        # AIForHypothesesProof.DEEPSEEK_R1_LAMBDA_DESTILLED,
        # AIForHypothesesProof.OPENAI_O3_mini,
        # AIForHypothesesProof.OPENAI_O1_mini,
    ]

    allowed_final_proof_models: List[AIForHypothesesProof] = [
        # AIForHypothesesProof.GEMINI_20,
        AIForHypothesesProof.GEMINI_2,
        AIForHypothesesProof.GEMINI_2_PAID,
        # AIForHypothesesProof.CLAUDE_37_THINKING,
        # AIForHypothesesProof.DEEPSEEK_R1,
        # AIForHypothesesProof.OPENAI_O3_mini,
        # # AIForHypothesesProof.DEEPSEEK_1_5,
        # AIForHypothesesProof.CLAUDE,
        # AIForHypothesesProof.GEMINI,
        # # AIForHypothesesProof.OPENAI_O3_mini,
        # # AIForHypothesesProof.OPENAI_O1,
        # AIForHypothesesProof.DEEPSEEK_R1_LAMBDA_DESTILLED,
        # AIForHypothesesProof.OPENAI_O1_mini,
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

    if not all(
        model in SOLVER_LIMITS.allowed_hypothesis_proof_models
        for model in kwargs.get("ai_for_hypotheses_proof", [])
    ):
        raise ValueError(
            f"Invalid AI model for hypothesis proof. Allowed models: {SOLVER_LIMITS.allowed_hypothesis_proof_models}"
        )

    if kwargs.get("ai_for_final_proof") not in SOLVER_LIMITS.allowed_final_proof_models:
        raise ValueError(
            f"Invalid AI model for final proof. Allowed models: {SOLVER_LIMITS.allowed_final_proof_models}"
        )

    if (
        kwargs.get("number_of_proving_cycles")
        > SOLVER_LIMITS.max_number_of_proving_cycles
    ):
        raise ValueError(
            f"Invalid AI model for number_of_proving_cycles. Allowed max number: {SOLVER_LIMITS.max_number_of_proving_cycles}"
        )

    # Special warning for mocked models
    if kwargs.get("ai_for_hypotheses_generation") in [AIForHypothesesProof.OPENAI_O1]:
        logger.warning("o1 is currently only mocked.")


def return_ai_client(ai_name):
    if ai_name == AIForHypothesesProof.CLAUDE:
        return OpenRouterClient("anthropic/claude-3.5-sonnet")
    elif ai_name == AIForHypothesesProof.DEEPSEEK_1_5:
        deepseek_url = os.getenv("DEEPSEEK_URL")
        return DeepSeekClient(base_url=deepseek_url)
    elif ai_name == AIForHypothesesProof.GEMINI:
        return OpenRouterClient("google/gemini-2.0-flash-001")
    elif ai_name == AIForHypothesesProof.CLAUDE_37_THINKING:
        return OpenRouterClient("anthropic/claude-3.7-sonnet:thinking")
    elif ai_name == AIForHypothesesProof.GEMINI_2:
        return GeminiClient()
    elif ai_name == AIForHypothesesProof.GEMINI_2_PAID:
        return GeminiClient("gemini-2.5-pro-preview-03-25")
    elif ai_name == AIForHypothesesProof.GEMINI_20:
        return GeminiClient("gemini-2.0-flash")
    elif ai_name == AIForHypothesesProof.DEEPSEEK_R1:
        return OpenRouterClient("deepseek/deepseek-r1-zero:free")
    elif ai_name == AIForHypothesesProof.DEEPSEEK_V3:
        return OpenRouterClient("deepseek/deepseek-chat-v3-0324:free")
    elif ai_name == AIForHypothesesProof.MOCK:
        return MockClient([api_output_1])
    elif ai_name == AIForHypothesesProof.OPENAI_O1:
        return OpenAIClient("o1")
    elif ai_name == AIForHypothesesProof.OPENAI_4O:
        return OpenRouterClient("openai/gpt-4o-2024-11-20")
    elif ai_name == AIForHypothesesProof.OPENAI_O3_mini:
        return OpenRouterClient("o3-mini")
    elif ai_name == AIForHypothesesProof.OPENAI_O1_mini:
        return OpenRouterClient("o1-mini")
    elif ai_name == AIForHypothesesProof.DEEPSEEK_R1_LAMBDA_DESTILLED:
        return OpenRouterClient("deepseek/deepseek-r1-distill-llama-70b")
    else:
        raise ValueError(f"Unknown AI client type: {ai_name}")


def get_solver_configs(kwargs) -> dict:

    # Create config object to store all variables
    config = {
        "name": kwargs["name"],
        "hypotheses": kwargs["hypotheses"],
        "code_env_0": kwargs["code_for_env_0"],
        "goal": kwargs["goal"],
        "max_iteration_hypotheses_proof": kwargs["max_iteration_hypotheses_proof"],
        "max_correction_iteration_hypotheses_proof": kwargs[
            "max_correction_iteration_hypotheses_proof"
        ],
        "max_iteration_final_proof": kwargs["max_iteration_final_proof"],
        "max_correction_iteration_final_proof": kwargs[
            "max_correction_iteration_final_proof"
        ],
        "verbose": kwargs["verbose"],
        "number_of_proving_cycles": kwargs["number_of_proving_cycles"],
    }

    # Get LeanServer from cache
    lean_cache = LeanServerCache.get_instance()
    config["lean_client"] = lean_cache.get_server(kwargs["code_env"])
    # Initialize moogle client
    config["library_search_client"] = LeanSearchClient()

    # Initialize AI clients
    config["api_client_for_hypothesis_search"] = return_ai_client(
        kwargs["ai_for_hypotheses_generation"]
    )
    config["hypothesis_proof_client"] = [
        return_ai_client(ai_type) for ai_type in kwargs["ai_for_hypotheses_proof"]
    ]
    config["final_proof_client"] = return_ai_client(kwargs["ai_for_final_proof"])

    return config
