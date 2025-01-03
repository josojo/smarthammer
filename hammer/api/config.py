from pydantic import BaseModel
from typing import List
from hammer.api.types import AIForHypothesesProof


class SolverLimits(BaseModel):
    # Iteration limits
    max_iteration_hypotheses_proof: int = 10
    max_correction_iteration_hypotheses_proof: int = 10
    max_iteration_final_proof: int = 10
    max_correction_iteration_final_proof: int = 10

    # Allowed AI configurations
    allowed_hypothesis_generation_models: List[AIForHypothesesProof] = [
        AIForHypothesesProof.CLAUDE,
        AIForHypothesesProof.DEEPSEEK_1_5,
        AIForHypothesesProof.OPENAI_O1,  # Currently mocked
        AIForHypothesesProof.OPENAI_4O,
    ]

    allowed_hypothesis_proof_models: List[AIForHypothesesProof] = [
        AIForHypothesesProof.CLAUDE,
        AIForHypothesesProof.DEEPSEEK_1_5,
    ]

    allowed_final_proof_models: List[AIForHypothesesProof] = [
        AIForHypothesesProof.CLAUDE,
        AIForHypothesesProof.DEEPSEEK_1_5,
    ]


# Global configuration instance
SOLVER_LIMITS = SolverLimits()
