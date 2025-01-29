from enum import Enum


class AIForHypothesesProof(Enum):
    CLAUDE = "Claude"
    OPENAI_O1 = "OpenAI(o1)"
    OPENAI_4O = "OpenAI(4o)"
    DEEPSEEK_1_5 = "DeepSeek1.5"
    GEMINI = "Gemini"
    DEEPSEEK_R1 = "DeepSeekR1"
    MOCK = "Mock o1"
