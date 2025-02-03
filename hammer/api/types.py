from enum import Enum


class AIForHypothesesProof(Enum):
    CLAUDE = "Claude"
    OPENAI_O1 = "OpenAI(o1)"
    OPENAI_4O = "OpenAI(4o)"
    DEEPSEEK_1_5 = "DeepSeekProver1.5"
    GEMINI = "Gemini-Flash-Thinking"
    DEEPSEEK_R1 = "DeepSeekR1"
    MOCK = "Mock o1"
    OPENAI_O3_mini = "OpenAI(o3-mini)"
    OPENAI_O1_mini = "OpenAI(o1-mini)"
    DEEPSEEK_R1_LAMBDA_DESTILLED = "DeepSeekR1LambdaDestilled"
