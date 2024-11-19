"""Client module for interacting with Claude AI via Anthropic's API."""
import os
import anthropic

class Client:
    """Client wrapper for Anthropic's Claude API interactions."""
    def __init__(self):
        self.client = anthropic.Anthropic(
            api_key=os.getenv("CLAUDEAPIKEY"),
        )

    def send(self, message, verbose=False):
        """Send a message to Claude and return its response."""
        if verbose:
            print(f"Sending message to Claude: {message}")
        # result = self.client.messages.create(
        #     model="claude-3-5-sonnet-20241022",
        #     max_tokens=1024,
        #     messages=[
        #         {"role": "user", "content": message}
        #     ]
        # )
        # output = result.content[0].text
        output = """
Let me help formulate a proof for this GCD theorem.

Natural language proof:
Let's call g = gcd(21n + 4, 14n + 3). If we show that g divides both numbers and their linear combination, we can find g.
If g divides both 21n + 4 and 14n + 3, then it also divides any linear combination of them.
Consider: (21n + 4) - (14n + 3) = 7n + 1
And: 3(14n + 3) - 2(21n + 4) = 42n + 9 - 42n - 8 = 1

Therefore g divides 1, which means g = 1.

Let's break this down into critical Lean4 hypotheses:

```lean
-- if g divides both numbers, it divides their difference
∀ a b g : ℕ, g ∣ a → g ∣ b → g ∣ (a - b)
```

```lean
-- first linear combination equals 7n + 1
(21*n + 4) - (14*n + 3) = 7*n + 1
```

```lean
-- second linear combination equals 1
3*(14*n + 3) - 2*(21*n + 4) = 1
```

```lean
-- if g divides both original numbers, it divides 1
∀ g : ℕ, g ∣ (21*n + 4) → g ∣ (14*n + 3) → g ∣ 1
```

```lean
-- only 1 divides 1 in natural numbers
∀ g : ℕ, g ∣ 1 → g = 1
```

These hypotheses capture the key steps needed to prove that the GCD must be 1."""
        if verbose:
            print(f"Received response from Claude: {output}")
        return output
