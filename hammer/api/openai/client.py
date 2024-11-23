"""Client module for interacting with OPEN AI via openai's API."""
from openai import OpenAI


class Client:
    """Client wrapper for Anthropic's Claude API interactions."""

    def __init__(self):
        self.client = OpenAI(
            organization="Personal",
            project="Default project",
        )

    def send(self, message, verbose=False):
        """Send a message to Open ai and return its response."""
        if verbose:
            print(f"Sending message to Open ai: {message}")
        result = self.client.chat.completions.create(
            messages=[
                {
                    "role": "user",
                    "content": message,
                }
            ],
            model="gpt-4o-mini",
        )
        output = result.content[0].text
        if verbose:
            print(f"Received response from OpenAI: {output}")
        return output
