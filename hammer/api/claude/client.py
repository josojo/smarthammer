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
        result = self.client.messages.create(
            model="claude-3-5-sonnet-20241022",
            max_tokens=1024,
            messages=[{"role": "user", "content": message}],
        )
        output = result.content[0].text
        if verbose:
            print(f"Received response from Claude: {output}")
        return output
