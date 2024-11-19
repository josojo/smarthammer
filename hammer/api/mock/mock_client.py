"""Client module for interacting with Claude AI via Anthropic's API."""
import os
import anthropic


class Client:
    """Client wrapper for Anthropic's Claude API interactions."""

    def __init__(self, return_outputs=[]):
        self.client = anthropic.Anthropic(
            api_key=os.getenv("CLAUDEAPIKEY"),
        )
        self.call_count = 0
        self.return_outputs = return_outputs

    def send(self, message, verbose=False):
        """Send a message to Claude and return its response."""
        if verbose:
            print(f"Sending message to Claude: {message}")
        output = self.return_outputs[self.call_count]
        self.call_count += 1

        if verbose:
            print(f"Received response from Claude: {output}")
        return output
