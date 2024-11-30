"""Client module for interacting with OPEN AI via openai's API."""

import os
from openai import OpenAI
import json


class Client:
    """Client wrapper for Anthropic's Claude API interactions."""

    def __init__(self):
        self.client = OpenAI(
            organization=os.getenv("OPENAI_ORG_ID"),
            project=os.getenv("OPENAI_PROJECT_ID"),
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
        content = result.choices[0].message.content
        if verbose:
            print(f"Received response from OpenAI: {content}")
        return content
