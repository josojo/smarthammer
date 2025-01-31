"""Client module for interacting with OPEN AI via openai's API."""

import os
from openai import OpenAI
import json
from hammer.api.base_client import AIClient
import logging

logger = logging.getLogger(__name__)


class Client(AIClient):
    """Client wrapper for OpenAI API interactions."""

    def __init__(self, model: str = "o1-mini"):
        self.client = OpenAI(
            organization=os.getenv("OPENAI_ORG_ID"),
            project=os.getenv("OPENAI_PROJECT_ID"),
        )
        self._name = "OpenAI"
        self.model = model

    def send(self, message: str, verbose: bool = False) -> str:
        """Send a message to OpenAI and return its response.

        Args:
            message: The message to send to the AI
            verbose: Whether to log debug information

        Returns:
            str: The AI's response
        """
        if verbose:
            logger.debug(f"Sending message to {self.model}: {message}")
        result = self.client.chat.completions.create(
            messages=[
                {
                    "role": "user",
                    "content": message,
                }
            ],
            model=self.model,
        )
        content = result.choices[0].message.content
        if verbose:
            logger.debug(f"Received response from {self.model}: {content}")
        return content
