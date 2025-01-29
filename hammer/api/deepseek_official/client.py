"""Client module for interacting with OPEN AI via openai's API."""

import os
from openai import OpenAI
from hammer.api.base_client import AIClient
import logging

logger = logging.getLogger(__name__)

class Client(AIClient):
    """Client wrapper for OpenAI API interactions."""

    def __init__(self, model: str = "o1-mini"):
        self.client = OpenAI(api_key=os.getenv("DEEPSEEK_API_KEY"), base_url="https://api.deepseek.com")
        self._name = "DeepSeek R1"
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
            logger.debug(f"Sending message to {self.model}:\n \033[33m {message} \n \n \033[0m")
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
            logger.debug(
                        f"Received response from DeepSeek R1:\n \033[33m {content}\033[0m"
                    ) 
        return content
