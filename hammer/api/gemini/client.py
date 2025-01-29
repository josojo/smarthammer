"""Client module for interacting with OPEN AI via openai's API."""

import os
from hammer.api.base_client import AIClient
from google import genai
import logging

logger = logging.getLogger(__name__)

class Client(AIClient):
    """Client wrapper for OpenAI API interactions."""

    def __init__(self, model: str = "o1-mini"):
        self.client = genai.Client(api_key=os.getenv('GEMINI_API_KEY'))
        self._name = "GEMINI"
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
            logger.debug(f"Sending message to Gemini:\n \033[33m {message} \n \n \033[0m")

        result = self.client.models.generate_content(
            model='gemini-1.5-flash', contents=message
        )
        content = result.candidates[0].content.parts[0].text
        if verbose:
            logger.debug(
                        f"Received response from GEMINI:\n \033[33m {content}\033[0m"
                    )
        return content
