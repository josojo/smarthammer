"""Client module for interacting with OPEN AI via openai's API."""

import os
from openai import OpenAI
from hammer.api.base_client import AIClient
import logging
import time

logger = logging.getLogger(__name__)


class Client(AIClient):
    """Client wrapper for OpenAI API interactions."""

    def __init__(self, model: str = "o1-mini"):
        self.client = OpenAI(
            base_url="https://openrouter.ai/api/v1",
            api_key=os.getenv("OPENROUTER_API_KEY"),
        )
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
            logger.debug(
                f"Sending message to {self.model}:\n \033[33m {message} \n \n \033[0m"
            )

        max_retries = 3
        initial_retry_delay = 2
        max_retry_delay = 16
        retry_delay = initial_retry_delay

        for attempt in range(max_retries):
            try:
                result = self.client.chat.completions.create(
                    messages=[
                        {
                            "role": "user",
                            "content": message,
                        }
                    ],
                    model=self.model,
                )
                if result is None or not result.choices:
                    raise ValueError("Received an invalid response from the API")

                content = result.choices[0].message.content
                if verbose:
                    logger.debug(
                        f"Received response from DeepSeek R1:\n \033[33m {content}\033[0m"
                    )
                return content

            except Exception as e:
                logger.warning(
                    f"Error during API call (attempt {attempt + 1}/{max_retries}): {str(e)}"
                )

                if attempt == max_retries - 1:
                    logger.error(f"All retries failed: {str(e)}")
                    raise

            if attempt < max_retries - 1:
                sleep_time = min(retry_delay, max_retry_delay)
                if verbose:
                    logger.debug(f"Retrying in {sleep_time} seconds...")
                time.sleep(sleep_time)
                retry_delay *= 2
