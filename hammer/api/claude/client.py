"""Client module for interacting with Claude AI via Anthropic's API."""

import os
import time
import anthropic
import logging
from hammer.api.base_client import AIClient

logger = logging.getLogger(__name__)


class Client(AIClient):
    """Client wrapper for Anthropic's Claude API interactions."""

    def __init__(self):
        self.client = anthropic.Anthropic(
            api_key=os.getenv("CLAUDEAPIKEY"),
        )
        self._name = "Claude"

    def send(self, message: str, verbose: bool = False) -> str:
        """Send a message to Claude and return its response."""
        if verbose:
            logger.debug(
                f"Sending message to Claude:\n \033[33m {message} \n \n \033[0m"
            )

        max_retries = 3
        retry_delay = 1  # seconds

        for attempt in range(max_retries):
            try:
                result = self.client.messages.create(
                    model="claude-3-5-sonnet-20241022",
                    max_tokens=1024,
                    messages=[{"role": "user", "content": message}],
                )
                output = result.content[0].text
                if verbose:
                    logger.debug(
                        f"Received response from Claude:\n \033[33m {output}\033[0m"
                    )
                return output

            except anthropic.InternalServerError as e:
                if attempt == max_retries - 1:  # Last attempt
                    raise  # Re-raise the exception if all retries failed
                if verbose:
                    logger.debug(
                        f"Got server error, retrying in {retry_delay} seconds..."
                    )
                time.sleep(retry_delay)
                retry_delay *= 2  # Exponential backoff
