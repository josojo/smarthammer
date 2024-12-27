"""Client module for interacting with DeepSeek AI via HTTP API."""

import os
import time
import requests
import logging
import json
from hammer.api.base_client import AIClient
from requests.exceptions import Timeout, RequestException

logger = logging.getLogger(__name__)


class Client(AIClient):
    """Client wrapper for DeepSeek API interactions."""

    def __init__(self, base_url=None):
        self.base_url = base_url or "http://194.26.196.173:21919"
        self.endpoint = f"{self.base_url}/generate"
        self._name = "DeepSeek"
        self.timeout = 300  # 5 minutes timeout by default

    @property
    def name(self) -> str:
        return self._name

    def send(self, message, verbose=False):
        """Send a message to DeepSeek and return its response."""
        if verbose:
            logger.debug(
                f"Sending message to DeepSeek:\n \033[33m {message} \n \n \033[0m"
            )

        max_retries = 3
        retry_delay = 1  # seconds

        for attempt in range(max_retries):
            try:
                response = requests.post(
                    self.endpoint,
                    headers={"Content-Type": "application/json"},
                    json={"prompt": message},
                    timeout=self.timeout,
                )
                response.raise_for_status()

                result = response.json()
                output = result["generated_text"]

                if verbose:
                    logger.debug(
                        f"Received response from DeepSeek:\n \033[33m {output}\033[0m"
                    )
                return output

            except Timeout as e:
                error_msg = (
                    f"DeepSeek API request timed out after {self.timeout} seconds"
                )
                logger.error(error_msg)
                if attempt == max_retries - 1:
                    raise TimeoutError(error_msg) from e
                if verbose:
                    logger.debug(f"Timeout error, retrying in {retry_delay} seconds...")
                time.sleep(retry_delay)
                retry_delay *= 2

            except (RequestException, json.JSONDecodeError) as e:
                if attempt == max_retries - 1:  # Last attempt
                    raise  # Re-raise the exception if all retries failed
                if verbose:
                    logger.debug(
                        f"Got server error: {str(e)}, retrying in {retry_delay} seconds..."
                    )
                time.sleep(retry_delay)
                retry_delay *= 2  # Exponential backoff
