"""Client module for interacting with DeepSeek AI via HTTP API."""

import os
import time
import requests
import logging
import json
from hammer.api.base_client import AIClient
from requests.exceptions import Timeout, RequestException
from urllib3.exceptions import ProtocolError
from requests.exceptions import ConnectionError
from rq.timeouts import JobTimeoutException

logger = logging.getLogger(__name__)


class Client(AIClient):
    """Client wrapper for DeepSeek API interactions."""

    def __init__(self, base_url=None):
        self.base_url = base_url or "http://194.26.196.173:21919"
        self.endpoint = f"{self.base_url}/generate"
        self._name = "DeepSeek"
        self.timeout = 300  # Increased timeout to 5 minutes
        self.max_retries = 3  # Reduced retries to avoid long waiting times
        self.initial_retry_delay = 2
        self.max_retry_delay = 16
        self.chunk_size = 8192  # Add chunk size for streaming responses

    def send(self, message, verbose=False):
        """Send a message to DeepSeek and return its response."""
        if verbose:
            logger.debug(
                f"Sending message to DeepSeek:\n \033[33m {message} \n \n \033[0m"
            )

        retry_delay = self.initial_retry_delay
        last_exception = None

        for attempt in range(self.max_retries):
            try:
                response = requests.post(
                    self.endpoint,
                    headers={
                        "Content-Type": "application/json",
                        "Accept": "application/json",
                        "Connection": "close"  # Prevent keep-alive connections
                    },
                    json={"prompt": message},
                    timeout=self.timeout,
                    stream=True  # Enable streaming response
                )
                response.raise_for_status()

                # Read response in chunks
                content = ""
                for chunk in response.iter_content(chunk_size=self.chunk_size, decode_unicode=True):
                    if chunk:
                        content += chunk.decode('utf-8') if isinstance(chunk, bytes) else chunk

                result = json.loads(content)
                output = result["generated_text"]

                if verbose:
                    logger.debug(
                        f"Received response from DeepSeek:\n \033[33m {output}\033[0m"
                    )
                return output

            except (Timeout, ConnectionError, ProtocolError, JobTimeoutException) as e:
                last_exception = e
                error_msg = f"DeepSeek API connection error (attempt {attempt + 1}/{self.max_retries}): {str(e)}"
                logger.warning(error_msg)
                
                if attempt == self.max_retries - 1:
                    logger.error(f"All retries failed for DeepSeek API: {str(e)}")
                    raise ConnectionError(f"Failed to connect to DeepSeek API after {self.max_retries} attempts") from e

            except (RequestException, json.JSONDecodeError) as e:
                last_exception = e
                logger.error(f"DeepSeek API error (attempt {attempt + 1}/{self.max_retries}): {str(last_exception)}")
                error_msg = f"DeepSeek API error (attempt {attempt + 1}/{self.max_retries}): {str(e)}"
                logger.warning(error_msg)
                
                if attempt == self.max_retries - 1:
                    logger.error(f"All retries failed for DeepSeek API: {str(e)}")
                    raise

            except Exception as e:
                last_exception = e
                logger.error(f"Unexpected error (attempt {attempt + 1}/{self.max_retries}): {str(e)}")
                error_msg = f"Unexpected error (attempt {attempt + 1}/{self.max_retries}): {str(e)}"
                logger.warning(error_msg)
                
                if attempt == self.max_retries - 1:
                    logger.error(f"All retries failed due to an unexpected error: {str(e)}")
                    raise

            if attempt < self.max_retries - 1:
                sleep_time = min(retry_delay, self.max_retry_delay)
                if verbose:
                    logger.debug(f"Retrying in {sleep_time} seconds...")
                time.sleep(sleep_time)
                retry_delay *= 2
