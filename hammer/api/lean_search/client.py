"""Client module for interacting with Lean Search via HTTP API."""

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
    """Client wrapper for Lean Search API interactions."""

    def __init__(self, base_url=None):
        self.base_url = base_url or "https://leansearch.net"
        self.endpoint = f"{self.base_url}/search"
        self._name = "LeanSearch"
        self.timeout = 60
        self.max_retries = 3
        self.initial_retry_delay = 2
        self.max_retry_delay = 16
        self.session = requests.Session()

    def send(self, query, num_results=10, verbose=False):
        """Send a search query to Lean Search and return its response.

        Args:
            query: String containing the search query
            num_results: Number of results to return (default: 1)
            verbose: Whether to log debug information
        """
        if verbose:
            logger.debug(
                f"Sending query to Lean Search:\n \033[33m {query} \n \n \033[0m"
            )

        retry_delay = self.initial_retry_delay
        last_exception = None
        output = "[]"  # Default empty response

        for attempt in range(self.max_retries):
            try:
                headers = {
                    "Content-Type": "application/json",
                    "Accept": "*/*",
                    "Origin": "https://leansearch.net",
                    "Referer": "https://leansearch.net/",
                }

                payload = {"query": [query], "num_results": str(num_results)}

                if verbose:
                    logger.debug(f"Sending request with payload: {payload}")

                response = self.session.post(
                    self.endpoint, headers=headers, json=payload, timeout=self.timeout
                )

                response.raise_for_status()
                response_text = response.text

                if not response_text.strip():
                    logger.error("Received empty response from Lean Search API")
                    return "[]"

                try:
                    response_json = json.loads(response_text)
                    if response_json and len(response_json) > 0:
                        # Handle the double-nested array structure
                        filtered_results = []
                        # Get the inner array
                        inner_array = (
                            response_json[0] if isinstance(response_json, list) else []
                        )

                        for item in inner_array:
                            if isinstance(item, dict) and "result" in item:
                                result = item["result"]
                                filtered_result = {
                                    "module_name": result.get("module_name"),
                                    "kind": result.get("kind"),
                                    "name": result.get("name"),
                                    "signature": result.get("signature"),
                                }
                                filtered_results.append(filtered_result)
                        output = json.dumps(filtered_results)
                    else:
                        logger.debug("No results found in response")
                        output = "[]"
                except (json.JSONDecodeError, AttributeError, TypeError) as e:
                    logger.error(f"Failed to process response: {response_text}")
                    logger.error(f"Error details: {str(e)}")
                    raise

                if verbose:
                    logger.debug(
                        f"Received response from Lean Search:\n \033[33m {output}\033[0m"
                    )
                return output

            except (Timeout, ConnectionError, ProtocolError, JobTimeoutException) as e:
                last_exception = e
                error_msg = f"Lean Search API connection error (attempt {attempt + 1}/{self.max_retries}): {str(e)}"
                logger.warning(error_msg)

                if attempt == self.max_retries - 1:
                    logger.error(f"All retries failed for Lean Search API: {str(e)}")
                    raise ConnectionError(
                        f"Failed to connect to Lean Search API after {self.max_retries} attempts"
                    ) from e

            except Exception as e:
                last_exception = e
                logger.error(
                    f"Unexpected error (attempt {attempt + 1}/{self.max_retries}): {str(e)}"
                )

                if attempt == self.max_retries - 1:
                    logger.error(f"All retries failed: {str(e)}")
                    raise

            if attempt < self.max_retries - 1:
                sleep_time = min(retry_delay, self.max_retry_delay)
                if verbose:
                    logger.debug(f"Retrying in {sleep_time} seconds...")
                time.sleep(sleep_time)
                retry_delay *= 2

        return output
