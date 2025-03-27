"""Client module for interacting with DeepSeek AI via HTTP API."""

import os
import time
import requests
import logging
import json
import brotli  # Add this import for Brotli decompression
from hammer.api.base_client import AIClient
from requests.exceptions import Timeout, RequestException
from urllib3.exceptions import ProtocolError
from requests.exceptions import ConnectionError
from rq.timeouts import JobTimeoutException

logger = logging.getLogger(__name__)


class Client(AIClient):
    """Client wrapper for DeepSeek API interactions."""

    def __init__(self, base_url=None):
        self.base_url = base_url or "https://www.moogle.ai"
        self.endpoint = f"{self.base_url}/api/search"
        self._name = "DeepSeek"
        self.timeout = 300  # Increased timeout to 5 minutes
        self.max_retries = 3  # Reduced retries to avoid long waiting times
        self.initial_retry_delay = 2
        self.max_retry_delay = 16
        self.chunk_size = 8192  # Add chunk size for streaming responses
        self.session = requests.Session()  # Create a session

    def send(self, message, verbose=False):
        """Send a message to DeepSeek and return its response."""
        # Return empty JSON array as string
        # return "[]"
        if verbose:
            logger.debug(
                f"Sending message to Moogle:\n \033[33m {message} \n \n \033[0m"
            )

        retry_delay = self.initial_retry_delay
        last_exception = None
        output = ""  # Initialize output variable

        for attempt in range(self.max_retries):
            try:
                headers = {
                    "Content-Type": "application/json",
                    "Accept": "*/*",
                    "Accept-Encoding": "gzip, deflate, br",
                    "Accept-Language": "de-DE,de;q=0.9,en-US;q=0.8,en;q=0.7",
                    "Origin": "https://www.moogle.ai",
                    "Referer": "https://www.moogle.ai/",
                    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
                }

                payload = [{"isFind": False, "contents": message}]

                if verbose:
                    logger.debug(f"Sending request with payload: {payload}")

                # First make a GET request to get any necessary cookies
                self.session.get(self.base_url)

                # Then make the actual API request
                response = self.session.post(
                    self.endpoint,
                    headers=headers,
                    json=payload,
                    timeout=self.timeout,
                    stream=False,
                )
                # Add detailed response logging
                logger.info(f"Response status: {response.status_code}")
                logger.info(f"Response headers: {dict(response.headers)}")
                logger.info(f"Response content length: {len(response.text)}")
                logger.info(f"Response content first 100 chars: '{response.text[:100]}'")
                
                # Ensure response is valid before processing
                response.raise_for_status()

                # Check if response is compressed with Brotli
                if response.headers.get('Content-Encoding') == 'br':
                    # Check if the content already looks like JSON (not actually compressed)
                    if response.text.strip().startswith('{'):
                        logger.info("Content appears to be JSON despite br Content-Encoding header")
                        response_text = response.text
                    else:
                        # Try to decompress Brotli content
                        try:
                            decompressed_content = brotli.decompress(response.content)
                            response_text = decompressed_content.decode('utf-8')
                            logger.info(f"Successfully decompressed Brotli content, length: {len(response_text)}")
                        except Exception as e:
                            logger.error(f"Failed to decompress Brotli content: {str(e)}")
                            # If decompression fails but content looks like JSON, try using it directly
                            if response.text.strip().startswith('{'):
                                logger.info("Using raw content as JSON despite decompression failure")
                                response_text = response.text
                            else:
                                return "[]"  # Return empty array as fallback
                else:
                    response_text = response.text

                # Check if response is empty before trying to parse JSON
                if not response_text.strip():
                    logger.error("Received empty response from Moogle API")
                    return "[]"  # Return empty array as string when no data
                
                try:
                    response_json = json.loads(response_text)
                    # Extract first entry from data array and get declarationName and declarationCode
                    if response_json.get("data") and len(response_json["data"]) > 0:
                        first_entries = response_json["data"][1:50]
                        result = []
                        for first_entry in first_entries:
                            result.append(
                                {
                                    "name": first_entry.get("declarationName"),
                                    "code": (
                                        first_entry.get("declarationCode").split(
                                            ":= by"
                                        )[0]
                                        if first_entry.get("declarationCode")
                                        else ""
                                    ),
                                }
                            )
                        logger.debug(f"Extracted result: {result}")
                        output = json.dumps(result)
                    else:
                        logger.debug("No data found in response")
                        output = "[]"  # Return empty array as string when no data
                except json.JSONDecodeError as e:
                    print(f"Failed to parse response as JSON: {response_text}")
                    print(f"JSON parse error: {str(e)}")
                    raise  # Re-raise the exception to be caught by outer try-except

                # Log the full response for debugging
                if not response.ok:
                    logger.error(f"Response status: {response.status_code}")
                    logger.error(f"Response content: {response_text}")

                if verbose:
                    logger.debug(
                        f"Received response from moogle:\n \033[33m {output}\033[0m"
                    )
                return output

            except (Timeout, ConnectionError, ProtocolError, JobTimeoutException) as e:
                last_exception = e
                error_msg = f"Moogle API connection error (attempt {attempt + 1}/{self.max_retries}): {str(e)}"
                logger.warning(error_msg)

                if attempt == self.max_retries - 1:
                    logger.error(f"All retries failed for Moogle API: {str(e)}")
                    raise ConnectionError(
                        f"Failed to connect to Moogle API after {self.max_retries} attempts"
                    ) from e

            except (RequestException, json.JSONDecodeError) as e:
                last_exception = e
                logger.error(
                    f"Moogle API error (attempt {attempt + 1}/{self.max_retries}): {str(last_exception)}"
                )
                # Add more detailed error logging
                if isinstance(e, json.JSONDecodeError):
                    logger.error(f"JSON decode error position: {e.pos}")
                    logger.error(f"Response content type: {type(response_text)}")
                    logger.error(f"Response content length: {len(response_text)}")
                    logger.error(f"Response first 100 chars: '{response_text[:100]}'")
                    logger.error(f"Response status code: {response.status_code}")
                
                error_msg = f"Moogle API error (attempt {attempt + 1}/{self.max_retries}): {str(e)}"
                logger.warning(error_msg)

                if attempt == self.max_retries - 1:
                    logger.error(f"All retries failed for Moogle API: {str(e)}")
                    raise

            except Exception as e:
                last_exception = e
                logger.error(
                    f"Unexpected error (attempt {attempt + 1}/{self.max_retries}): {str(e)}"
                )
                error_msg = f"Unexpected error (attempt {attempt + 1}/{self.max_retries}): {str(e)}"
                logger.warning(error_msg)

                if attempt == self.max_retries - 1:
                    logger.error(
                        f"All retries failed due to an unexpected error: {str(e)}"
                    )
                    raise

            if attempt < self.max_retries - 1:
                sleep_time = min(retry_delay, self.max_retry_delay)
                if verbose:
                    logger.debug(f"Retrying in {sleep_time} seconds...")
                time.sleep(sleep_time)
                retry_delay *= 2
        return output
