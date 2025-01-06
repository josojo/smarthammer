"""Server module for interacting with Lean REPL."""

import json
import os
import pexpect
from dotenv import load_dotenv
import logging
import sys
import signal

logger = logging.getLogger(__name__)


class LeanServer:
    """Server class for managing interactions with a Lean REPL instance."""

    def __init__(self, code_for_env_0="import Mathlib"):
        load_dotenv()
        path_to_repl = os.getenv("REPLPATH")
        if not path_to_repl:
            raise ValueError("REPLPATH environment variable not set in .env file")

        # Strip whitespace and normalize path
        path_to_repl = path_to_repl.strip()
        path_to_repl = os.path.normpath(path_to_repl)

        # Create directory if it doesn't exist
        os.makedirs(path_to_repl, exist_ok=True)

        # Check if the REPL binary exists
        repl_binary = "../../.lake/build/bin/repl"
        full_repl_path = os.path.join(path_to_repl, repl_binary)

        if not os.path.exists(full_repl_path):
            raise FileNotFoundError(f"REPL binary not found at {full_repl_path}")

        # Add more detailed logging before spawning process
        logger.info(
            f"Memory settings - LEAN_MEMORY: {os.getenv('LEAN_MEMORY')}, LAKE_MEMORY: {os.getenv('LAKE_MEMORY')}"
        )
        command = f"/bin/bash -c 'stty -icanon && lake env {repl_binary}'"

        self.proc = pexpect.spawn(
            command,
            cwd=path_to_repl,
            encoding="utf-8",
            echo=False,
            timeout=300,  # Add 5 minute timeout
        )

        # Fix: Create a file-like object that handles encoding
        class EncodedStream:
            def __init__(self, stream):
                self.stream = stream

            def write(self, data):
                if isinstance(data, str):
                    self.stream.write(data.encode("utf-8"))
                else:
                    self.stream.write(data)

            def flush(self):
                self.stream.flush()

        # Use the wrapper for logging
        self.proc.logfile = EncodedStream(sys.stdout.buffer)

        if code_for_env_0:
            self.run_code(code_for_env_0)

    def run_code(self, code, env=None, verbose=False):
        """Execute Lean code in the REPL."""
        if not self.proc.isalive():
            raise Exception("REPL process is not alive")

        if env is not None:
            command = (
                json.dumps(
                    {"cmd": code, "env": env},
                )
                .replace("\\\\", "\\")
                .replace("\\n\\n", "\\n")
            )
        else:
            command = '{ "cmd" : "' + repr(code)[1:-1] + '" }'

        logger.debug(
            f"Sending the following command to the Lean REPL\n \033[35m{command}\033[0m"
        )

        try:
            self.proc.sendline(command)
            self.proc.sendline()

            # Add pattern for error messages
            patterns = [
                r'(?:\{.*"env": \d+\})',
                r">>",
                r"error:.*$",
                pexpect.EOF,
                pexpect.TIMEOUT,
            ]

            index = self.proc.expect(patterns, timeout=300)

            if index == 0 or index == 1:  # Success cases
                output = self.proc.before + (
                    self.proc.match.group() if self.proc.match else ""
                )
                try:
                    jsonText = json.loads(output)
                    logger.debug(f"JSON response: {jsonText}")
                    return jsonText
                except json.JSONDecodeError:
                    logger.error(f"Failed to parse JSON: {output}")
                    return {"error": "Invalid JSON response", "raw_output": output}
            elif index == 2:  # Error message
                error_msg = self.proc.match.group()
                logger.error(f"Lean error: {error_msg}")
                return {"error": error_msg}
            elif index == 3:  # EOF
                raise Exception("REPL process ended unexpectedly")
            else:  # TIMEOUT
                logger.error("Command timed out")
                logger.error(f"Buffer contents: {self.proc.before}")
                self.proc.kill(signal.SIGTERM)
                raise Exception("Command execution timed out")

        except Exception as e:
            logger.error(f"Error executing command: {str(e)}")
            logger.error(f"Process status: {self.proc.status}")
            logger.error(f"Last output: {self.proc.before}")
            raise
