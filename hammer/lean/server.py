"""Server module for interacting with Lean REPL."""

import json
import os
import pexpect
from dotenv import load_dotenv
import logging
import sys

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

        # Add debug logging
        logger.debug(f"REPLPATH (raw): {os.getenv('REPLPATH')}")
        logger.debug(f"REPLPATH (cleaned): {path_to_repl}")
        logger.debug(f"Current directory: {os.getcwd()}")

        # Create directory if it doesn't exist
        os.makedirs(path_to_repl, exist_ok=True)

        logger.debug(f"Directory contents: {os.listdir(path_to_repl)}")

        # Check if the REPL binary exists
        repl_binary = "../../.lake/build/bin/repl"
        full_repl_path = os.path.join(path_to_repl, repl_binary)
        logger.debug(f"Looking for REPL binary at: {full_repl_path}")

        if not os.path.exists(full_repl_path):
            raise FileNotFoundError(f"REPL binary not found at {full_repl_path}")

        command = f"/bin/bash -c 'stty -icanon && lake env {repl_binary}'"
        logger.debug(f"Executing command: {command}")

        self.proc = pexpect.spawn(
            command,
            cwd=path_to_repl,
            encoding="utf-8",
            echo=False,
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

        self.proc.sendline(command)
        self.proc.sendline()

        try:
            try:
                self.proc.expect(r'env": \d+\}', timeout=100)
                output = self.proc.before + self.proc.match.group()
                if verbose:
                    logger.debug(
                        f"Receiving the following simulation output\n \033[35m{output}\033[0m"
                    )
                return json.loads(output)
            except pexpect.exceptions.EOF:
                logger.error("EOF. Current buffer contents:")
                logger.error(self.proc.before)
                raise
        except pexpect.exceptions.TIMEOUT:
            logger.error("TIMEOUT. Current buffer contents:")
            logger.error(self.proc.before)
            raise pexpect.exceptions.TIMEOUT
