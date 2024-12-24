"""Server module for interacting with Lean REPL."""

import json
import os
import pexpect
from dotenv import load_dotenv
import logging

logger = logging.getLogger(__name__)


class LeanServer:
    """Server class for managing interactions with a Lean REPL instance."""

    def __init__(self, code_for_env_0="import Mathlib"):
        load_dotenv()
        path_to_repl = os.getenv("REPLPATH")
        if not path_to_repl:
            raise ValueError("REPLPATH environment variable not set in .env file")

        # stty -icanon is a command to disable canonical mode in the terminal to allow for longer inputs
        self.proc = pexpect.spawn(
            "/bin/bash -c 'stty -icanon && lake env ../../.lake/build/bin/repl'",
            cwd=path_to_repl,
            encoding="utf-8",
            echo=False,
        )
        if code_for_env_0:
            self.run_code(code_for_env_0)

    def run_code(self, code, env=None, verbose=False):
        """Execute Lean code in the REPL.

        Args:
            code (str): The Lean code to execute
            env (int, optional): Environment ID. Defaults to None
            verbose (bool, optional): Enable verbose output. Defaults to False

        Returns:
            dict: JSON response from the REPL

        Raises:
            pexpect.exceptions.TIMEOUT: If REPL response times out
        """
        if env is not None:
            command = (
                json.dumps(
                    {"cmd": code, "env": env},
                )
                .replace("\\\\", "\\")  # [1:-1] removes single quotes
                .replace("\\n\\n", "\\n")  # [1:-1] removes double newlines
            )
        else:
            command = (
                '{ "cmd" : "' + repr(code)[1:-1] + '" }'
            )  # [1:-1] removes single quotes
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
                # Print the buffer contents even if expect times out
                logger.error("EOF. Current buffer contents:")
                logger.error(self.proc.before)
                raise
        except pexpect.exceptions.TIMEOUT:
            logger.error("TIMEOUT. Current buffer contents:")
            logger.error(self.proc.before)
            raise pexpect.exceptions.TIMEOUT
