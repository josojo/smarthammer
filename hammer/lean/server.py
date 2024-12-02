"""Server module for interacting with Lean REPL."""

import json
import os
import pexpect
from dotenv import load_dotenv
import logging

logger = logging.getLogger(__name__)


class LeanServer:
    """Server class for managing interactions with a Lean REPL instance."""

    def __init__(self, initiate_mathlib=False):
        load_dotenv()
        path_to_repl = os.getenv("REPLPATH")
        if not path_to_repl:
            raise ValueError("REPLPATH environment variable not set in .env file")

        self.proc = pexpect.spawn(
            "lake env ../../.lake/build/bin/repl", cwd=path_to_repl, encoding="utf-8"
        )
        if initiate_mathlib:
            # setup the mathlib import, as this takes the longest in any simulation
            # and is "always" needed
            self.run_code("import Mathlib")

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
            command = json.dumps(
                {"cmd": code, "env": env},
            ).replace(
                "\\\\", "\\"
            )  # [1:-1] removes single quotes
        else:
            command = (
                '{ "cmd" : "' + repr(code)[1:-1] + '" }'
            )  # [1:-1] removes single quotes

        command_array = command.split("\\n")
        command_array = [cmd for cmd in command_array if cmd.strip() != ""]
        if verbose:
            logger.debug("Sending the following commands to the REPL:")
        for i, command in enumerate(command_array):
            if verbose:
                logger.debug(f"{i}-th line: \033[34m {command}\033[0m")
            self.proc.sendline(command)
            self.proc.expect_exact(command + "\r\n")
        self.proc.sendline()
        self.proc.expect_exact("\r\n")
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
