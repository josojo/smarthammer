"""Server module for interacting with Lean REPL."""
import json
import os
import pexpect
from dotenv import load_dotenv


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
            command = json.dumps({"cmd": code, "env": env},).replace(
                "\\\\", "\\"
            )  # [1:-1] removes single quotes
        else:
            command = (
                '{ "cmd" : "' + repr(code)[1:-1] + '" }'
            )  # [1:-1] removes single quotes

        command_array = command.split("\\n")
        print("command_array", command_array)
        for command in command_array:
            if verbose:
                print("sending the following command", command)
            self.proc.sendline(command)
            self.proc.expect_exact(command + "\r\n")
        self.proc.sendline()
        self.proc.expect_exact("\r\n")
        try:
            try:
                self.proc.expect(r'env": \d+\}', timeout=300)
                output = self.proc.before + self.proc.match.group()
                if verbose:
                    print("Receiving the following output", output)
                return json.loads(output)
            except pexpect.exceptions.EOF:
                # Print the buffer contents even if expect times out
                print("EOF. Current buffer contents:")
                print(self.proc.before)
                raise
        except pexpect.exceptions.TIMEOUT:
            raise pexpect.exceptions.TIMEOUT
