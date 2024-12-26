from abc import ABC, abstractmethod


class AIClient(ABC):
    """Abstract base class for AI clients."""

    @abstractmethod
    def send(self, message: str, verbose: bool = False) -> str:
        """Send a message to the AI and return its response.

        Args:
            message: The message to send to the AI
            verbose: Whether to log debug information

        Returns:
            str: The AI's response
        """
        pass
