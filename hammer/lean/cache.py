from hammer.lean.server import LeanServer
import threading
import logging


class LeanServerCache:
    _instance = None
    _lock = threading.Lock()
    _current_server = None
    _current_env = None

    def __init__(self):
        self.logger = logging.getLogger(__name__)

    @classmethod
    def get_instance(cls):
        if cls._instance is None:
            with cls._lock:
                if cls._instance is None:
                    cls._instance = cls()
        return cls._instance

    @classmethod
    def initialize(cls, code_env: str):
        """Pre-initialize the cache with a given environment"""
        instance = cls.get_instance()
        logger = logging.getLogger(__name__)
        logger.info(f"Starting LeanServer initialization with environment: {code_env}")
        try:
            server = instance.get_server(code_env)  # This will create the initial server
            logger.info("LeanServer initialization successful")
        except Exception as e:
            logger.error(f"LeanServer initialization failed: {str(e)}", exc_info=True)
            raise

    def get_server(self, code_env: str) -> LeanServer:
        with self._lock:
            if self._current_env != code_env:
                self.logger.debug(
                    f"Creating new LeanServer for environment: {code_env}"
                )
                if self._current_env is not None:
                    self.logger.debug(
                        f"Previous LeanServer was for the env environment: {self._current_env}"
                    )
                self._current_server = LeanServer(code_env)
                self._current_env = code_env
            return self._current_server
