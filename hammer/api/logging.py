import logging
import json
from redis import Redis

# Configure Redis connection
redis_pubsub = Redis(host="localhost", port=6379)

# Create internal logger for handler operations
internal_logger = logging.getLogger("internal")


class LogStreamHandler(logging.Handler):
    def __init__(self, task_id):
        super().__init__()
        self.task_id = task_id
        self.redis_conn = Redis(host="localhost", port=6379)
        # Add back the logging configurations
        self.setLevel(logging.DEBUG)
        self.setFormatter(logging.Formatter("%(message)s"))
        self._internal_logger = logging.getLogger("internal")
        self._internal_logger.debug(f"Initialized LogStreamHandler for task: {task_id}")

        # List of logger names to ignore
        self.ignored_loggers = [
            "anthropic",
            "anthropic._base_client",
            "urllib3",
            "httpcore",
            "httpx",
        ]

    def emit(self, record):
        try:
            # Skip ignored loggers
            if record.name == "internal" or any(
                record.name.startswith(ignored) for ignored in self.ignored_loggers
            ):
                return

            msg = self.format(record)
            # Publish to pubsub for real-time streaming
            message = json.dumps(
                {
                    "timestamp": record.created,
                    "name": record.name,
                    "level": record.levelname,
                    "message": msg,
                }
            )
            self.redis_conn.publish(f"logs:{self.task_id}", message + "\n")

            # Append to a Redis string for persistent storage
            self.redis_conn.append(f"logs:{self.task_id}", message + "\n")

        except Exception:
            self.handleError(record)
