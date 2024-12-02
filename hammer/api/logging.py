import logging
import json
from redis import Redis

# Configure Redis connection
redis_pubsub = Redis(host="localhost", port=6379)

# Create internal logger for handler operations
internal_logger = logging.getLogger("internal")


class LogStreamHandler(logging.StreamHandler):
    def __init__(self, task_id):
        super().__init__()
        self.task_id = task_id
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
            # Skip logs from ignored loggers and internal logger
            if record.name == "internal" or any(
                record.name.startswith(ignored) for ignored in self.ignored_loggers
            ):
                return

            log_entry = self.format(record)
            channel = f"logs:{self.task_id}"
            message = json.dumps(
                {
                    "timestamp": record.created,
                    "name": record.name,
                    "level": record.levelname,
                    "message": log_entry,
                }
            )
            redis_pubsub.publish(channel, message)
        except Exception as e:
            self._internal_logger.error(f"Error in LogStreamHandler.emit: {e}")
