import logging
import json
import os
from urllib.parse import urlparse
import redis


class ContextualLoggerAdapter(logging.LoggerAdapter):
    def process(self, msg, kwargs):
        # Add the current step to the log message
        self.set_step(self.extra["step"])
        return f"[{self.extra['step']}] {msg}", kwargs

    def set_step(self, step):
        # Update the step in the extra dictionary
        self.extra["step"] = step


# Configure Redis connection
redis_url = os.getenv("REDIS_URL", "redis://localhost:6379")
url = urlparse(redis_url)
# Configure Redis connection with the connection pool
redis_pubsub = redis.Redis(
    host=url.hostname,
    port=url.port,
    password=url.password,
    ssl=(url.scheme == "rediss"),
    ssl_cert_reqs=None,
)

# Create internal logger for handler operations
internal_logger = logging.getLogger("internal")


class LogStreamHandler(logging.Handler):
    def __init__(self, task_id):
        super().__init__()
        self.task_id = task_id
        self.redis_conn = redis.Redis(
            host=url.hostname,
            port=url.port,
            password=url.password,
            ssl=(url.scheme == "rediss"),
            ssl_cert_reqs=None,
        )
        # Add back the logging configurations
        self.setLevel(logging.DEBUG)
        self.setFormatter(logging.Formatter("%(message)s"))
        self._internal_logger = logging.getLogger("internal")
        self._contextual_logger = ContextualLoggerAdapter(
            self._internal_logger, {"step": "Initialization"}
        )
        self._contextual_logger.debug(
            f"Initialized LogStreamHandler for task: {task_id}"
        )

        # List of logger names to ignore
        self.ignored_loggers = [
            "anthropic",
            "anthropic._base_client",
            "urllib3",
            "httpcore",
            "httpx",
            "rq.scheduler",
        ]

    def set_step(self, step):
        # Update the step in the contextual logger
        self._contextual_logger.set_step(step)

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
                    "step": self._contextual_logger.extra["step"],
                    "message": msg,
                }
            )
            self.redis_conn.publish(f"logs:{self.task_id}", message + "\n")

            # Append to a Redis string for persistent storage
            self.redis_conn.append(f"logs:{self.task_id}", message + "\n")

        except Exception:
            self.handleError(record)
