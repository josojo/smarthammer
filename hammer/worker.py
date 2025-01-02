from rq import Worker, Queue
import os
import logging
from rq.timeouts import JobTimeoutException
import signal
from urllib.parse import urlparse
import redis

logger = logging.getLogger(__name__)

# Configure Redis connection
redis_url = os.getenv("REDIS_URL", "redis://localhost:6379")
url = urlparse(redis_url)
# Configure Redis connection with the connection pool
redis_conn = redis.Redis(host=url.hostname, port=url.port, password=url.password, ssl=(url.scheme == "rediss"), ssl_cert_reqs=None)

# Worker configuration
default_worker_ttl = 7200  # 2 hours
default_result_ttl = 14400  # 4 hours
job_timeout = 3600  # 1 hour


def handle_timeout(signum, frame):
    raise JobTimeoutException("Job exceeded maximum timeout value")


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)

    # Suppress debug logs from rq.scheduler
    logging.getLogger("rq.scheduler").setLevel(logging.INFO)

    # Register signal handlers
    signal.signal(signal.SIGALRM, handle_timeout)

    def handle_term(signum, frame):
        logger.info(f"Received signal {signum}")
        raise SystemExit("Received SIGTERM")

    signal.signal(signal.SIGTERM, handle_term)

    # Create queue with default settings
    queue = Queue(
        "theorem_prover", connection=redis_conn, default_timeout=3600, result_ttl=14400
    )

    worker = Worker(
        queues=[queue],
        connection=redis_conn,
        worker_ttl=default_worker_ttl,  # Set appropriate TTL
    )

    # Start the worker with exception handling
    try:
        worker.work(
            with_scheduler=True,
            burst=False,
            logging_level=logging.DEBUG,
        )
    except KeyboardInterrupt:
        logger.info("Worker stopped by user")
    except Exception as e:
        logger.error(f"Worker failed with error: {e}", exc_info=True)
    finally:
        try:
            worker.register_death()
        except Exception as e:
            logger.error(f"Error during worker cleanup: {e}")
