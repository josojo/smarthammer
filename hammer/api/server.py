from fastapi import FastAPI, HTTPException
from fastapi.responses import StreamingResponse
from pydantic import BaseModel
from redis import Redis, ConnectionPool
from rq import Queue
import uuid
import logging
from typing import List, Optional, Dict
import json
import asyncio
import time
import logging
from rq.job import Job
from fastapi.middleware.cors import CORSMiddleware
from enum import Enum
import os
from rq.registry import FailedJobRegistry
from urllib.parse import urlparse
import redis

from hammer.main import prove_theorem
from hammer.proof.proof import ProofSearchState
from hammer.api.logging import LogStreamHandler, redis_pubsub
from hammer.api.types import AIForHypothesesProof
from hammer.api.config import SOLVER_LIMITS

app = FastAPI()
# Configure Redis connection and queue
redis_url = os.getenv("REDIS_URL", "redis://localhost:6379")

url = urlparse(redis_url)


# Configure Redis connection with the connection pool
redis_conn = redis.Redis(
    host=url.hostname,
    port=url.port,
    password=url.password,
    ssl=(url.scheme == "rediss"),
    ssl_cert_reqs=None,
)
task_queue = Queue("theorem_prover", connection=redis_conn)

# Add Redis pubsub connection
redis_pubsub = redis.Redis(
    host=url.hostname,
    port=url.port,
    password=url.password,
    ssl=(url.scheme == "rediss"),
    ssl_cert_reqs=None,
)

# Add CORS middleware configuration
app.add_middleware(
    CORSMiddleware,
    allow_origins=[
        "http://localhost:3000",  # React default port
        "http://127.0.0.1:3000",  # React default port (alternative URL)
        "http://localhost:5173",  # Vite default port
        "http://127.0.0.1:5173",
        "https://owlgebra.vercel.app",  # Add your Vercel domain
    ],
    allow_credentials=True,
    allow_methods=["GET", "POST", "PUT", "DELETE"],
    allow_headers=["Content-Type", "Authorization"],
)


def setup_logging():
    # Configure root logger
    logging.basicConfig(
        level=logging.DEBUG,
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    )

    # Create internal logger for handler operations
    internal_logger = logging.getLogger("internal")
    internal_logger.setLevel(logging.DEBUG)

    # Create console handler for internal logger
    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.DEBUG)
    formatter = logging.Formatter(
        "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    )
    console_handler.setFormatter(formatter)
    internal_logger.addHandler(console_handler)


setup_logging()
logger = logging.getLogger(__name__)


class TheoremRequest(BaseModel):
    name: str
    hypotheses: List[str]
    goal: str
    ai_for_hypotheses_generation: AIForHypothesesProof = AIForHypothesesProof.CLAUDE
    ai_for_hyptheses_proof: AIForHypothesesProof = AIForHypothesesProof.CLAUDE
    ai_for_final_proof: AIForHypothesesProof = AIForHypothesesProof.CLAUDE
    max_iteration_hypotheses_proof: int = 1
    max_correction_iteration_hypotheses_proof: int = 1
    max_iteration_final_proof: int = 1
    max_correction_iteration_final_proof: int = 1
    verbose: bool = True
    code_for_env_0: str | None = "import Mathlib"


class TaskStatus(BaseModel):
    task_id: str
    status: str
    result: Optional[dict] = None
    logs: Optional[str] = None


def my_handler(job, exc_type, exc_value, traceback):
    # Custom error handling logic

    logger.error(f"Job {job.id} failed with error: {exc_value}", exc_info=True)


@app.post("/prove/", response_model=TaskStatus)
async def create_proof_task(theorem: TheoremRequest):
    # Create a task_id that starts with the theorem name and includes timestamp
    timestamp = int(time.time())
    task_id = f"{theorem.name}-{timestamp}-{str(uuid.uuid4())[:10]}"

    # Initialize task status in Redis
    initial_status = {"status": "pending", "result": None, "logs": ""}
    redis_conn.set(f"task:{task_id}", json.dumps(initial_status))
    # Initialize empty log string in Redis
    redis_conn.set(f"logs:{task_id}", "")

    # Enqueue the task with the task_id
    job = task_queue.enqueue(
        prove_theorem,
        kwargs={
            "name": theorem.name,
            "hypotheses": theorem.hypotheses,
            "goal": theorem.goal,
            "code_for_env_0": theorem.code_for_env_0,
            "max_iteration_hypotheses_proof": theorem.max_iteration_hypotheses_proof,
            "max_correction_iteration_hypotheses_proof": theorem.max_correction_iteration_hypotheses_proof,
            "max_iteration_final_proof": theorem.max_iteration_final_proof,
            "max_correction_iteration_final_proof": theorem.max_correction_iteration_final_proof,
            "ai_for_hypotheses_generation": theorem.ai_for_hypotheses_generation,
            "ai_for_hyptheses_proof": theorem.ai_for_hyptheses_proof,
            "ai_for_final_proof": theorem.ai_for_final_proof,
            "verbose": theorem.verbose,
            "task_id": task_id,
        },
        job_id=task_id,
        result_ttl=166400,  # Store finished jobs for 2*24 hours
        job_timeout=7200,  # Increase timeout to 2 hours
        failure_ttl=24 * 3600,  # Keep failed jobs for 24 hours
        meta={
            "enqueued_at": time.time(),
            "memory_limit": 1024 * 1024 * 1024 * 2,  # 1GB limit
        },
        exception_handlers=[my_handler],
    )

    return TaskStatus(task_id=task_id, status="pending", logs="")


@app.get("/status/{task_id}", response_model=TaskStatus)
async def get_task_status(task_id: str):
    # Get the job first
    job = task_queue.fetch_job(task_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Task not found in queue")

    # Get logs from Redis
    logs = redis_conn.get(f"logs:{task_id}")
    logs = logs.decode("utf-8") if logs else ""

    if job.is_finished:
        result = job.result
        if isinstance(result, ProofSearchState):
            # Safely convert proven_hypotheses to dictionaries
            proven_hypotheses = []
            for h in result.proven_hypotheses:
                if hasattr(h, "__dict__"):
                    # If it's an object with attributes, convert to dict
                    proven_hypotheses.append(vars(h))
                else:
                    # If it's a simple type, use it as is
                    proven_hypotheses.append(h)

            result_dict = {
                "proof": result.proof,
                "theoretical_hypotheses": result.theoretical_hypotheses,
                "proven_hypotheses": proven_hypotheses,
                "name": result.name,
                "goal": result.goal,
            }
            return TaskStatus(
                task_id=task_id, status="completed", result=result_dict, logs=logs
            )

    if job.is_failed:
        return TaskStatus(
            task_id=task_id,
            status="failed",
            result={"error": str(job.exc_info)},
            logs=logs,
        )

    return TaskStatus(task_id=task_id, status="pending", logs=logs)


@app.get("/logs/{task_id}")
async def stream_logs(task_id: str):
    logger.debug(f"Starting log stream for task: {task_id}")

    async def event_stream():
        pubsub = redis_pubsub.pubsub()
        channel = f"logs:{task_id}"
        pubsub.subscribe(channel)

        try:
            while True:
                # Check if task is complete
                job = task_queue.fetch_job(task_id)
                if job and (job.is_finished or job.is_failed):
                    logger.debug(f"Task {task_id} completed or failed, closing stream")
                    break

                message = pubsub.get_message(timeout=1.0)
                if message and message["type"] == "message":
                    log_message = message["data"].decode("utf-8")
                    # Append the new log message to task_status
                    if task_id in task_status:
                        logs = redis_pubsub.get(f"logs:{task_id}") or ""
                        task_status[task_id]["logs"] = (
                            logs.decode() if isinstance(logs, bytes) else logs
                        )
                    yield f"data: {log_message}\n\n"
                await asyncio.sleep(0.5)
        finally:
            pubsub.unsubscribe()
            pubsub.close()

    return StreamingResponse(event_stream(), media_type="text/event-stream")


@app.get("/test-logs/{task_id}")
async def test_logs(task_id: str):
    """Test endpoint to verify Redis pub/sub"""
    channel = f"logs:{task_id}"
    message = json.dumps({"timestamp": time.time(), "message": "Test log message"})
    result = redis_pubsub.publish(channel, message)
    return {"published_to": channel, "receivers": result}


@app.get("/pending-tasks/", response_model=Dict[str, List[str]])
async def get_pending_tasks():
    """
    Returns a dictionary containing:
    - pending_tasks: List of task IDs that are waiting to be executed
    - running_tasks: List of task IDs that are currently being executed
    - failed_tasks: List of task IDs that failed
    - finished_tasks: List of task IDs that completed successfully
    """
    # Get all jobs from the queue
    registry = task_queue.started_job_registry
    running_jobs = registry.get_job_ids()

    # Get queued jobs
    pending_jobs = task_queue.get_jobs()

    # Get failed jobs
    failed_registry = task_queue.failed_job_registry
    failed_jobs = failed_registry.get_job_ids()

    # Get finished jobs
    finished_registry = task_queue.finished_job_registry
    finished_jobs = finished_registry.get_job_ids()

    logger.debug(f"Found running jobs: {running_jobs}")
    logger.debug(f"Found pending jobs: [job.id for job in pending_jobs]")
    logger.debug(f"Found failed jobs: {failed_jobs}")
    logger.debug(f"Found finished jobs: {finished_jobs}")

    return {
        "pending_tasks": [job.id for job in pending_jobs][::-1],
        "running_tasks": running_jobs[::-1],
        "failed_tasks": failed_jobs[::-1],
        "finished_tasks": finished_jobs[::-1],
    }


@app.delete("/clean-failed-tasks/")
async def clean_failed_tasks():
    """
    Deletes all failed tasks from the worker queue.
    """
    failed_job_registry = FailedJobRegistry(queue=task_queue)
    deleted_jobs = []

    for job_id in failed_job_registry.get_job_ids():
        job = Job.fetch(job_id, connection=redis_conn)
        job.delete()
        deleted_jobs.append(job_id)
        logger.info(f"Deleted failed job: {job_id}")

    return {
        "deleted_jobs": deleted_jobs,
        "message": "All failed jobs have been deleted.",
    }


@app.get("/solver-config/")
async def get_solver_config():
    """
    Returns the current solver configuration limits.
    """
    return {
        "limits": {
            "iterations": {
                "max_iteration_hypotheses_proof": SOLVER_LIMITS.max_iteration_hypotheses_proof,
                "max_correction_iteration_hypotheses_proof": SOLVER_LIMITS.max_correction_iteration_hypotheses_proof,
                "max_iteration_final_proof": SOLVER_LIMITS.max_iteration_final_proof,
                "max_correction_iteration_final_proof": SOLVER_LIMITS.max_correction_iteration_final_proof,
            },
            "allowed_models": {
                "hypothesis_generation": [model.value for model in SOLVER_LIMITS.allowed_hypothesis_generation_models],
                "hypothesis_proof": [model.value for model in SOLVER_LIMITS.allowed_hypothesis_proof_models],
                "final_proof": [model.value for model in SOLVER_LIMITS.allowed_final_proof_models],
            }
        },
        "description": {
            "max_iteration_hypotheses_proof": "Maximum number of iterations for hypothesis proof generation",
            "max_correction_iteration_hypotheses_proof": "Maximum number of correction iterations for hypothesis proofs",
            "max_iteration_final_proof": "Maximum number of iterations for final proof generation",
            "max_correction_iteration_final_proof": "Maximum number of correction iterations for final proof",
            "allowed_models": "List of allowed AI models for each proof stage"
        }
    }
