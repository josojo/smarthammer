from fastapi import FastAPI, HTTPException
from fastapi.responses import StreamingResponse
from pydantic import BaseModel
from redis import Redis
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

from hammer.main import prove_theorem
from hammer.proof.proof import ProofSearchState
from hammer.api.logging import LogStreamHandler, redis_pubsub

app = FastAPI()
# Configure Redis connection and queue
redis_conn = Redis(host="localhost", port=6379)
task_queue = Queue("theorem_prover", connection=redis_conn)

# Add Redis pubsub connection
redis_pubsub = Redis(host="localhost", port=6379)

# Add CORS middleware configuration
app.add_middleware(
    CORSMiddleware,
    allow_origins=[
        "http://localhost:3000",  # React default port
        "http://127.0.0.1:3000",  # React default port (alternative URL)
        "http://localhost:5173",  # Vite default port
        "http://127.0.0.1:5173",
        "http://your-production-domain.com",
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


# Store task status and logs
task_status = {}


@app.post("/prove/", response_model=TaskStatus)
async def create_proof_task(theorem: TheoremRequest):
    # Create a task_id that starts with the theorem name
    task_id = f"{theorem.name}-{uuid.uuid4()}"

    # Initialize task status with empty logs
    task_status[task_id] = {"status": "pending", "result": None, "logs": ""}

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
            "verbose": theorem.verbose,
            "task_id": task_id,  # Pass task_id to the worker
        },
        job_id=task_id,
        result_ttl=86400,  # Store finished jobs for 24 hours
    )

    return TaskStatus(task_id=task_id, status="pending", logs="")


@app.get("/status/{task_id}", response_model=TaskStatus)
async def get_task_status(task_id: str):
    # Get the job first
    job = task_queue.fetch_job(task_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Task not found in queue")

    # Initialize task_status if it doesn't exist
    if task_id not in task_status:
        task_status[task_id] = {"status": "pending", "result": None, "logs": ""}

    # Get the logs from the job's meta if available
    logs = job.meta.get("logs", "") if job.meta else ""
    logs = task_status[task_id]["logs"]
    # console.log(logs)

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
                        task_status[task_id]["logs"] += log_message + "\n"
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
        "pending_tasks": [job.id for job in pending_jobs],
        "running_tasks": running_jobs,
        "failed_tasks": failed_jobs,
        "finished_tasks": finished_jobs,
    }
