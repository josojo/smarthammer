from fastapi import FastAPI, HTTPException
from fastapi.responses import StreamingResponse
from pydantic import BaseModel
from redis import Redis
from rq import Queue
import uuid
import io
import logging
from typing import List, Optional
from dataclasses import asdict
import json
import asyncio
import time
import logging

from hammer.main import prove_theorem
from hammer.proof.proof import ProofSearchState

app = FastAPI()
# Configure Redis connection and queue
redis_conn = Redis(host="localhost", port=6379)
task_queue = Queue("theorem_prover", connection=redis_conn)

# Add Redis pubsub connection
redis_pubsub = Redis(host="localhost", port=6379)

def setup_logging():
    # Configure root logger
    logging.basicConfig(
        level=logging.DEBUG,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )
    
    # Create internal logger for handler operations
    internal_logger = logging.getLogger("internal")
    internal_logger.setLevel(logging.DEBUG)
    
    # Create console handler for internal logger
    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.DEBUG)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    console_handler.setFormatter(formatter)
    internal_logger.addHandler(console_handler)

setup_logging()
logger = logging.getLogger(__name__)

class LogStreamHandler(logging.StreamHandler):
    def __init__(self, task_id):
        super().__init__()
        self.task_id = task_id
        self._internal_logger = logging.getLogger("internal")
        self._internal_logger.debug(f"Initialized LogStreamHandler for task: {task_id}")

    def emit(self, record):
        # Skip logs from the streaming endpoint itself to avoid loops
        if record.name == "internal":
            return
            
        log_entry = self.format(record)
        channel = f"logs:{self.task_id}"
        message = json.dumps({
            'timestamp': record.created,
            'message': log_entry
        })
        self._internal_logger.debug(f"Publishing to channel {channel}: {message}")
        redis_pubsub.publish(channel, message)


class TheoremRequest(BaseModel):
    name: str
    hypotheses: List[str]
    goal: str
    max_iteration_hypotheses_proof: int = 1
    max_correction_iteration_hypotheses_proof: int = 1
    max_iteration_final_proof: int = 1
    max_correction_iteration_final_proof: int = 1
    verbose: bool = True


class TaskStatus(BaseModel):
    task_id: str
    status: str
    result: Optional[dict] = None
    logs: Optional[str] = None


# Store task status and logs
task_status = {}


@app.post("/prove/", response_model=TaskStatus)
async def create_proof_task(theorem: TheoremRequest):
    task_id = str(uuid.uuid4())

    # Replace StringIO with custom handler
    log_handler = LogStreamHandler(task_id)
    log_handler.setLevel(logging.DEBUG)
    logging.getLogger().addHandler(log_handler)

    # Enqueue the task with the log capture
    job = task_queue.enqueue(
        prove_theorem,
        kwargs={
            "name": theorem.name,
            "hypotheses": theorem.hypotheses,
            "goal": theorem.goal,
            "max_iteration_hypotheses_proof": theorem.max_iteration_hypotheses_proof,
            "max_correction_iteration_hypotheses_proof": theorem.max_correction_iteration_hypotheses_proof,
            "max_iteration_final_proof": theorem.max_iteration_final_proof,
            "max_correction_iteration_final_proof": theorem.max_correction_iteration_final_proof,
            "verbose": theorem.verbose,
            "_log_capture": io.StringIO(),
        },
        job_id=task_id,
    )

    task_status[task_id] = {"status": "pending", "result": None, "logs": ""}

    return TaskStatus(task_id=task_id, status="pending", logs="")


@app.get("/status/{task_id}", response_model=TaskStatus)
async def get_task_status(task_id: str):
    if task_id not in task_status:
        raise HTTPException(status_code=404, detail="Task not found")

    job = task_queue.fetch_job(task_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Task not found in queue")

    # Get the logs from the job's meta if available
    logs = job.meta.get("logs", "") if job.meta else ""

    if job.is_finished:
        result = job.result
        if isinstance(result, ProofSearchState):
            result_dict = {
                "proof": result.proof,
                "theoretical_hypotheses": result.theoretical_hypotheses,
                "proven_hypotheses": [asdict(h) for h in result.proven_hypotheses],
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
                if message and message['type'] == 'message':
                    yield f"data: {message['data'].decode('utf-8')}\n\n"
                await asyncio.sleep(0.5)
        finally:
            pubsub.unsubscribe()
            pubsub.close()

    return StreamingResponse(
        event_stream(),
        media_type="text/event-stream"
    )


@app.get("/test-logs/{task_id}")
async def test_logs(task_id: str):
    """Test endpoint to verify Redis pub/sub"""
    channel = f"logs:{task_id}"
    message = json.dumps({
        'timestamp': time.time(),
        'message': 'Test log message'
    })
    result = redis_pubsub.publish(channel, message)
    return {"published_to": channel, "receivers": result}
