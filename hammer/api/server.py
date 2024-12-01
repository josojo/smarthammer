from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
from redis import Redis
from rq import Queue
import uuid
import io
import logging
from typing import List, Optional
from dataclasses import asdict

from hammer.main import prove_theorem
from hammer.proof.proof import ProofSearchState

app = FastAPI()
# Configure Redis connection and queue
redis_conn = Redis(host="localhost", port=6379)
task_queue = Queue("theorem_prover", connection=redis_conn)


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

    # Create a string buffer to capture logs
    log_capture = io.StringIO()
    log_handler = logging.StreamHandler(log_capture)
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
            "_log_capture": log_capture,
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
