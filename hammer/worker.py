from redis import Redis
from rq import Worker, Queue

redis_conn = Redis(host="localhost", port=6379)

worker = Worker(["theorem_prover"], connection=redis_conn)
worker.work()
