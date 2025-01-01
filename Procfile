# Procfile
release: ./install_lean.sh
web: uvicorn hammer.api.server:app --host 0.0.0.0 --port $PORT
worker: python -m rq worker theorem_prover --url $REDIS_URL 