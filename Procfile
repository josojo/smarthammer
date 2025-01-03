# Procfile
release: ./bin/install_lean.sh
web: uvicorn hammer.api.server:app --host 0.0.0.0 --port $PORT
worker: python -m hammer.worker
