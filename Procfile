# Procfile
release: ./bin/install_lean.sh
web: uvicorn hammer.api.server:app
worker: python -m hammer.worker 