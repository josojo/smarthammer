# Use Python 3.10 instead of 3.9
FROM python:3.10-slim

# Install system dependencies
RUN apt-get update && apt-get install -y \
    git \
    curl \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /app

# Copy only requirements first to leverage Docker cache
COPY requirements.txt .
RUN pip install -r requirements.txt

# Install Elan (Lean version manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Add Elan to PATH
ENV PATH="/root/.elan/bin:$PATH"

# Install Lean
# Setup REPL directory and clone
WORKDIR /app/repl
RUN --mount=type=cache,target=/root/.cache/lake \
    git clone https://github.com/leanprover-community/repl.git . && \
    elan default $(cat lean-toolchain) && \
    lake update && \
    lake build

# Setup Mathlib with cache
WORKDIR /app/repl/test/Mathlib
RUN --mount=type=cache,target=/root/.cache/lake \
    lake exe cache get

# Debug step to verify REPL setup
RUN ls -la /app/repl/test/Mathlib && \
    ls -la /app/repl/.lake/build/bin && \
    which lake && \
    lake --version

# Set environment variable for REPL path
ENV REPLPATH=/app/repl/test/Mathlib

# Copy the rest of your application files
# This should be near the end as it changes frequently
COPY . .

# Return to app directory
WORKDIR /app

# Expose port (adjust if needed)
EXPOSE 8000

# Add memory limits for container
# 4GB for Lean
ENV LEAN_MEMORY=4096
# 2GB for Lake
ENV LAKE_MEMORY=2048

# Start command using the same structure as your Procfile
CMD ["sh", "-c", "ulimit -v $((LEAN_MEMORY * 1024)) && uvicorn hammer.api.server:app --host 0.0.0.0 --port ${PORT:-8000} & python -m hammer.worker"] 