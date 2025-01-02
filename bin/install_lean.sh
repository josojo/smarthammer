#!/bin/bash
set -e

echo "Starting REPL setup..."

# Create a writable directory in /tmp
WORK_DIR="/tmp/repl_setup"
mkdir -p "$WORK_DIR"
cd "$WORK_DIR"

echo "Current PATH: $PATH"
echo "Current directory: $(pwd)"
echo "Listing available commands:"
which git || echo "git not found"

# Install Elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Add Elan to PATH
export PATH="$HOME/.elan/bin:$PATH"

# Clone REPL repository
echo "Cloning REPL repository..."
/app/.apt/usr/bin/git clone https://github.com/leanprover-community/repl.git
cd repl

# Install Lean version as specified in lean-toolchain:
LEAN_VERSION=$(cat lean-toolchain)
elan default $LEAN_VERSION

# Build REPL
lake update
lake build
cd test/Mathlib
lake exe cache get > /dev/null

# Copy built files to the app directory
mkdir -p /app/repl
cp -r "$WORK_DIR/repl"/* /app/repl/

echo "REPL setup completed successfully"