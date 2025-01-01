   # install_lean.sh
   #!/bin/bash
   set -e



    # Install necessary system packages
    apt-get update && apt-get install -y \
    build-essential \
    cmake \
    ninja-build \
    libssl-dev \
    pkg-config

   # Install Elan
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

   # Add Elan to PATH
   export PATH="$HOME/.elan/bin:$PATH"

   # Install Lean version as specified in lean-toolchain
   cd repl
   LEAN_VERSION=$(cat lean-toolchain)
   elan default $LEAN_VERSION

   # Build REPL
   lake update
   lake build
   cd test/Mathlib
   lake exe cache get > /dev/null