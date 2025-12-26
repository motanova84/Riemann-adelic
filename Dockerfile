# Dockerfile for reproducible Lean 4 formal verification
# Based on official Lean 4 community image with pinned version

FROM leanprovercommunity/lean:4.5.0

# Set working directory
WORKDIR /work

# Install make for Makefile support
RUN apt-get update && apt-get install -y make && rm -rf /var/lib/apt/lists/*

# Copy project files
COPY formalization/lean/lean-toolchain formalization/lean/lean-toolchain
COPY formalization/lean/lakefile.lean formalization/lean/lakefile.lean

# Pre-fetch dependencies to cache them in Docker layer
WORKDIR /work/formalization/lean
RUN lake update

# Copy remaining files
WORKDIR /work
COPY . .

# Default command: run proof verification
CMD ["make", "proof"]
