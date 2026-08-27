# Makefile for Python-Lean FFI Bridge
# ====================================
#
# This Makefile builds the C bridge library that connects Python and Lean.
#
# Usage:
#   make           - Build the FFI bridge library
#   make test      - Run tests for the FFI bridge
#   make clean     - Remove build artifacts
#   make install   - Install the library (requires sudo)

# Detect Python version
PYTHON_VERSION := $(shell python3 -c "import sys; print(f'{sys.version_info.major}.{sys.version_info.minor}')")
PYTHON_INCLUDE := $(shell python3 -c "import sysconfig; print(sysconfig.get_path('include'))")
PYTHON_LIB := $(shell python3 -c "import sysconfig; print(sysconfig.get_config_var('LIBDIR'))")

# Compiler settings
CC := gcc
CFLAGS := -Wall -Wextra -fPIC -O2 -I$(PYTHON_INCLUDE)
LDFLAGS := -shared -L$(PYTHON_LIB) -lpython$(PYTHON_VERSION)

# Output library
TARGET := libffi_bridge.so

# Source files
SRC := ffi_bridge.c

# Installation directory (change if needed)
INSTALL_DIR := /usr/local/lib

.PHONY: all test clean install help

all: $(TARGET)
	@echo "✅ FFI bridge library built successfully: $(TARGET)"
	@echo ""
	@echo "To use the library:"
	@echo "  1. Ensure Python $(PYTHON_VERSION) is installed"
	@echo "  2. Set LD_LIBRARY_PATH to include current directory:"
	@echo "     export LD_LIBRARY_PATH=\$$LD_LIBRARY_PATH:$$(pwd)"
	@echo "  3. Build Lean code with: lake build"
	@echo ""

$(TARGET): $(SRC)
	@echo "🔨 Building FFI bridge library..."
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

test: $(TARGET)
	@echo "🧪 Running FFI bridge tests..."
	@echo ""
	@echo "[1] Testing Python wrapper..."
	python3 python_ffi_wrapper.py
	@echo ""
	@echo "[2] Testing C bridge (requires Lean)..."
	@echo "    (Run 'lake build' in formalization/lean to test Lean bindings)"
	@echo ""
	@echo "✅ Python tests completed"

clean:
	@echo "🧹 Cleaning build artifacts..."
	rm -f $(TARGET)
	rm -f *.o
	rm -rf __pycache__
	rm -rf *.pyc
	@echo "✅ Clean complete"

install: $(TARGET)
	@echo "📦 Installing FFI bridge library to $(INSTALL_DIR)..."
	sudo cp $(TARGET) $(INSTALL_DIR)/
	sudo ldconfig
	@echo "✅ Installation complete"
	@echo ""
	@echo "Library installed to: $(INSTALL_DIR)/$(TARGET)"
	@echo "You may need to update LD_LIBRARY_PATH if not using system paths"

uninstall:
	@echo "🗑️  Uninstalling FFI bridge library..."
	sudo rm -f $(INSTALL_DIR)/$(TARGET)
	sudo ldconfig
	@echo "✅ Uninstall complete"

help:
	@echo "QCAL Python-Lean FFI Bridge - Build System"
	@echo "=========================================="
	@echo ""
	@echo "Available targets:"
	@echo "  make           - Build the FFI bridge library"
	@echo "  make test      - Run tests"
	@echo "  make clean     - Remove build artifacts"
	@echo "  make install   - Install library to system (requires sudo)"
	@echo "  make uninstall - Remove library from system (requires sudo)"
	@echo "  make help      - Show this help message"
	@echo ""
	@echo "Current configuration:"
	@echo "  Python version: $(PYTHON_VERSION)"
	@echo "  Python include: $(PYTHON_INCLUDE)"
	@echo "  Python lib:     $(PYTHON_LIB)"
	@echo "  Target:         $(TARGET)"
	@echo ""
