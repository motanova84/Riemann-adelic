# Makefile for Riemann-Adelic Formal Verification
# Builds and verifies all Lean 4 formal content

.PHONY: all pdf figs tables proof clean help

# Default target
all: pdf figs tables proof

# PDF target: build PDF documentation
pdf:
	@echo "Building PDF documentation..."
	@if [ -f paper_standalone.tex ]; then \
		latexmk -pdf -shell-escape paper_standalone.tex 2>/dev/null || echo "Note: LaTeX build requires pdflatex, latexmk, and biber"; \
	else \
		echo "No LaTeX files found to build"; \
	fi
	@echo "✓ PDF build complete (if applicable)!"

# Figures target: generate figures
figs:
	@echo "Generating figures..."
	@if [ -f scripts/make_figs.py ]; then \
		python3 scripts/make_figs.py; \
	else \
		echo "Note: scripts/make_figs.py not found, skipping"; \
	fi
	@echo "✓ Figures generation complete!"

# Tables target: generate tables
tables:
	@echo "Generating tables..."
	@if [ -f scripts/make_tables.py ]; then \
		python3 scripts/make_tables.py; \
	else \
		echo "Note: scripts/make_tables.py not found, skipping"; \
	fi
	@echo "✓ Tables generation complete!"

# Proof target: build and verify all Lean formalization
proof:
	@echo "Building Lean 4 formalization..."
	cd formalization/lean && lake build
	@echo "✓ Proof verification complete!"

# Clean build artifacts
clean:
	@echo "Cleaning build artifacts..."
	cd formalization/lean && lake clean
	@if [ -f paper_standalone.tex ]; then \
		latexmk -C paper_standalone.tex 2>/dev/null || true; \
	fi
	@echo "✓ Clean complete!"

# Help target
help:
	@echo "Available targets:"
	@echo "  all       - Build PDF, figures, tables, and proofs (default)"
	@echo "  pdf       - Build PDF documentation"
	@echo "  figs      - Generate figures"
	@echo "  tables    - Generate tables"
	@echo "  proof     - Build and verify all Lean 4 formal proofs"
	@echo "  clean     - Clean build artifacts"
	@echo "  help      - Show this help message"
	@echo ""
	@echo "Docker usage (reproducible build):"
	@echo "  docker run --rm -v \"\$$PWD\":/work -w /work leanprovercommunity/lean:4.5.0 /bin/bash -lc \"make proof\""
	@echo ""
	@echo "Nix usage (reproducible build):"
	@echo "  nix develop --command make proof"
