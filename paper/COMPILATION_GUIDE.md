# Compilation Guide for Integrated Paper

## Prerequisites

You need a LaTeX distribution installed:

### Linux (Ubuntu/Debian)
```bash
sudo apt-get install texlive-full
```

### macOS
```bash
brew install --cask mactex
```

### Windows
Download and install MiKTeX or TeX Live from their official websites.

## Compilation Steps

### Basic Compilation

```bash
cd paper/
pdflatex main_integrated.tex
bibtex main_integrated
pdflatex main_integrated.tex
pdflatex main_integrated.tex
```

The multiple `pdflatex` runs are needed to:
1. First run: Generate auxiliary files
2. After bibtex: Process bibliography
3. Second run: Resolve citations
4. Third run: Resolve cross-references

### Using Makefile (Recommended)

Create a `Makefile` in the `paper/` directory:

```makefile
.PHONY: all clean

MAIN = main_integrated
LATEX = pdflatex
BIBTEX = bibtex

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex sections/*.tex appendix/*.tex biblio.bib
	$(LATEX) $(MAIN)
	$(BIBTEX) $(MAIN)
	$(LATEX) $(MAIN)
	$(LATEX) $(MAIN)

clean:
	rm -f *.aux *.log *.bbl *.blg *.out *.toc *.lof *.lot

distclean: clean
	rm -f $(MAIN).pdf
```

Then compile with:
```bash
cd paper/
make
```

### Watch Mode (for Development)

If you have `latexmk` installed:

```bash
cd paper/
latexmk -pdf -pvc main_integrated.tex
```

This will automatically recompile when you save changes.

## Troubleshooting

### Missing Packages

If you get errors about missing packages, install them:

**Ubuntu/Debian:**
```bash
sudo apt-get install texlive-latex-extra texlive-fonts-extra
```

**MiKTeX (Windows):**
Packages are installed automatically on first use.

### Bibliography Issues

If citations show as `[?]`:
1. Make sure you ran `bibtex` after the first `pdflatex`
2. Run `pdflatex` at least twice more after `bibtex`
3. Check that `biblio.bib` is in the same directory

### Encoding Problems

If you see strange characters, ensure your editor saves files as UTF-8.

## Output Files

After successful compilation, you'll have:
- `main_integrated.pdf` - The final PDF document
- `main_integrated.aux` - Auxiliary file (can be deleted)
- `main_integrated.log` - Compilation log (useful for debugging)
- `main_integrated.bbl` - Bibliography file (generated from .bib)
- `main_integrated.blg` - Bibliography log
- `main_integrated.out` - Hyperref information
- `main_integrated.toc` - Table of contents (if enabled)

## Current Status

✅ **Compilable Structure**: The skeleton is ready to compile
⚠️ **Placeholder Content**: Sections 4-12 and Appendices A-F contain placeholders

The first three sections (Introduction, Preliminaries, Local Length) contain full mathematical content and should compile without errors.

## Testing Compilation

To test if everything is set up correctly:

```bash
cd paper/
pdflatex -interaction=nonstopmode main_integrated.tex
```

If there are no errors, you should see output ending with:
```
Output written on main_integrated.pdf (X pages, YYYY bytes).
```

## Tips

1. **Incremental Compilation**: While writing, you can comment out sections you're not working on to speed up compilation.

2. **Version Control**: Consider using git to track changes to your LaTeX source.

3. **Backup**: Keep backups of your work, especially before major changes.

4. **Collaboration**: Use tools like Overleaf if collaborating with others.

## Next Steps

Once you've verified compilation works:
1. Fill in the placeholder sections (04-12)
2. Complete the appendices (A-F)
3. Add figures and tables as needed
4. Run final compilation with all content
5. Proofread the generated PDF
