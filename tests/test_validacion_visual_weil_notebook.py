
import json
import subprocess
from pathlib import Path
import sys


def test_validacion_visual_weil_notebook_is_executable():
    notebook_path = Path(__file__).resolve().parent.parent / 'notebooks' / 'validacion_visual_weil.ipynb'
    notebook = json.loads(notebook_path.read_text(encoding='utf-8'))

    kernelspec = notebook.get('metadata', {}).get('kernelspec', {})
    assert kernelspec.get('name') == 'python3'

    code_cells = [cell for cell in notebook.get('cells', []) if cell.get('cell_type') == 'code']
    assert code_cells, 'Expected at least one code cell in the validation notebook'

    for cell in code_cells:
        source = ''.join(cell.get('source', []))
        compile(source, str(notebook_path), 'exec')


def test_validate_explicit_formula_help_lists_weil_flag():
    repo_root = Path(__file__).resolve().parent.parent
    result = subprocess.run(
        [sys.executable, str(repo_root / 'validate_explicit_formula.py'), '--help'],
        check=True,
        capture_output=True,
        text=True,
    )

    assert '--use_weil_formula' in result.stdout
