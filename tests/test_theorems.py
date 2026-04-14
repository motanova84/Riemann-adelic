import subprocess


def run(cmd):
    return subprocess.run(cmd, shell=True, check=True, capture_output=True, text=True)


def test_functional_symmetry_holds():
    out = run("python proof-check/check_functional_equation.py").stdout
    max_err = float(out.strip().split(":")[-1])
    assert max_err < 1e-40


def test_vertical_growth_bound_runs():
    out = run("python proof-check/check_growth.py").stdout
    assert "Max |D(2+it)|" in out


def test_positive_form_runs():
    out = run("python proof-check/check_positive_form.py").stdout
    assert "Q[f]" in out
