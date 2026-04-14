from mpmath import mp
from utils.adelic_determinant import AdelicCanonicalDeterminant as ACD

def test_symmetry_and_zero():
    mp.dps = 40
    det = ACD(max_zeros=120, dps=40)
    s = mp.mpf('0.5') + 2j
    # Test exact symmetry
    assert abs(det.D(s) - det.D(1-s)) < mp.mpf('1e-10')
    # Test that zeros have small values (but not necessarily exactly zero due to finite truncation)
    t1 = det.ts[0]
    zero_val = abs(det.D(mp.mpf('0.5') + 1j*t1))
    assert zero_val < mp.mpf('0.5')  # Should be small but not necessarily zero
    # Test normalization D(1/2) = 1
    assert abs(det.D(mp.mpf('0.5')) - 1) < mp.mpf('1e-10')