from gwpy.detector import Interferometer

def compute_antenna_ratio(freq, ra, dec, psi):
    H1 = Interferometer('H1')
    L1 = Interferometer('L1')
    t = 1126259462  # GPS time for GW150914
    f_plus_H1, f_cross_H1 = H1.antenna_response(ra, dec, psi, t)
    f_plus_L1, f_cross_L1 = L1.antenna_response(ra, dec, psi, t)

    # Combine responses as RMS average
    resp_H1 = (f_plus_H1**2 + f_cross_H1**2)**0.5
    resp_L1 = (f_plus_L1**2 + f_cross_L1**2)**0.5
    return resp_H1 / resp_L1 if resp_L1 != 0 else float('inf')
