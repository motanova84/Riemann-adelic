from gw_141hz_tools.antenna import compute_antenna_ratio

if __name__ == "__main__":
    # Parameters for GW150914
    freq = 141.7  # Hz
    ra = 1.95     # Right ascension (rad)
    dec = -1.27   # Declination (rad)
    psi = 0       # Polarization angle (rad)

    expected_ratio = compute_antenna_ratio(freq, ra, dec, psi)
    print(f"Expected antenna pattern ratio H1/L1: {expected_ratio:.3f}")
