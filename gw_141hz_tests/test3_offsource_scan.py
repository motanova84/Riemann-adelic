from gw_141hz_tools.offsource import scan_offsource_peaks

if __name__ == "__main__":
    snr_list = scan_offsource_peaks(freq=141.7, n_days=10)
    print("Off-source peak SNRs at 141.7 Hz:")
    for i, snr in enumerate(snr_list, 1):
        print(f"  Day -{i}: SNR ≈ {snr:.2f}")
