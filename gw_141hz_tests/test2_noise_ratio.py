from gw_141hz_tools.noise import compute_noise_ratio

if __name__ == "__main__":
    ratio = compute_noise_ratio(event="GW150914", freq=141.7)
    print(f"Noise ratio (L1/H1) at 141.7 Hz: {ratio:.2f}")
