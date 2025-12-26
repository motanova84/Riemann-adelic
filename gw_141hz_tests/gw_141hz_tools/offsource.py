from gwpy.timeseries import TimeSeries

def scan_offsource_peaks(freq, n_days=10):
    base_time = 1126259462
    snr_list = []
    for i in range(1, n_days + 1):
        t0 = base_time - 86400 * i
        ts = TimeSeries.fetch_open_data('H1', t0, t0 + 64, cache=True)
        psd = ts.asd(fftlength=4)
        snr_estimate = 1 / psd.value_at(freq)
        snr_list.append(snr_estimate)
    return snr_list
