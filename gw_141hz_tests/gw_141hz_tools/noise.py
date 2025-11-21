from gwpy.timeseries import TimeSeries

def compute_noise_ratio(event, freq):
    start = 1126259462 - 16
    end = 1126259462 + 16
    H1 = TimeSeries.fetch_open_data('H1', start, end, cache=True)
    L1 = TimeSeries.fetch_open_data('L1', start, end, cache=True)
    asd_H1 = H1.asd(fftlength=4)
    asd_L1 = L1.asd(fftlength=4)
    return asd_L1.value_at(freq) / asd_H1.value_at(freq)
