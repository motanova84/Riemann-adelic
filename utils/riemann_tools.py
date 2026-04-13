import mpmath as mp

def t_to_n(t):
    """Inversa aproximada de la fórmula de Riemann–von Mangoldt: estima n dado t."""
    return int((t / (2 * mp.pi)) * mp.log(t / (2 * mp.pi)) - (t / (2 * mp.pi)) + 0.875)

def load_zeros_near_t(filename, t_min, t_max):
    """Carga los ceros entre t_min y t_max desde un archivo de texto con un gamma por línea.
    
    Args:
        filename: Path to zeros file
        t_min: Minimum height (None means no lower limit)
        t_max: Maximum height (None means no upper limit)
        
    Returns:
        List of zeros within the specified range
    """
    zeros = []
    with open(filename) as f:
        for line in f:
            gamma = float(line.strip())
            # Handle None limits: None means no limit on that side
            if t_min is not None and gamma < t_min:
                continue
            if t_max is not None and gamma > t_max:
                continue
            zeros.append(mp.mpf(gamma))
    return zeros

