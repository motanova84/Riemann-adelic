import numpy as np

def K_D(x, y, zeros, t=1e-2):
    """
    Kernel K_D(x,y) construido a partir de los ceros de D(s).
    Regularizado con parámetro t (ventana gaussiana).
    
    Args:
        x: Point x
        y: Point y
        zeros: List of zeros (complex numbers)
        t: Regularization parameter (default: 1e-2)
        
    Returns:
        Complex kernel value K_D(x,y)
    """
    s = np.array(zeros)
    return np.sum(np.exp(-t * np.abs(s)**2) * np.exp(1j * s * (np.log(x) - np.log(y))))

def prime_measure_from_zeros(zeros, X, t=1e-2):
    """
    Reconstruye aproximación de la medida de primos desde ceros.
    
    Args:
        zeros: Lista de ceros (complejos)
        X: Array de valores log(n) donde evaluar
        t: Regularization parameter (default: 1e-2)
        
    Returns:
        Array with reconstructed prime measure
    """
    return np.array([K_D(np.exp(x), 1.0, zeros, t) for x in X])
