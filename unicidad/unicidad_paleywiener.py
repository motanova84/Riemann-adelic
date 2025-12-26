import numpy as np

class PaleyWienerClass:
    """
    Clase de funciones de prueba de Paley–Wiener.
    """
    def __init__(self, bandwidth=10.0):
        """
        Initialize Paley-Wiener class.
        
        Args:
            bandwidth: Bandwidth for test functions (default: 10.0)
        """
        self.bandwidth = bandwidth

    def test_function(self, x):
        """
        Generate a test function (sinc-based band-limited function).
        
        Args:
            x: Point where to evaluate
            
        Returns:
            Test function value at x
        """
        # Ejemplo: sinc normalizada de banda limitada
        return np.sinc(x / self.bandwidth)

def compare_distributions(D1, D2, tests):
    """
    Verifica coincidencia de dos distribuciones de Weil en la clase de pruebas.
    
    Args:
        D1: First distribution (callable)
        D2: Second distribution (callable)
        tests: List of test functions
        
    Returns:
        Boolean indicating if distributions match on all test functions
    """
    for phi in tests:
        if not np.allclose(D1(phi), D2(phi)):
            return False
    return True
