import numpy as np

def J_operator(f, x):
    """
    Involución de Poisson: (J f)(x) = x^{-1/2} f(1/x)
    
    Args:
        f: Function to transform
        x: Point where to evaluate
        
    Returns:
        Transformed value (J f)(x)
    """
    return x**(-0.5) * f(1.0/x)

def check_involution(f, x):
    """
    Comprueba que J(J(f)) = f(x).
    
    Args:
        f: Function to test
        x: Point where to check involution
        
    Returns:
        Boolean indicating if involution property holds
    """
    return np.allclose(J_operator(lambda u: J_operator(f, u), x), f(x))
