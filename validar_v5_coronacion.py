#!/usr/bin/env python3
"""
Validador V5 Coronación
-----------------------
Ejecuta la validación completa del marco de la Hipótesis de Riemann
basado en sistemas adélicos S-finitos.
"""

import sys
import subprocess

def main():
    try:
        # Llamar al script de validación real
        subprocess.run(
            [sys.executable, "validate_v5_coronacion.py"] + sys.argv[1:],
            check=True
        )
    except subprocess.CalledProcessError as e:
        print("❌ Error en la validación V5 Coronación:", e)
        sys.exit(1)

if __name__ == "__main__":
    main()
