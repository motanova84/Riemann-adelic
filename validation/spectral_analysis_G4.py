# spectral_analysis_G4.py
# Author: José Manuel Mota Burruezo (JMMB Ψ✧)
# Description: Spectral analysis of the 4×4 expander G₄ used in Lean formalization
# License: CC-BY-4.0

import numpy as np
import matplotlib.pyplot as plt

# Adjacency matrix of G₄ (handcrafted expander)
A = np.array([
    [0, 1, 1, 0],
    [1, 0, 1, 1],
    [1, 1, 0, 1],
    [0, 1, 1, 0]
], dtype=float)

# Compute eigenvalues (for symmetric matrices, eigvalsh is recommended)
eigenvalues = np.linalg.eigvalsh(A)
eigenvalues_sorted = np.sort(eigenvalues)[::-1]

# Spectral gap: λ₁ − λ₂
spectral_gap = eigenvalues_sorted[0] - eigenvalues_sorted[1]

# Print results
print("Eigenvalues (sorted):", eigenvalues_sorted)
print("Spectral gap Δ = λ₁ − λ₂ =", spectral_gap)

# Plot spectrum
plt.figure(figsize=(6, 4))
plt.plot(eigenvalues_sorted, 'o-', label='Eigenvalues')
plt.axhline(2, color='red', linestyle='--', label='Ramanujan bound (2√(d−1))')
plt.title("Spectrum of G₄ (4×4 Expander)")
plt.xlabel("Index")
plt.ylabel("Eigenvalue")
plt.grid(True)
plt.legend()
plt.tight_layout()
plt.savefig("G4_spectrum_plot.png")
plt.show()
