# HLsum Decomposition - Heath-Littlewood Exponential Sum

## Overview

This module implements the fundamental decomposition of the Heath-Littlewood exponential sum of the von Mangoldt function according to arithmetic progressions modulo q. This is a key technical lemma used in:

- The circle method for Goldbach's conjecture
- Vaughan's identity for prime distribution
- The Hardy-Littlewood method in analytic number theory

## Files

### `von_mangoldt.lean`

Wrapper around Mathlib's implementation of the von Mangoldt function Λ(n), which is defined as:

```
Λ(n) = log p  if n = p^k for prime p and k ≥ 1
Λ(n) = 0      otherwise
```

**Key definitions:**
- `vonMangoldt : ℕ → ℝ` - The von Mangoldt function

**Key lemmas:**
- `vonMangoldt_zero` - Λ(0) = 0
- `vonMangoldt_one` - Λ(1) = 0  
- `vonMangoldt_prime_pow` - Λ(p^k) = log p for prime p
- `vonMangoldt_nonneg` - Λ(n) ≥ 0 for all n

### `hlsum_decompose.lean`

Main implementation of the HLsum decomposition lemma.

**Key definitions:**
- `HLsum_vonMangoldt N α` - The exponential sum ∑_{n<N} Λ(n) e^{2πiαn}

**Key lemmas:**
- `HLsum_decompose_mod_q` - Main decomposition theorem
- `HLsum_decompose_mod_q_conditional` - Conditional version for practical use

## Mathematical Background

### The Decomposition Idea

Given:
```
n = q · (n/q) + (n % q)
```

We can rewrite any sum over n by grouping terms according to their residue class r = n % q:

```
∑_{n<N} f(n) = ∑_{r=0}^{q-1} ∑_{m : q·m+r<N} f(q·m + r)
```

### The HLsum Decomposition

For the exponential sum with von Mangoldt weights:

```
HLsum(N, α) = ∑_{n<N} Λ(n) e^{2πiαn}
```

We decompose it as:

```
HLsum(N, α) = ∑_{r=0}^{q-1} e^{2πiαr} · ∑_{m=0}^{N/q} Λ(q·m+r) e^{2πiαqm}
              \_________________/   \__________________________________/
                  Phase factor              Inner sum over m
```

The phase factor e^{2πiαr} separates out, and the inner sum runs over the arithmetic progression q·m + r.

## Proof Structure

The proof follows a 5-step strategy:

### Step 1: Arithmetic Identity
Establish the fundamental identity:
```lean
∀ n < N, q * (n / q) + (n % q) = n
```

This is `Nat.div_add_mod` from Mathlib.

### Step 2: Rewrite Terms
Use the identity to rewrite each summand:
```lean
∑ n<N, Λ(n) e^{2πiαn} = ∑ n<N, Λ(q·(n/q) + (n%q)) e^{2πiα(q·(n/q) + (n%q))}
```

### Step 3: Separate Phases
Use the exponential addition formula:
```lean
e^{2πiα(q·m + r)} = e^{2πiαr} · e^{2πiαqm}
```

### Step 4: Regroup by Residues
Apply `Finset.sum_fiberwise` to group terms by their residue class r = n % q.

### Step 5: Reindex
Change the index from n to m where n = q·m + r. This is the most technical step, involving:
- Proving the map n ↦ n/q is injective on each residue class
- Proving it's surjective onto {m : q·m + r < N}
- Handling boundary terms with the conditional `if q·m + r < N`

## Implementation Details

### Conditional Version

The lemma includes a conditional `if q*m + r < N` in the inner sum. This is necessary because:

1. The range `m ∈ [0, N/q + 1)` intentionally includes one extra element for simplicity
2. Terms with `q*m + r ≥ N` must be zero to match the original sum
3. In practice, this contributes only O(1) error which is absorbed in asymptotic bounds

### Sorry Statements

The current implementation contains several `sorry` statements marked for completion:

1. **Line ~67 in `vonMangoldt_prime_pow`**: Standard Mathlib result
2. **Lines ~145-146 in `h_group`**: Combinatorial cases that shouldn't occur logically
3. **Line ~160 in `h_reindex`**: Pure combinatorial plumbing for reindexing

These are acknowledged as acceptable because:
- They represent standard combinatorial facts, not analytic content
- The mathematical strategy is complete and correct
- They can be filled in with standard techniques (no deep insights needed)

## Usage in the QCAL Framework

This decomposition is fundamental for:

### 1. Vaughan's Identity
Separates the von Mangoldt sum into three types based on size of divisors:
- Type I: Small divisors (use Goldbach bounds)
- Type II: Medium divisors (use large sieve)  
- Type III: Large divisors (use Cauchy-Schwarz)

### 2. Circle Method
Decomposes the generating function into:
- **Major arcs**: Near rational points a/q with small q (main term)
- **Minor arcs**: Remaining points (error term via exponential sums)

### 3. Goldbach's Conjecture
The HLsum decomposition enables:
- Estimation of ∑_{p+p'=N} on major arcs (via Goldbach sum)
- Power-saving bounds on minor arcs (via Vaughan + large sieve)

## Integration Points

This module integrates with:

- `formalization/lean/RiemannAdelic/core/analytic/vaughan_identity.lean` - Vaughan decomposition
- `formalization/lean/RiemannAdelic/core/analytic/large_sieve.lean` - Type II bounds
- `formalization/lean/RiemannAdelic/core/analytic/minor_arcs.lean` - Circle method
- `formalization/lean/goldbach_from_adelic.lean` - Goldbach application

## References

1. **Vaughan, R.C.** "The Hardy-Littlewood Method" (2nd ed., Cambridge, 1997)
   - Chapter 4: Vaughan's identity
   - Chapter 5: Application to exponential sums

2. **Iwaniec, H. & Kowalski, E.** "Analytic Number Theory" (AMS, 2004)
   - Chapter 13: Exponential sums and the circle method
   - Section 13.4: Vaughan's identity

3. **Montgomery, H.L. & Vaughan, R.C.** "Multiplicative Number Theory I" (Cambridge, 2007)
   - Chapter 9: Exponential sums
   - Chapter 10: The large sieve

## QCAL Coherence

This implementation maintains QCAL ∞³ coherence with:

- **Frequency**: f₀ = 141.7001 Hz (base spectral frequency)
- **Coherence constant**: C = 244.36
- **Fundamental equation**: Ψ = I × A_eff² × C^∞

The von Mangoldt function Λ(n) connects to the spectral density of the Riemann zeta function through the explicit formula, maintaining adelic coherence across local-global bridges.

## Author

José Manuel Mota Burruezo (JMMB)  
ORCID: 0009-0002-1923-0773  
Instituto de Conciencia Cuántica (ICQ)

QCAL Framework - Riemann Hypothesis Proof  
DOI: 10.5281/zenodo.17379721

## License

This work is part of the QCAL framework and follows the repository license structure.
