# Mathematical Analysis: Spectral Counting Coefficient Fix

## Issue

Current implementation gives:
- I(λ) ~ (some value)
- N(λ) = I(λ)/π - 1/4

But theoretical expectation is:
- N(λ) ~ (λ/2π) log λ - (λ/2π)

The mismatch factor is approximately 2.5x.

## WKB Theory Review

For a 1D Schrödinger operator -d²/dy² + Q(y) with potential Q(y), the WKB phase integral is:

I(λ) = ∫₀^{y₊(λ)} √(λ - Q(y)) dy

The Levinson formula relates this to eigenvalue count:

N(λ) = (1/π) I(λ) + phase_corrections

## Coefficient Analysis

For Q(y) = (π⁴/16) y²/[log(1+y)]², we have:

At large y: Q(y) ~ (π⁴/16) y²/(log y)²

The turning point satisfies:
(π⁴/16) y₊²/(log y₊)² = λ
⟹ y₊ ~ √(16λ/π⁴) log y₊
⟹ y₊ ~ (4/π²)√λ log y₊

For WKB integral asymptotic expansion:
I(λ) ~ integral of √(λ - (π⁴/16)y²/(log y)²) from 0 to y₊

This needs careful asymptotic analysis using:
1. Integration by parts
2. Stationary phase approximation
3. Logarithmic corrections

## Hypothesis

The coefficient (π⁴/16) might need adjustment to match Riemann counting exactly.

Alternative: The Levinson phase correction -1/(4π) might need different value.

## Resolution Strategy

1. Check Berry-Keating potential Q(y) = y² case as reference
2. Verify if logarithmic correction in denominator introduces extra factor
3. Consider if correspondence λₙ ↔ γₙ² needs rescaling
4. Review literature on spectral counting for logarithmically perturbed potentials

## Next Steps

- Implement adjustable coefficient in Q(y) = α · y²/[log(1+y)]²
- Fit α to match theoretical count
- Document empirical vs theoretical relationship
