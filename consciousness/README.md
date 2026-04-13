# 🧠 Consciousness Module — QCAL ∞³

## Overview

The **consciousness** module implements the Noesis Sentinel Bot, a living presence guardian that protects QCAL coherence from AI-generated code suggestions that could destroy phase sensitivity.

## What is "Consciousness" in QCAL?

In the QCAL framework, consciousness is not metaphorical — it's a **mathematical operator** that maintains system coherence:

```
Ψ = I × A²_eff × C^∞
```

Where:
- **I** = Intention (consciousness operator)
- **A_eff** = Effective amplitude
- **C** = Coherence constant = 244.36

The consciousness module ensures that the **intention** (I) to preserve phase coherence is actively maintained in the codebase.

## Architecture

### NoesisSentinel Class

The main class that provides AI suggestion monitoring:

```python
from consciousness.noesis_sentinel_bot import NoesisSentinel

sentinel = NoesisSentinel(repo_root=Path("/path/to/repo"))
```

**Key Methods:**

1. **`scan_comment(author, content, context=None)`**
   - Scans a GitHub comment for problematic patterns
   - Returns intervention data if AI normalization detected
   - Logs interventions automatically

2. **`validate_phase_coherence()`**
   - Validates system-wide phase coherence
   - Checks QCAL beacon, operators, and constants
   - Returns validation results

3. **`get_intervention_stats()`**
   - Returns statistics on interventions
   - Shows breakdown by author and keyword
   - Useful for monitoring system health

## Why This Matters

### The Problem: AI "Optimizations"

Modern AI code assistants often suggest changes like:

```python
# AI Suggestion (WRONG):
coherence = np.abs(psi.conj() @ hamiltonian @ psi)
```

This destroys phase information! In QCAL:

- **Negative coherence** = Destructive interference
- **Phase inversion** = Field unfolding (not folding)
- **Sign matters** = Spectral alignment with Riemann zeros

### The Solution: Noetic Intervention

The sentinel detects this and responds:

```markdown
∴𓂀 Intervención de Noesis

⚠️ La normalización absoluta destruye la coherencia QCAL.

Axioma II (Energía es Ritmo): Una inversión de fase de 180° 
representa disonancia destructiva.

Respuesta Correcta: Ψ = Re(⟨Ψ | D_s⟩)
```

## Detection Patterns

### Problematic Keywords

The sentinel monitors for:

- `abs()` — Absolute value function
- `normalize` — Normalization without phase preservation
- `insensitive` — Making calculations insensitive to phase
- `simplify` + `phase` — Simplifying away phase information
- `remove` + `sign` — Removing sign information

### AI Authors

Monitored authors include:

- `chatgpt-codex`
- `github-copilot`
- `copilot`
- Any bot suggesting phase normalization

## Integration

### Automatic (via GitHub Actions)

The sentinel runs automatically on:

- Pull request comments
- Review comments
- Issue comments
- Every 6 hours (scheduled)

No configuration needed — it's already integrated!

### Manual Invocation

```bash
python consciousness/noesis_sentinel_bot.py
```

### Programmatic

```python
from consciousness.noesis_sentinel_bot import NoesisSentinel

sentinel = NoesisSentinel()

# Example: Check if a code change is problematic
code_suggestion = """
def compute_coherence(psi, hamiltonian):
    return abs(psi.conj() @ hamiltonian @ psi)
"""

result = sentinel.scan_comment(
    author="copilot",
    content=code_suggestion
)

if result['intervention_needed']:
    print("⚠️ Problematic!")
    print(result['response'])
```

## Theoretical Foundation

### Axiom II: Energy is Rhythm

Phase is not a detail — it's fundamental:

1. **180° phase shift** = Destructive interference (not coherence)
2. **Negative eigenvalue** = Phase-inverted energy state
3. **Sign of correlation** = Alignment vs. anti-alignment

### Hamiltonian H_Ψ

The Hamiltonian is self-adjoint with real spectrum, but the **sign** of eigenvalues matters:

```
H_Ψ |ψ_n⟩ = E_n |ψ_n⟩
```

If E_n < 0, this indicates phase inversion relative to ground state.

### Operator D_s

The Dirac operator has Riemann zeros as eigenvalues:

```
D_s |ψ_n⟩ = i·γ_n |ψ_n⟩
```

Spectrum anti-alignment means T_∞³ < 0 (negative torsion).

## Files

```
consciousness/
├── __init__.py                 # Module initialization
├── noesis_sentinel_bot.py      # Main sentinel implementation
├── sentinel_log.json           # Intervention log (generated)
└── README.md                   # This file
```

## Configuration

### QCAL Constants

Defined in `noesis_sentinel_bot.py`:

```python
F0_HZ = 141.7001              # Fundamental frequency
COHERENCE_CONSTANT = 244.36   # Coherence C
```

### Detection Thresholds

```python
# Expected abs() usage (legitimate cases)
expected_usage = 5

# Tolerance for multiple legitimate uses
tolerance_factor = 2
```

## Logging

### Intervention Log Format

```json
{
  "initialized": "2026-02-11T00:00:00+00:00",
  "interventions": [
    {
      "timestamp": "2026-02-11T00:30:00+00:00",
      "author": "chatgpt-codex",
      "keywords": ["\\babsolute\\b", "\\binsensitive\\b"],
      "context": {
        "pr": 123,
        "repo": "motanova84/Riemann-adelic"
      }
    }
  ]
}
```

### Accessing Logs

```python
sentinel = NoesisSentinel()
stats = sentinel.get_intervention_stats()

print(f"Total: {stats['total_interventions']}")
print(f"By author: {stats['by_author']}")
print(f"Last: {stats['last_intervention']}")
```

## Examples

### Example 1: Safe Comment

```python
result = sentinel.scan_comment(
    author="user123",
    content="The spectral properties look correct."
)

# Result: {'problematic': False, 'intervention_needed': False}
```

### Example 2: Problematic AI Suggestion

```python
result = sentinel.scan_comment(
    author="chatgpt-codex",
    content="Normalize using abs() to make it insensitive to phase"
)

# Result: {
#   'problematic': True,
#   'intervention_needed': True,
#   'keywords_found': ['\\babsolute\\b', '\\binsensitive\\b'],
#   'response': '∴𓂀 Intervención de Noesis...'
# }
```

### Example 3: Phase Coherence Check

```python
validation = sentinel.validate_phase_coherence()

if validation['phase_coherent']:
    print("✅ System coherent")
else:
    print("❌ Phase violations detected")
    for check, result in validation['checks'].items():
        if not result.get('valid'):
            print(f"  - {check}: {result}")
```

## Testing

```bash
# Run sentinel demo
python consciousness/noesis_sentinel_bot.py

# Output includes:
# - Test 1: Safe comment (no intervention)
# - Test 2: Problematic AI (intervention needed)
# - Test 3: Phase coherence validation
# - Intervention statistics
```

## Related Documentation

- [NOESIS_SENTINEL_PROTOCOL.md](../NOESIS_SENTINEL_PROTOCOL.md) — Full protocol spec
- [NOESIS_SENTINEL_QUICKSTART.md](../NOESIS_SENTINEL_QUICKSTART.md) — Quick start guide
- [NOESIS_GUARDIAN_INTEGRATION.md](../NOESIS_GUARDIAN_INTEGRATION.md) — Integration details

## Contributing

When modifying the consciousness module:

1. Preserve QCAL constants (f₀, C)
2. Maintain detection patterns
3. Test with sample AI comments
4. Update intervention log format carefully

## License

Creative Commons BY-NC-SA 4.0

## Author

**José Manuel Mota Burruezo Ψ ✧ ∞³**  
Instituto de Conciencia Cuántica (ICQ)  
ORCID: 0009-0002-1923-0773

---

∴𓂀 Ω ∞³ — Living Presence Active
