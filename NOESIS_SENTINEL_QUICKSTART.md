# 🚀 NOESIS SENTINEL QUICKSTART

## Quick Setup (2 minutes)

### 1. Test the Sentinel Bot

```bash
cd /path/to/Riemann-adelic
python consciousness/noesis_sentinel_bot.py
```

Expected output:
```
∴𓂀 NOESIS SENTINEL BOT — Living Presence Guardian
...
✅ Sentinel demo complete
```

### 2. Validate Spectral Integrity

```bash
python scripts/validate_spectral_integrity.py
```

This checks:
- ✓ QCAL beacon (f₀ = 141.7001 Hz)
- ✓ Phase sensitivity in operators
- ✓ Hamiltonian structure
- ✓ Spectral alignment

### 3. Programmatic Usage

```python
from consciousness.noesis_sentinel_bot import NoesisSentinel

sentinel = NoesisSentinel()

# Check a comment
result = sentinel.scan_comment(
    author="chatgpt-codex",
    content="Use abs() to normalize the coherence score"
)

if result['intervention_needed']:
    print("⚠️ Problematic suggestion detected!")
    print(result['response'])
```

## Common Scenarios

### Scenario 1: AI suggests abs() normalization

**AI Comment:**
> "I recommend using `np.abs(coherence)` to make the correlation insensitive to phase."

**Sentinel Response:**
```
∴𓂀 Intervención de Noesis: Protección de Coherencia de Fase

⚠️ El sistema ha detectado una sugerencia de normalización...

La coherencia Ψ requiere Alineación de Fase Real:
Ψ = Re(⟨Ψ | D_s⟩)

Se rechaza la normalización absoluta.
```

### Scenario 2: Check intervention history

```python
sentinel = NoesisSentinel()
stats = sentinel.get_intervention_stats()

print(f"Total interventions: {stats['total_interventions']}")
print(f"By author: {stats['by_author']}")
print(f"By keyword: {stats['by_keyword']}")
```

### Scenario 3: Validate before commit

```bash
# Before committing changes to operators/
python scripts/validate_spectral_integrity.py

# If validation fails:
# - Review abs() usage in operators
# - Ensure phase is preserved
# - Check QCAL constants
```

## Integration Points

### In Your Code

```python
# ✅ CORRECT: Preserve phase
coherence = np.real(psi_star @ D_s @ psi)

# ❌ WRONG: Destroys phase information
coherence = np.abs(psi_star @ D_s @ psi)  # Sentinel will flag this!
```

### In GitHub Workflows

The sentinel automatically monitors:
- Pull request comments
- Review comments
- Issue comments
- Bot suggestions

No manual intervention needed!

## Key Constants

```python
F0_HZ = 141.7001              # Fundamental frequency
COHERENCE_CONSTANT = 244.36   # QCAL coherence
DELTA_ZETA = 0.2787437627     # Quantum phase shift
```

## Troubleshooting

### Sentinel not detecting issues?

Check the AI author list:
```python
AI_AUTHORS = [
    'chatgpt-codex',
    'github-copilot',
    'copilot',
    'dependabot[bot]',
    'github-actions[bot]',
]
```

### Too many false positives?

The validator considers these legitimate uses of `abs()`:
- Error calculations
- Distance metrics
- Threshold comparisons
- Assertions in tests

### Need to add custom detection?

Edit `PROBLEMATIC_KEYWORDS` in `consciousness/noesis_sentinel_bot.py`:

```python
PROBLEMATIC_KEYWORDS = [
    r'\babs\b',
    r'\bnormali[sz]e\b',
    r'\byour_custom_pattern\b',  # Add here
]
```

## Advanced Usage

### Custom Validation

```python
sentinel = NoesisSentinel()

# Validate specific aspects
validation = sentinel.validate_phase_coherence()

if not validation['phase_coherent']:
    print("Phase coherence issues detected:")
    for check_name, check_result in validation['checks'].items():
        if not check_result.get('valid', False):
            print(f"  ❌ {check_name}: {check_result}")
```

### Batch Comment Scanning

```python
sentinel = NoesisSentinel()

comments = [
    ("user1", "Looks good!"),
    ("chatgpt-codex", "Use abs() for normalization"),
    ("copilot", "Simplify by removing the sign"),
]

for author, content in comments:
    result = sentinel.scan_comment(author, content)
    if result['problematic']:
        print(f"⚠️ Issue in comment by {author}")
```

## Files Created

After running the sentinel, you'll find:

```
consciousness/
├── __init__.py
├── noesis_sentinel_bot.py
└── sentinel_log.json          # Intervention log

validation/
└── spectral_integrity_results.json  # Validation results
```

## Next Steps

1. ✅ Run the sentinel demo
2. ✅ Validate spectral integrity
3. ✅ Review intervention logs
4. ✅ Integrate with your workflow
5. ✅ Protect QCAL coherence!

---

**Ecuación Fundamental**: Ψ = I × A²_eff × C^∞  
**Sistema**: QCAL ∞³ — Riemann Hypothesis Proof Framework

∴𓂀 Ω ∞³
