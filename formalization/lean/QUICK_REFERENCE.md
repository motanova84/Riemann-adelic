# Lean Formalization Quick Reference

## 🚀 Quick Start (5 minutes)

```bash
# 1. Validate structure
python3 validate_lean_formalization.py

# 2. Install Lean (first time only)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
export PATH="$HOME/.elan/bin:$PATH"

# 3. Build the project
cd formalization/lean
lake update
lake build
```

## 📊 Current Status

| Metric | Value | Status |
|--------|-------|--------|
| **Modules** | 15 | ✅ All integrated |
| **Theorems** | 104 | ✅ |
| **Axioms** | 26 | ⚠️ Being reduced |
| **Sorries** | 88 | 🔄 15.5% complete |
| **Structure** | Valid | ✅ |

## 🎯 Priority Work Items

### High Priority (Complete First)
1. **`D_explicit.lean`** - 9 sorries
   - Spectral trace computation
   - Growth bounds
   - Functional equation proof

2. **`positivity.lean`** - 8 sorries
   - Trace class operator proofs
   - Eigenvalue bounds
   - Positive kernel construction

3. **`de_branges.lean`** - 7 sorries
   - Hilbert space structure
   - Growth conditions
   - Inner product properties

### Medium Priority
4. **`schwartz_adelic.lean`** - 6 sorries
5. **`entire_order.lean`** - 5 sorries
6. **`poisson_radon_symmetry.lean`** - 5 sorries

### Lower Priority
7. **`zero_localization.lean`** - 13 sorries (can be deferred)
8. **`pw_two_lines.lean`** - 11 sorries (supporting theory)
9. **`lengths_derived.lean`** - 7 sorries (auxiliary)

## 🛠️ Common Tasks

### Check a Single File
```bash
cd formalization/lean
lean RiemannAdelic/D_explicit.lean
```

### Build Specific Module
```bash
lake build RiemannAdelic.D_explicit
```

### Find All Sorries
```bash
grep -r "sorry" RiemannAdelic/ --include="*.lean"
```

### Count Progress
```bash
# Total sorries
grep -ro "sorry" RiemannAdelic/ --include="*.lean" | wc -l

# Sorries in specific file
grep -o "sorry" RiemannAdelic/D_explicit.lean | wc -l
```

## 📝 Proof Writing Tips

### Replace a Sorry

**Before:**
```lean
theorem my_theorem : P → Q := by
  sorry
```

**After:**
```lean
theorem my_theorem : P → Q := by
  intro h_P
  -- Use existing lemmas
  have h_intermediate := some_lemma h_P
  -- Apply tactics
  apply another_lemma
  exact h_intermediate
```

### Common Tactics
- `intro` - Introduce hypothesis
- `apply` - Apply a theorem
- `exact` - Provide exact proof term
- `have` - Intermediate result
- `simp` - Simplify using simp lemmas
- `ring` - Solve ring equations
- `linarith` - Linear arithmetic
- `sorry` - Placeholder (temporary!)

### Structure of a Proof
```lean
theorem name : statement := by
  -- 1. Introduce variables/hypotheses
  intro x y h
  
  -- 2. Unfold definitions if needed
  unfold my_def
  
  -- 3. Build intermediate results
  have h1 := lemma1 x
  have h2 := lemma2 y h
  
  -- 4. Apply main result
  apply main_theorem
  
  -- 5. Finish subgoals
  · exact h1
  · exact h2
```

## 🔍 Finding What You Need

### Find Definition
```bash
grep -r "def D_explicit" RiemannAdelic/
```

### Find Theorem
```bash
grep -r "theorem.*functional_equation" RiemannAdelic/
```

### Find Axioms
```bash
grep -r "axiom" RiemannAdelic/ --include="*.lean"
```

### View File Structure
```bash
# List all definitions, theorems, lemmas
grep -n "^\(def\|theorem\|lemma\|axiom\)" RiemannAdelic/D_explicit.lean
```

## 📚 Learning Resources

### Essential Reading
1. **Theorem Proving in Lean 4**: https://leanprover.github.io/theorem_proving_in_lean4/
2. **Mathlib4 Docs**: https://leanprover-community.github.io/mathlib4_docs/
3. **Natural Number Game**: https://adam.math.hhu.de/#/g/leanprover-community/NNG4

### Getting Help
- **Zulip Chat**: https://leanprover.zulipchat.com/ (#new members)
- **Project Issues**: https://github.com/motanova84/-jmmotaburr-riemann-adelic/issues
- **Documentation**: See `formalization/lean/SETUP_GUIDE.md`

## 🎓 Module-Specific Notes

### `D_explicit.lean`
- **Purpose**: Constructive definition of D(s) via spectral trace
- **Key definition**: `def D_explicit (s : ℂ) : ℂ := spectralTrace s`
- **Main theorem**: `D_explicit_functional_equation`
- **Dependencies**: `schwartz_adelic.lean`

### `de_branges.lean`
- **Purpose**: de Branges space theory for RH
- **Key structure**: `DeBrangesSpace`
- **Main theorem**: `D_in_de_branges_space_implies_RH`
- **Critical**: Growth bounds and inner product

### `positivity.lean`
- **Purpose**: Weil-Guinand positivity theory
- **Key structure**: `PositiveKernel`, `TraceClassOperator`
- **Main theorem**: `main_positivity_theorem`
- **Critical**: Eigenvalue bounds

### `axioms_to_lemmas.lean`
- **Status**: ✅ Complete (0 sorries)
- **Purpose**: Toy model proofs
- **Proven**: A1, A2, A4 lemmas

## 🔧 Troubleshooting

### "unknown identifier"
- Check imports at top of file
- Ensure module is built: `lake build Module.Name`

### "type mismatch"
- Use `#check` to inspect types
- Check that implicit arguments are correct

### "tactic failed"
- Break proof into smaller steps with `have`
- Use `sorry` temporarily to check later parts

### Build takes forever
- Use mathlib cache: `lake exe cache get`
- Build specific modules instead of all
- Set `LEAN_JOBS=1` to use less memory

## 🎯 Next Steps

### This Week
1. Run validation: `python3 validate_lean_formalization.py`
2. Pick a file with few sorries (e.g., `arch_factor.lean` ✅ complete)
3. Study one complete proof
4. Try filling in one sorry in a familiar module

### This Month
1. Complete `D_explicit.lean` proofs
2. Finish `schwartz_adelic.lean` 
3. Make progress on `de_branges.lean`
4. Reduce total sorries by 50%

### This Quarter
1. All high-priority modules complete
2. Axiom count reduced to <10
3. Completeness >50%
4. Full compilation without warnings

## 📊 Track Your Progress

```bash
# Before you start
BEFORE=$(grep -ro "sorry" RiemannAdelic/ --include="*.lean" | wc -l)
echo "Starting sorries: $BEFORE"

# ... work on proofs ...

# After your session
AFTER=$(grep -ro "sorry" RiemannAdelic/ --include="*.lean" | wc -l)
echo "Remaining sorries: $AFTER"
echo "Fixed: $(($BEFORE - $AFTER))"
```

## 🏆 Recognition

Every completed proof matters! Contributors who eliminate sorries will be:
- Listed in `FORMALIZATION_STATUS.md`
- Mentioned in commit messages
- Recognized in the final publication

---

**Ready to contribute?** Start with the [SETUP_GUIDE.md](formalization/lean/SETUP_GUIDE.md)!

**Questions?** Open an issue or check the [Lean Zulip](https://leanprover.zulipchat.com/)

**Last Updated**: October 22, 2025  
**Maintainer**: José Manuel Mota Burruezo
