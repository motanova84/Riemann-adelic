/-
  Example Lean file for conversion smoke testing.
  This is a minimal example that demonstrates basic Lean syntax.
-/

namespace RiemannAdelic

-- Simple definition
def example_constant : Nat := 42

-- Basic theorem
theorem example_theorem : 1 + 1 = 2 := by
  rfl

-- Another simple lemma
lemma addition_commutative (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]

end RiemannAdelic
