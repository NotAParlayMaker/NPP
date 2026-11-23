import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

/-- The quantum nullity of a quantum operator `f : V →ₗ[ℂ] V` on a finite-dimensional complex
space: the dimension of the kernel of `f` — the space of input states that are mapped to the
zero state. -/
def QuantumNullity {V : Type} [Module ℂ V] (f : V →ₗ[ℂ] V) : ℕ :=
  finrank ℂ (LinearMap.ker f)

/-- Rank–nullity for a quantum operator: `finrank V = finrank (range f) + QuantumNullity f`. -/
theorem L_quantum_nullity_rank {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) :
    finrank ℂ (LinearMap.range f) + QuantumNullity f = finrank ℂ V := by
  rw [QuantumNullity]
  exact LinearMap.finrank_range_add_finrank_ker f

end PEqualNP.Outside
