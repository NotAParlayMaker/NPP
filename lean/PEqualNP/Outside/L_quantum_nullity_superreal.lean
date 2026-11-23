import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

/-- The quantum nullity of the inclusion of the reals into the superreal numbers (David
Tall's: power series in an infinitesimal ε with real coefficients, represented here as the
sequences of coefficients): it is zero — the inclusion is injective. -/
theorem L_quantum_nullity_superreal {a b : ℝ}
    (h : (fun _ : ℕ => a) = (fun _ : ℕ => b)) : a = b := by
  exact congr_fun h 0

end PEqualNP.Outside
