import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4823 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → (0 : ℕ) < x1 + x2.size → (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset = Finset.range (x1 + x2.size - (1 : ℕ)) → x1 + ((List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card) = x2.size + (1 : ℕ) := by
  intro x1 x2 hAO hpos hfin
  have htwo : ∀ g ∈ x2.gates, g.inputs.length = 2 := hAO.2.2
  have sum_two : ∀ (l : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ l, g.inputs.length = 2) →
      (l.map (fun g => g.inputs.length)).sum = 2 * l.length := by
    intro l hl
    induction l with
    | nil => simp
    | cons g gs ih =>
        have hg : g.inputs.length = 2 := hl g (by simp)
        have hgs : ∀ h ∈ gs, h.inputs.length = 2 := by
          intro h hh
          exact hl h (by simp [hh])
        simp [hg, ih hgs, Nat.mul_succ]
        omega
  have hlen : (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length = 2 * x2.size := by
    simp [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_flatMap, sum_two x2.gates htwo]
  have hcard : (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card = x1 + x2.size - 1 := by
    rw [hfin, Finset.card_range]
  have hle : x1 + x2.size - 1 ≤ 2 * x2.size := by
    rw [← hcard, ← hlen]
    exact List.toFinset_card_le _
  omega
