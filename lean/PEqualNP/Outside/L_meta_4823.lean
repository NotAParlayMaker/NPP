import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4823 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → (0 : ℕ) < x1 + x2.size → (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset = Finset.range (x1 + x2.size - (1 : ℕ)) → x1 + ((List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card) = x2.size + (1 : ℕ) := by
  intro n C hAO hpos hcover
  obtain ⟨_hop, _hrb, hexact⟩ := hAO
  have hL : (C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length = 2 * C.size := by
    have key : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
        (∀ g ∈ gs, g.inputs.length = 2) →
        (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length = 2 * gs.length := by
      intro gs hall
      induction gs with
      | nil => simp
      | cons g rest ih =>
        have hg : g.inputs.length = 2 := hall g (by simp)
        have hr : (rest.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length = 2 * rest.length :=
          ih (fun g' hg' => hall g' (List.mem_cons.2 (Or.inr hg')))
        simp only [List.flatMap_cons, List.length_append, List.length_cons, hg, hr]
        omega
    exact key C.gates hexact
  have hD : (C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).toFinset.card
      = n + C.size - 1 := by
    rw [hcover, Finset.card_range]
  have hle : (C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).toFinset.card
      ≤ (C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length :=
    List.toFinset_card_le _
  omega
