import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4823 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → (0 : ℕ) < x1 + x2.size → (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset = Finset.range (x1 + x2.size - (1 : ℕ)) → x1 + ((List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card) = x2.size + (1 : ℕ) := by
  intro x1 x2 hAO hpos hset
  have hlen_aux : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
      (∀ g ∈ gs, g.inputs.length = 2) →
      (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs gs).length = 2 * gs.length := by
    intro gs
    induction gs with
    | nil => intro _; simp
    | cons g gs ih =>
      intro h2
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hg : g.inputs.length = 2 := h2 g (List.mem_cons.mpr (Or.inl rfl))
      have hgs : ∀ g' ∈ gs, g'.inputs.length = 2 := fun g' hg' => h2 g' (List.mem_cons.mpr (Or.inr hg'))
      have := ih hgs
      omega
  have hlen : (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length = 2 * x2.size :=
    hlen_aux x2.gates hAO.2.2
  have hcard : (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card = x1 + x2.size - 1 := by
    rw [hset, Finset.card_range]
  have hle : (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card ≤
      (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length :=
    List.toFinset_card_le _
  omega
