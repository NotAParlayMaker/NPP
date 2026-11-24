import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4823 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → (0 : ℕ) < x1 + x2.size → (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset = Finset.range (x1 + x2.size - (1 : ℕ)) → x1 + ((List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card) = x2.size + (1 : ℕ) := by
  intro n C hAO hpos hset
  have key : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
      (∀ g ∈ gs, g.inputs.length = 2) →
      (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length = 2 * gs.length := by
    intro gs
    induction gs with
    | nil => intro _; simp
    | cons g gs ih =>
      intro h
      rw [List.flatMap_cons, List.length_append, h g (by simp),
        ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')), List.length_cons]
      ring
  have hlen := key C.gates hAO.2.2
  have hle := List.toFinset_card_le (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates)
  have hsz : C.size = C.gates.length := rfl
  rw [hset, Finset.card_range] at hle ⊢
  rw [hlen]
  rw [hlen] at hle
  omega
