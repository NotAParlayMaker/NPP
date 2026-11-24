import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

private lemma L_meta_4823_flatMap_inputs_length (l : List Gate)
    (h : ∀ g ∈ l, g.inputs.length = 2) :
    (List.flatMap Gate.inputs l).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons g t ih =>
      have hg : g.inputs.length = 2 := h g (by simp)
      have ht : ∀ a ∈ t, a.inputs.length = 2 := fun a ha => h a (by simp [ha])
      simp only [List.flatMap_cons, List.length_append, List.length_cons, hg, ih ht]
      omega

theorem PEqualNP.Outside.L_meta_4823 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → (0 : ℕ) < x1 + x2.size → (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset = Finset.range (x1 + x2.size - (1 : ℕ)) → x1 + ((List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card) = x2.size + (1 : ℕ) := by
  intro n C _hAO2 _hpos hset
  have hfan : ∀ g ∈ C.gates, g.inputs.length = 2 := _hAO2.2.2
  have hlen : (List.flatMap Gate.inputs C.gates).length = 2 * C.gates.length :=
    L_meta_4823_flatMap_inputs_length C.gates hfan
  have hcard : (List.flatMap Gate.inputs C.gates).toFinset.card = n + C.size - 1 := by
    rw [hset, Finset.card_range]
  have hle : (List.flatMap Gate.inputs C.gates).toFinset.card ≤
      (List.flatMap Gate.inputs C.gates).length := List.toFinset_card_le _
  have hsize : C.size = C.gates.length := rfl
  omega
