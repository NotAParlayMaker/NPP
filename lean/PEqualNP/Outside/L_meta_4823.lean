import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4823

lemma flatLen (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length = 2) :
    (List.flatMap Gate.inputs gs).length = 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.flatMap_cons, List.length_append, ih (fun x hx => h x (by simp [hx])),
      h g (by simp), List.length_cons]
    ring

end PEqualNP.Outside.L_meta_4823

open PEqualNP.Outside.L_meta_4823 in
theorem PEqualNP.Outside.L_meta_4823 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → (0 : ℕ) < x1 + x2.size → (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset = Finset.range (x1 + x2.size - (1 : ℕ)) → x1 + ((List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card) = x2.size + (1 : ℕ) := by
  intro n C hAO hpos hset
  obtain ⟨-, -, h2⟩ := hAO
  have hlen : (List.flatMap Gate.inputs C.gates).length = 2 * C.size := by
    rw [flatLen C.gates h2]
    simp only [Circuit.size]
  have hcard : (List.flatMap Gate.inputs C.gates).toFinset.card = n + C.size - 1 := by
    rw [hset]
    simp
  have hle : (List.flatMap Gate.inputs C.gates).toFinset.card ≤ (List.flatMap Gate.inputs C.gates).length :=
    List.toFinset_card_le _
  omega
