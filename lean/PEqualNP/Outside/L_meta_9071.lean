import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9071_aux

open PEqualNP.CircuitLowerBounds

theorem pre (gs : List Gate) : ∀ w : List Bool,
    w <+: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    exact (List.prefix_append _ _).trans (ih _)

theorem wire_in (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := by
  unfold Circuit.eval Circuit.wires
  obtain ⟨t, ht⟩ := pre C.gates x
  rw [← ht]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

end PEqualNP.Outside.L_meta_9071_aux

open PEqualNP.Outside.L_meta_9071_aux in
theorem PEqualNP.Outside.L_meta_9071 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (26 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → (59 : ℕ) ≤ x1.size := by
  intro C ho _ hf
  have hl : C.output < (List.ofFn (fun j : Fin 26 => decide (j.val = C.output))).length := by
    simpa using ho
  have he := wire_in C _ hl
  have ht : C.eval (List.ofFn (fun j : Fin 26 => decide (j.val = C.output))) = true := by
    rw [he]
    generalize hk : C.output = k at ho ⊢
    interval_cases k <;> rfl
  obtain ⟨a, b, _, _, h1, h2⟩ := (hf _).mp ht
  simp at h1 h2
  exact absurd (h1.trans h2.symm) (by have := a.isLt; omega)
