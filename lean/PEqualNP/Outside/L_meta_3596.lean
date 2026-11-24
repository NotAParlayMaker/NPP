import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3596

open PEqualNP.CircuitLowerBounds

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem eval_input (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := by
  unfold Circuit.eval Circuit.wires
  exact fold_pre _ _ _ h

end PEqualNP.Outside.L_meta_3596

theorem PEqualNP.Outside.L_meta_3596 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I _ C hq _ _ _ _ hout _ _ hsound
  exfalso
  let z : Fin (N + N) → Bool := fun k => decide (k.val = C.output)
  have hcard : Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q := by
    have : Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro a b
      apply Subtype.ext
      have ha := a.2
      have hb := b.2
      simp only [z, Fin.natAdd, decide_eq_true_eq] at ha hb
      exact Fin.ext (by omega)
    omega
  have hni : ¬ ∃ (p : Fin N) (l : Fin N), I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    rintro ⟨p, l, _, hp, hl⟩
    simp only [z, Fin.castAdd, Fin.natAdd, decide_eq_true_eq, Fin.val_castLE] at hp hl
    have := p.isLt
    omega
  have h := hsound z hcard hni
  unfold PEqualNP.MetaComplexity.circuitFun at h
  rw [PEqualNP.Outside.L_meta_3596.eval_input C _ (by simpa using hout)] at h
  rw [List.getD_eq_getElem _ _ (by simpa using hout), List.getElem_ofFn] at h
  simp [z] at h
