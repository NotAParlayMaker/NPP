import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3481_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma run_keeps (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ h

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = w.length + (g :: gs).length
    rw [ih]
    simp [step]
    omega

lemma wires_length (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.size :=
  run_length C.gates w

lemma eval_input (C : Circuit) (w : List Bool) (h : C.output < w.length) :
    C.eval w = w.getD C.output false :=
  run_keeps C.gates w C.output h

lemma eval_outside (C : Circuit) (w : List Bool)
    (h : w.length + C.size ≤ C.output) : C.eval w = false := by
  unfold Circuit.eval
  apply List.getD_eq_default
  simpa only [wires_length] using h

end PEqualNP.Outside.L_meta_3481_aux

theorem PEqualNP.Outside.L_meta_3481 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ¬x3.Adj x6 x7 → (2 : ℕ) ≤ (x3.neighborSet x6).ncard → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → ∃ (x12 : Fin x1), ¬(x3.Adj x6 x12 ↔ x3.Adj x7 x12)) → (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → (2 : ℕ) ≤ (x3.neighborSet x8).ncard → ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x7 x12 ∧ x12 ≠ x8 ∧ x3.Adj x8 x13 ∧ x13 ≠ x7 ∧ (x12 = x13 ∨ ¬x3.Adj x12 x13)) → (∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → (2 : ℕ) ≤ (x3.neighborSet x9).ncard → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x8.card = x2) → (∀ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → (2 : ℕ) ≤ (x3.neighborSet x11).ncard → x10 ∈ x9 ∨ x11 ∈ x9) → x2 ≤ x9.card) → PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 ∨ x1 + x4.size ≤ x4.output → (∀ (x12 x13 : Fin x1), x4.eval (List.ofFn fun (x14 : Fin x1) => Decidable.decide (x14 = x12 ∨ x14 = x13)) = Bool.true ↔ x3.Adj x12 x13) → x1 + x2 ≤ x4.size + (1 : ℕ) := by
  intro n k G C noiso _ _ _ minimum _ hout correct
  by_cases hn : n = 0
  · subst n
    have hk := minimum ∅ (by intro i; exact Fin.elim0 i)
    simp only [Finset.card_empty] at hk
    omega
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    rcases hout with hin | hout
    · let v : Fin n := ⟨C.output, hin⟩
      let z : Fin n → Bool := fun i => decide (i = v ∨ i = v)
      have hz : C.eval (List.ofFn z) = true := by
        rw [PEqualNP.Outside.L_meta_3481_aux.eval_input C (List.ofFn z)
          (by simpa using hin)]
        simp [z, v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin]
      have hadj := (correct v v).mp hz
      simp at hadj
    · let v : Fin n := ⟨0, hpos⟩
      obtain ⟨u, ha⟩ := noiso v
      have hf := PEqualNP.Outside.L_meta_3481_aux.eval_outside C
        (List.ofFn fun i : Fin n => decide (i = v ∨ i = u))
        (by simpa using hout)
      have ht := (correct v u).mpr ha
      rw [hf] at ht
      contradiction
