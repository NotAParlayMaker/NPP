import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_3481

private lemma append_wires (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, t.length = gs.length ∧
      gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hw⟩ := ih (w ++ [b])
    exact ⟨b :: t, by simp [ht], by simpa only [List.foldl_cons, List.append_assoc,
      List.singleton_append, b] using hw⟩

end PEqualNP.Outside.L_meta_3481

open PEqualNP.Outside.L_meta_3481 in
theorem PEqualNP.Outside.L_meta_3481 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ¬x3.Adj x6 x7 → (2 : ℕ) ≤ (x3.neighborSet x6).ncard → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → ∃ (x12 : Fin x1), ¬(x3.Adj x6 x12 ↔ x3.Adj x7 x12)) → (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → (2 : ℕ) ≤ (x3.neighborSet x8).ncard → ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x7 x12 ∧ x12 ≠ x8 ∧ x3.Adj x8 x13 ∧ x13 ≠ x7 ∧ (x12 = x13 ∨ ¬x3.Adj x12 x13)) → (∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → (2 : ℕ) ≤ (x3.neighborSet x9).ncard → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x8.card = x2) → (∀ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → (2 : ℕ) ≤ (x3.neighborSet x11).ncard → x10 ∈ x9 ∨ x11 ∈ x9) → x2 ≤ x9.card) → PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 ∨ x1 + x4.size ≤ x4.output → (∀ (x12 x13 : Fin x1), x4.eval (List.ofFn fun (x14 : Fin x1) => Decidable.decide (x14 = x12 ∨ x14 = x13)) = Bool.true ↔ x3.Adj x12 x13) → x1 + x2 ≤ x4.size + (1 : ℕ) := by
  intro n k G C neighbors _ _ cover _ _ hout tests
  by_cases hn : n = 0
  · subst n
    obtain ⟨S, _, rfl⟩ := cover
    have empty : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i => Fin.elim0 i)
    simp [empty]
  rcases hout with hraw | hout
  · let u : Fin n := ⟨C.output, hraw⟩
    let x := fun i : Fin n => decide (i = u ∨ i = u)
    obtain ⟨t, _, hw⟩ := append_wires C.gates (List.ofFn x)
    have hlen : C.output < (List.ofFn x).length := by simpa using hraw
    have yes : C.eval (List.ofFn x) = true := by
      change (C.wires (List.ofFn x)).getD C.output false = true
      change C.wires (List.ofFn x) = _ at hw
      rw [hw, List.getD, List.getElem?_append_left hlen, List.getElem?_eq_getElem hlen]
      simp [x, u]
    exact (G.loopless.irrefl u ((tests u u).mp yes)).elim
  · let u : Fin n := ⟨0, by omega⟩
    obtain ⟨v, edge⟩ := neighbors u
    let x := fun i : Fin n => decide (i = u ∨ i = v)
    have yes := (tests u v).mpr edge
    obtain ⟨t, ht, hw⟩ := append_wires C.gates (List.ofFn x)
    change C.wires (List.ofFn x) = _ at hw
    change (C.wires (List.ofFn x)).getD C.output false = true at yes
    rw [hw, List.getD_eq_default] at yes
    · contradiction
    · simpa [ht, Circuit.size] using hout
