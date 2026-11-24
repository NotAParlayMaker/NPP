import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_3481

lemma wireSuffix (C : Circuit) (xs : List Bool) :
    ∃ tail : List Bool, C.wires xs = xs ++ tail ∧ tail.length = C.size := by
  obtain ⟨gs, out⟩ := C
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp [Circuit.wires], rfl⟩
  | cons g gs ih =>
    let value := g.op.eval (g.inputs.map fun i => xs.getD i false)
    obtain ⟨tail, hw, hl⟩ := ih (xs ++ [value])
    refine ⟨value :: tail, ?_, ?_⟩
    · change (Circuit.mk gs out).wires (xs ++ [value]) = _
      rw [hw]
      simp
    · simpa [Circuit.size] using congrArg Nat.succ hl

end PEqualNP.Outside.L_meta_3481

open PEqualNP.Outside.L_meta_3481

theorem PEqualNP.Outside.L_meta_3481 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ¬x3.Adj x6 x7 → (2 : ℕ) ≤ (x3.neighborSet x6).ncard → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → ∃ (x12 : Fin x1), ¬(x3.Adj x6 x12 ↔ x3.Adj x7 x12)) → (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → (2 : ℕ) ≤ (x3.neighborSet x8).ncard → ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x7 x12 ∧ x12 ≠ x8 ∧ x3.Adj x8 x13 ∧ x13 ≠ x7 ∧ (x12 = x13 ∨ ¬x3.Adj x12 x13)) → (∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → (2 : ℕ) ≤ (x3.neighborSet x9).ncard → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x8.card = x2) → (∀ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → (2 : ℕ) ≤ (x3.neighborSet x11).ncard → x10 ∈ x9 ∨ x11 ∈ x9) → x2 ≤ x9.card) → PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 ∨ x1 + x4.size ≤ x4.output → (∀ (x12 x13 : Fin x1), x4.eval (List.ofFn fun (x14 : Fin x1) => Decidable.decide (x14 = x12 ∨ x14 = x13)) = Bool.true ↔ x3.Adj x12 x13) → x1 + x2 ≤ x4.size + (1 : ℕ) := by
  intro n k G C incident _ _ cover _ _ output pair
  by_cases hn : n = 0
  · subst n
    obtain ⟨S, _, hS⟩ := cover
    have hcard : S.card ≤ 0 := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ S
    omega
  exfalso
  rcases output with input | outside
  · let v : Fin n := ⟨C.output, input⟩
    apply G.loopless.irrefl v
    apply (pair v v).mp
    let xs := List.ofFn fun i : Fin n => decide (i = v ∨ i = v)
    obtain ⟨tail, hw, _⟩ := wireSuffix C xs
    have hi : C.output < xs.length := by simpa [xs] using input
    change (C.wires xs).getD C.output false = true
    rw [hw, List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
    simp [xs, v]
  · let v : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    obtain ⟨w, hadj⟩ := incident v
    have accepted := (pair v w).mpr hadj
    let xs := List.ofFn fun i : Fin n => decide (i = v ∨ i = w)
    obtain ⟨tail, hw, hl⟩ := wireSuffix C xs
    have bound : (C.wires xs).length ≤ C.output := by
      rw [hw, List.length_append, hl]
      simpa only [xs, List.length_ofFn] using outside
    change (C.wires xs).getD C.output false = true at accepted
    rw [List.getD_eq_default _ _ bound] at accepted
    contradiction
