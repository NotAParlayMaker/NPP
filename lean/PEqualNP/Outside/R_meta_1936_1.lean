import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_1936_1_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The edge function of the Petersen graph with the vertex `0` deleted. -/
def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

/-- The wires before the thirteen-gate tail: the nine inputs and the forced `NOT x_0`. -/
def pre (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [!x 0]

lemma pre_length (x : Fin 9 → Bool) : (pre x).length = 10 := by
  simp [pre]

/-- A wire index capped at `10`, the first index that is out of range for `pre`. -/
def cap (i : ℕ) : Fin 11 :=
  if h : i < 10 then ⟨i, by omega⟩ else 10

lemma getD_cap (w : List Bool) (hw : w.length = 10) (i : ℕ) :
    w.getD (cap i).val false = w.getD i false := by
  unfold cap
  split
  · rfl
  · rename_i hi
    have h1 : w.length ≤ i := by omega
    have h2 : w.length ≤ 10 := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2]

lemma and_nil : GateOp.and.eval [] = true := rfl

lemma and_single (p : Bool) : GateOp.and.eval [p] = p := by
  simp [GateOp.eval]

lemma and_pair (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by
  simp [GateOp.eval]

end PEqualNP.Outside.R_meta_1936_1_aux

open PEqualNP.Outside.R_meta_1936_1_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The `AND` case of the first-gate `NOT x_0` lower bound, reduced to one empty-pin case
(the second gate is then the constant `true`) and `66 = 11 * 12 / 2` pair cases.  This is the
`AND` analogue of the checked reduction `R_meta_1938_741` for the `OR` case. -/
theorem PEqualNP.Outside.R_meta_1936_1
    (hEmpty : ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        C.eval (pre x ++ [true]) ≠ target x)
    (hBound : ∀ (a b : Fin 11), a ≤ b → ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        C.eval (pre x ++ [(pre x).getD a.val false && (pre x).getD b.val false]) ≠
          target x) :
    ∀ (x1 : List ℕ), x1.length ≤ 2 →
      ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool,
          C.eval (pre x ++
            [GateOp.and.eval (x1.map fun i => (pre x).getD i false)]) ≠ target x := by
  intro x1 hlen C hfan hsize
  rcases x1 with _ | ⟨i, rest⟩
  · simpa [and_nil] using hEmpty C hfan hsize
  · rcases rest with _ | ⟨j, rest⟩
    · let a := cap i
      obtain ⟨x, hx⟩ := hBound a a le_rfl C hfan hsize
      refine ⟨x, ?_⟩
      have hv : GateOp.and.eval [(pre x).getD i false] =
          ((pre x).getD a.val false && (pre x).getD a.val false) := by
        rw [and_single]
        dsimp [a]
        rw [getD_cap (pre x) (pre_length x) i, Bool.and_self]
      simp only [List.map_cons, List.map_nil]
      rw [hv]
      exact hx
    · rcases rest with _ | ⟨k, rest⟩
      · let a := min (cap i) (cap j)
        let b := max (cap i) (cap j)
        have hab : a ≤ b := min_le_max
        obtain ⟨x, hx⟩ := hBound a b hab C hfan hsize
        refine ⟨x, ?_⟩
        have hv : GateOp.and.eval [(pre x).getD i false, (pre x).getD j false] =
            ((pre x).getD a.val false && (pre x).getD b.val false) := by
          rw [and_pair]
          dsimp [a, b]
          rcases le_total (cap i).val (cap j).val with h | h
          · rw [min_eq_left h, max_eq_right h,
              getD_cap (pre x) (pre_length x) i,
              getD_cap (pre x) (pre_length x) j]
          · rw [min_eq_right h, max_eq_left h,
              getD_cap (pre x) (pre_length x) i,
              getD_cap (pre x) (pre_length x) j, Bool.and_comm]
        simp only [List.map_cons, List.map_nil]
        rw [hv]
        exact hx
      · simp only [List.length_cons] at hlen
        omega
