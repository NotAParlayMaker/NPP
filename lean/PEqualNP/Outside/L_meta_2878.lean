import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2878_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  unfold Circuit.wires Circuit.size
  induction C.gates generalizing x with
  | nil => simp
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp
      omega

lemma getD_snoc_eq (l : List Bool) (v d : Bool) (i : ℕ) (hi : i = l.length) :
    (l ++ [v]).getD i d = v := by
  subst hi
  simp [List.getD]

end PEqualNP.Outside.L_meta_2878_aux

open PEqualNP.Outside.L_meta_2878_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_2878 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x2 →
      ∀ (x4 : PEqualNP.CircuitLowerBounds.GateOp),
        x4 = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          x4 = PEqualNP.CircuitLowerBounds.GateOp.or →
        ∀ (x6 x7 : ℕ),
          ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit),
            PEqualNP.MetaComplexity.Monotone2 x8 ∧
              x8.size ≤ x2.size + 1 ∧
              ∀ (x9 : Fin x1 → Bool),
                x8.eval (List.ofFn x9) =
                  x4.eval [(x2.wires (List.ofFn x9)).getD x6 Bool.false,
                    (x2.wires (List.ofFn x9)).getD x7 Bool.false] := by
  intro n C hmono op hop a b
  let g : Gate := { op := op, inputs := [a, b] }
  let C' : Circuit := { gates := C.gates ++ [g], output := n + C.size }
  refine ⟨C', ?_, ?_, ?_⟩
  · intro h hh
    simp only [C', List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · exact hmono h hh
    · refine ⟨?_, by simp [g]⟩
      rcases hop with rfl | rfl <;> simp [g]
  · simp [C', Circuit.size]
  · intro x
    have hw : C'.wires (List.ofFn x) =
        C.wires (List.ofFn x) ++
          [op.eval [(C.wires (List.ofFn x)).getD a false,
            (C.wires (List.ofFn x)).getD b false]] := by
      simp [C', Circuit.wires, List.foldl_append, g, List.map]
    have hl : n + C.size = (C.wires (List.ofFn x)).length := by
      rw [wires_length, List.length_ofFn]
    rw [Circuit.eval, hw, getD_snoc_eq _ _ _ _ hl]
