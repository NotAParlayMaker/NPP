import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_4891 : ∀ (x1 : Fin (63 : ℕ) → Bool) (x2 x3 : Fin (63 : ℕ) → Fin (89 : ℕ)), (∀ (x4 : Fin (63 : ℕ)), ↑(x2 x4) < (26 : ℕ) + ↑x4 ∧ ↑(x3 x4) < (26 : ℕ) + ↑x4 ∧ x2 x4 ≤ x3 x4) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = (63 : ℕ) ∧ ∀ (x6 : Fin (26 : ℕ) → Bool), x5.eval (List.ofFn x6) = (fun (x7 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x8 : List Bool) (x9 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x8 ++ [bif x9.1 then x8.getD (↑x9.2.1) Bool.false && x8.getD (↑x9.2.2) Bool.false else x8.getD (↑x9.2.1) Bool.false || x8.getD (↑x9.2.2) Bool.false]) (List.ofFn x7) (List.ofFn fun (x8 : Fin (63 : ℕ)) => (x1 x8, x2 x8, x3 x8))).getD (88 : ℕ) Bool.false) x6 := by
  intro ops a b _
  let toGate : Bool × Fin 89 × Fin 89 → Gate := fun t =>
    ⟨if t.1 = true then GateOp.and else GateOp.or, [t.2.1.val, t.2.2.val]⟩
  let L : List (Bool × Fin 89 × Fin 89) := List.ofFn fun i : Fin 63 => (ops i, a i, b i)
  refine ⟨⟨L.map toGate, 88⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨t, _, rfl⟩ := hg
    refine ⟨?_, by simp [toGate]⟩
    by_cases ht : t.1 = true
    · simp [toGate, ht]
    · simp [toGate, ht]
  · show (L.map toGate).length = 63
    simp [L]
  · intro x6
    have hstep : ∀ (w : List Bool) (t : Bool × Fin 89 × Fin 89),
        w ++ [(toGate t).op.eval ((toGate t).inputs.map fun i => w.getD i false)] =
          w ++ [bif t.1 then w.getD t.2.1.val false && w.getD t.2.2.val false
            else w.getD t.2.1.val false || w.getD t.2.2.val false] := by
      intro w t
      obtain ⟨o, i, j⟩ := t
      cases o
      · show w ++ [([i.val, j.val].map fun k => w.getD k false).any id] = _
        simp
      · show w ++ [([i.val, j.val].map fun k => w.getD k false).all id] = _
        simp
    show (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x6) (L.map toGate)).getD 88 false = _
    rw [List.foldl_map]
    have hf : (fun (w : List Bool) (t : Bool × Fin 89 × Fin 89) =>
        w ++ [(toGate t).op.eval ((toGate t).inputs.map fun i => w.getD i false)]) =
        (fun (x8 : List Bool) (x9 : Bool × Fin 89 × Fin 89) => x8 ++ [bif x9.1 then x8.getD (↑x9.2.1) false && x8.getD (↑x9.2.2) false
          else x8.getD (↑x9.2.1) false || x8.getD (↑x9.2.2) false]) := by
      funext w t
      exact hstep w t
    rw [hf]
