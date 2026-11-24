import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Split size at most 13 from the tight size-14 case, and split the first gate of the latter.
theorem PEqualNP.Outside.R_meta_5090_1
    (h13 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hAND : ∀ C : Circuit, FanInTwo C → C.size = 14 →
      (∀ g M, C.gates = g :: M → g.op = GateOp.and) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hOR : ∀ C : Circuit, FanInTwo C → C.size = 14 →
      (∀ g M, C.gates = g :: M → g.op = GateOp.or) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hNOT : ∀ C : Circuit, FanInTwo C → C.size = 14 →
      (∀ g M, C.gates = g :: M → g.op = GateOp.not) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
  intro C fan hsz
  by_cases hle : C.size ≤ 13
  · exact h13 C fan hle
  have heq : C.size = 14 := by
    have : ¬ C.size ≤ 13 := hle
    omega
  cases hgs : C.gates with
  | nil =>
    have : C.gates.length = 0 := (congrArg List.length hgs).trans List.length_nil
    have : C.gates.length = 14 := heq
    omega
  | cons g M =>
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using
        (fan g (by simp [hgs])).1
    have hall (op : GateOp) (hopg : g.op = op) :
        ∀ g' M', C.gates = g' :: M' → g'.op = op := by
      intro g' M' heq'
      have : g' = g := by
        rw [hgs] at heq'
        exact (List.cons.inj heq').1.symm
      exact this ▸ hopg
    rcases hop with ha | ho | hn
    · exact hAND C fan heq (hall GateOp.and ha)
    · exact hOR C fan heq (hall GateOp.or ho)
    · exact hNOT C fan heq (hall GateOp.not hn)
