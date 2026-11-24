import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Size at most 12, or an unused extra wire, is left as one case. The tight
-- 13-gate case with both extra wires used is split on the first gate.
theorem PEqualNP.Outside.R_meta_3122_2
    (hshort :
      ∀ (ops : List ℕ), ops.length ≤ 2 →
      ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∃ g, C.gates[1]? = some g) →
        (C.size ≤ 12 ∨
          ¬ ((∃ g ∈ C.gates, 10 ∈ g.inputs) ∨ C.output = 10) ∨
          ¬ ((∃ g ∈ C.gates, 9 ∈ g.inputs) ∨ 9 ∈ ops ∨ C.output = 9)) →
        ∃ (x7 : Fin (9 : ℕ) → Bool),
        have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))]
        C.eval (x8 ++ [GateOp.or.eval (List.map (fun i : ℕ => x8.getD i false) ops)]) ≠
          (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (hAND :
      ∀ (ops : List ℕ), ops.length ≤ 2 →
      ∀ (C : Circuit), FanInTwo C → C.size = 13 →
        ((∃ g ∈ C.gates, 10 ∈ g.inputs) ∨ C.output = 10) →
        ((∃ g ∈ C.gates, 9 ∈ g.inputs) ∨ 9 ∈ ops ∨ C.output = 9) →
        (∀ g M, C.gates = g :: M → g.op = GateOp.and) →
        ∃ (x7 : Fin (9 : ℕ) → Bool),
        have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))]
        C.eval (x8 ++ [GateOp.or.eval (List.map (fun i : ℕ => x8.getD i false) ops)]) ≠
          (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (hOR :
      ∀ (ops : List ℕ), ops.length ≤ 2 →
      ∀ (C : Circuit), FanInTwo C → C.size = 13 →
        ((∃ g ∈ C.gates, 10 ∈ g.inputs) ∨ C.output = 10) →
        ((∃ g ∈ C.gates, 9 ∈ g.inputs) ∨ 9 ∈ ops ∨ C.output = 9) →
        (∀ g M, C.gates = g :: M → g.op = GateOp.or) →
        ∃ (x7 : Fin (9 : ℕ) → Bool),
        have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))]
        C.eval (x8 ++ [GateOp.or.eval (List.map (fun i : ℕ => x8.getD i false) ops)]) ≠
          (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (hNOT :
      ∀ (ops : List ℕ), ops.length ≤ 2 →
      ∀ (C : Circuit), FanInTwo C → C.size = 13 →
        ((∃ g ∈ C.gates, 10 ∈ g.inputs) ∨ C.output = 10) →
        ((∃ g ∈ C.gates, 9 ∈ g.inputs) ∨ 9 ∈ ops ∨ C.output = 9) →
        (∀ g M, C.gates = g :: M → g.op = GateOp.not) →
        ∃ (x7 : Fin (9 : ℕ) → Bool),
        have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))]
        C.eval (x8 ++ [GateOp.or.eval (List.map (fun i : ℕ => x8.getD i false) ops)]) ≠
          (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro ops hlen C fan hsz hgate
  dsimp only
  by_cases h12 : C.size ≤ 12
  · exact hshort ops hlen C fan hsz hgate (Or.inl h12)
  by_cases u10 : (∃ g ∈ C.gates, 10 ∈ g.inputs) ∨ C.output = 10
  · by_cases u9 : (∃ g ∈ C.gates, 9 ∈ g.inputs) ∨ 9 ∈ ops ∨ C.output = 9
    · have heq : C.size = 13 := by
        have : ¬ C.size ≤ 12 := h12
        omega
      cases hgs : C.gates with
      | nil =>
        have : C.size = 0 := by simp [Circuit.size, hgs]
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
        · exact hAND ops hlen C fan heq u10 u9 (hall GateOp.and ha)
        · exact hOR ops hlen C fan heq u10 u9 (hall GateOp.or ho)
        · exact hNOT ops hlen C fan heq u10 u9 (hall GateOp.not hn)
    · exact hshort ops hlen C fan hsz hgate (Or.inr (Or.inr u9))
  · exact hshort ops hlen C fan hsz hgate (Or.inr (Or.inl u10))
