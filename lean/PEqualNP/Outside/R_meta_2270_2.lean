import Mathlib.Order.Nat
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2270_2
    (restriction : let count := fun (n : ℕ) (C : Circuit) (u v : Fin n) =>
      (C.gates.filter (fun g => decide (g.op.eval [false, false] = false ∧
        (u.val ∈ g.inputs ∨ v.val ∈ g.inputs)))).length;
    ∀ (n : ℕ) (C : Circuit) (u v : Fin n), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size + count n C u v ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          C.eval (List.ofFn (Function.update (Function.update x u false) v false)))
    (sparse : let count := fun (n : ℕ) (C : Circuit) (u v : Fin n) =>
      (C.gates.filter (fun g => decide (g.op.eval [false, false] = false ∧
        (u.val ∈ g.inputs ∨ v.val ∈ g.inputs)))).length;
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (C : Circuit),
      ¬ G.Colorable 2 →
      (∀ u ∉ A, (G.neighborSet u).ncard = 3) →
      (∀ (u : Fin n) (w : G.Walk u u), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) →
      (∃ u v, G.Adj u v) →
      IsMinimalCircuit n C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        (∃ a ∈ A, x a = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ u v, G.Adj u v → count n C u v < 7) →
      ∃ u v, G.Adj u v ∧
        ∃ D : Circuit, FanInTwo D ∧ D.size + 7 ≤ C.size ∧
          ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
            C.eval (List.ofFn (Function.update (Function.update x u false) v false))) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (7 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  intro n G A f nonbipartite cubic girth isolated edge fSpec s has
  classical
  have witness : ∃ k : ℕ, HasCircuitSize n f k := ⟨s, has⟩
  obtain ⟨C, cFan, bound, cEval⟩ := Nat.find_spec witness
  have cSize : C.size ≤ s := bound.trans (Nat.find_min' witness has)
  have minimal : IsMinimalCircuit n C := by
    refine ⟨cFan, ?_⟩
    intro E eFan same
    have eHas : HasCircuitSize n f E.size := ⟨E, eFan, le_rfl, fun x =>
      (congrFun same x).trans (cEval x)⟩
    exact bound.trans (Nat.find_min' witness eHas)
  have cSpec (x : Fin n → Bool) : C.eval (List.ofFn x) = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    rw [cEval]
    exact fSpec x
  let count (u v : Fin n) := (C.gates.filter (fun g =>
    decide (g.op.eval [false, false] = false ∧ (u.val ∈ g.inputs ∨ v.val ∈ g.inputs)))).length
  have result : ∃ u v, G.Adj u v ∧
      ∃ D : Circuit, FanInTwo D ∧ D.size + 7 ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          C.eval (List.ofFn (Function.update (Function.update x u false) v false)) := by
    by_cases low : ∀ u v, G.Adj u v → count u v < 7
    · exact sparse n G A C nonbipartite cubic girth isolated edge minimal cSpec low
    · push Not at low
      obtain ⟨u, v, adjacent, high⟩ := low
      obtain candidate := restriction n C u v cFan
      obtain ⟨D, dFan, cost, correct⟩ := candidate
      exact ⟨u, v, adjacent, D, dFan, (Nat.add_le_add_left high _).trans cost, correct⟩
  obtain ⟨u, v, adjacent, D, dFan, dSize, dEval⟩ := result
  refine ⟨u, v, isolated _ _ adjacent, isolated _ _ (G.adj_symm adjacent), adjacent,
    D.size, dSize.trans cSize, D, dFan, le_rfl, fun x => (dEval x).trans (cEval _)⟩
