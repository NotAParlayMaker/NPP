import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2640_713
    (batch : ∀ (n : ℕ) (row : (Fin n → Bool) → (Fin n → Bool)) (B : Circuit) (S : Finset ℕ) (p : ℕ → ℕ),
     (∀ m ∈ S, m < B.size ∧ p m < n+m ∧ (∀ j ∈ S, p m ≠ n+j) ∧
       ((∀ x, let w := B.wires (List.ofFn (row x)); w.getD (n+m) false = w.getD (p m) false) ∨
        (B.output ≠ n+m ∧ ∀ (j : ℕ) (g : Gate), B.gates[j]? = some g → j ∉ S → n+m ∉ g.inputs))) →
     ∃ D : ℕ → Circuit, D 0 = B ∧ ∀ j < S.card, ∃ m p, m < (D j).size ∧ p < n+m ∧ D (j+1) = CircuitMoves.eraseGate n (D j) m p ∧
       ((∀ x, let w := (D j).wires (List.ofFn (row x)); w.getD (n+m) false = w.getD p false) ∨
       ((D j).output ≠ n+m ∧ ∀ g ∈ (D j).gates.drop (m+1), n+m ∉ g.inputs)))
    (marks : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (C : Circuit),
     ¬ G.Colorable 2 → (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
     (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
     (∀ u v, G.Adj u v → u ∉ A) → IsMinimalCircuit n C →
     (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
       (∃ a ∈ A, x a = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
     ∃ (u v : Fin n) (B : Circuit) (S : Finset ℕ) (p : ℕ → ℕ),
       G.Adj u v ∧ FanInTwo B ∧ B.size ≤ C.size ∧ circuitFun n B = circuitFun n C ∧
       7 ≤ S.card ∧
       let row := fun (x : Fin n → Bool) => Function.update (Function.update x u false) v false
       ∀ m ∈ S, m < B.size ∧ p m < n+m ∧ (∀ j ∈ S, p m ≠ n+j) ∧
       ((∀ x, let w := B.wires (List.ofFn (row x)); w.getD (n+m) false = w.getD (p m) false) ∨
        (B.output ≠ n+m ∧ ∀ (j : ℕ) (g : Gate), B.gates[j]? = some g → j ∉ S → n+m ∉ g.inputs))) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   ¬x2.Colorable (2 : ℕ) →     (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →       (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →         (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →           (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →               (∀ (x11 : Fin x1 → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →                 ∃ (x12 : Fin x1) (x13 : Fin x1),                   x2.Adj x12 x13 ∧                     ∃ (x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x14 (0 : ℕ)) ∧                         (x14 (0 : ℕ)).size ≤ x4.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x14 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x4 ∧                             ∀ x15 < (7 : ℕ),                               ∃ (x17 : ℕ) (x18 : ℕ),                                 x17 < (x14 x15).size ∧                                   (x18 < x1 + x17 ∨ x1 + (x14 x15).size ≤ x18) ∧                                     x14 (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x14 x15) x17 x18 ∧                                       ((∀ (x19 : Fin x1 → Bool),                                           have x20 : List Bool := (x14 x15).wires (List.ofFn (Function.update (Function.update x19 x12 Bool.false) x13 Bool.false));                                           x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨                                         (x14 x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (x14 x15).gates, x1 + x17 ∉ x19.inputs) := by
  intro n G A C odd cubic girth isolated _edge minC spec
  obtain ⟨u,v,B,S,p,adj,fan,budget,same,count,cert⟩ := marks n G A C odd cubic girth isolated minC spec
  let row := fun (x : Fin n → Bool) => Function.update (Function.update x u false) v false
  obtain ⟨D,start,trace⟩ := batch n row B S p cert
  refine ⟨u,v,adj,D,start ▸ fan,start ▸ budget,start ▸ same,?_⟩
  intro j hj
  obtain ⟨m,r,hm,hr,next,legal⟩ := trace j (by omega)
  exact ⟨m,r,hm,Or.inl hr,next,legal⟩
