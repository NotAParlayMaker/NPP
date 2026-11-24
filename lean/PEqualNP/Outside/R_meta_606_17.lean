import Mathlib
import PEqualNP.Defs

-- Reduction of L-meta-606 along the low-merge route, for graphs instead of point-line incidences.
-- A gate k is a MERGE at the vertex w when it is an OR gate reading two earlier wires a and b,
-- it is LOW at w (on inputs with x_w on, the neighbours of w free and every other input off,
-- the gate is on only if some neighbour of w is on), and the alive sets of a and b at w
-- (the neighbours p of w such that the wire is on when exactly x_w and x_p are on) are
-- incomparable.
-- h1: the per-vertex count, the graph form of L-meta-663: a vertex of degree d has at least
--     d - 1 merges.
-- h2: the summed count (the frontier row, shard 0): the merges at all vertices together are
--     at most a constant times the circuit size.
-- h3: every vertex that has a neighbour is read by some gate, so there are at most
--     2 * size + 2 of them.
-- Then 2|E| = sum of degrees <= (sum of merges) + (vertices with a neighbour) <= (c + 2)(size + 1).
theorem PEqualNP.Outside.R_meta_606_17
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∀ w : Fin n, 0 < G.degree w → G.degree w ≤ {k : ℕ | ∃ a b : ℕ, a < n + k ∧ b < n + k ∧ D.gates[k]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ ∧ (∀ pts : Fin n → Bool, (D.wires (List.ofFn (fun v : Fin n => decide (v = w ∨ (G.Adj w v ∧ pts v = true))))).getD (n + k) false = true → ∃ p : Fin n, G.Adj w p ∧ pts p = true) ∧ ¬ ({p : Fin n | G.Adj w p ∧ (D.wires (List.ofFn (fun v : Fin n => decide (v = w ∨ v = p)))).getD a false = true} ⊆ {p : Fin n | G.Adj w p ∧ (D.wires (List.ofFn (fun v : Fin n => decide (v = w ∨ v = p)))).getD b false = true}) ∧ ¬ ({p : Fin n | G.Adj w p ∧ (D.wires (List.ofFn (fun v : Fin n => decide (v = w ∨ v = p)))).getD b false = true} ⊆ {p : Fin n | G.Adj w p ∧ (D.wires (List.ofFn (fun v : Fin n => decide (v = w ∨ v = p)))).getD a false = true})}.ncard + 1)
    (h2 : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∑ w : Fin n, {k : ℕ | ∃ a b : ℕ, a < n + k ∧ b < n + k ∧ D.gates[k]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ ∧ (∀ pts : Fin n → Bool, (D.wires (List.ofFn (fun v : Fin n => decide (v = w ∨ (G.Adj w v ∧ pts v = true))))).getD (n + k) false = true → ∃ p : Fin n, G.Adj w p ∧ pts p = true) ∧ ¬ ({p : Fin n | G.Adj w p ∧ (D.wires (List.ofFn (fun v : Fin n => decide (v = w ∨ v = p)))).getD a false = true} ⊆ {p : Fin n | G.Adj w p ∧ (D.wires (List.ofFn (fun v : Fin n => decide (v = w ∨ v = p)))).getD b false = true}) ∧ ¬ ({p : Fin n | G.Adj w p ∧ (D.wires (List.ofFn (fun v : Fin n => decide (v = w ∨ v = p)))).getD b false = true} ⊆ {p : Fin n | G.Adj w p ∧ (D.wires (List.ofFn (fun v : Fin n => decide (v = w ∨ v = p)))).getD a false = true})}.ncard ≤ c * (D.size + 1))
    (h3 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → {v : Fin n | 0 < G.degree v}.ncard ≤ 2 * D.size + 2) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → G.edgeFinset.card ≤ c * (D.size + 1) := by
  obtain ⟨c, hc⟩ := h2
  refine ⟨c + 2, ?_⟩
  intro n G _ hg D hD hf
  have hs := hc n G hg D hD hf
  have hd := h1 n G hg D hD hf
  have hn : (Finset.univ.filter (fun v : Fin n => 0 < G.degree v)).card ≤ 2 * D.size + 2 := by
    have h := h3 n G D hD hf
    rw [← Set.ncard_coe_finset]
    simpa using h
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hle : ∑ v : Fin n, G.degree v ≤ ∑ v : Fin n, ({k : ℕ | ∃ a b : ℕ, a < n + k ∧ b < n + k ∧ D.gates[k]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ ∧ (∀ pts : Fin n → Bool, (D.wires (List.ofFn (fun u : Fin n => decide (u = v ∨ (G.Adj v u ∧ pts u = true))))).getD (n + k) false = true → ∃ p : Fin n, G.Adj v p ∧ pts p = true) ∧ ¬ ({p : Fin n | G.Adj v p ∧ (D.wires (List.ofFn (fun u : Fin n => decide (u = v ∨ u = p)))).getD a false = true} ⊆ {p : Fin n | G.Adj v p ∧ (D.wires (List.ofFn (fun u : Fin n => decide (u = v ∨ u = p)))).getD b false = true}) ∧ ¬ ({p : Fin n | G.Adj v p ∧ (D.wires (List.ofFn (fun u : Fin n => decide (u = v ∨ u = p)))).getD b false = true} ⊆ {p : Fin n | G.Adj v p ∧ (D.wires (List.ofFn (fun u : Fin n => decide (u = v ∨ u = p)))).getD a false = true})}.ncard + if 0 < G.degree v then 1 else 0) := by
    apply Finset.sum_le_sum
    intro v _
    by_cases h : 0 < G.degree v
    · simp only [h, ite_true]
      exact hd v h
    · simp only [h, ite_false]
      omega
  rw [Finset.sum_add_distrib, ← Finset.card_filter] at hle
  have h2e : 2 * G.edgeFinset.card ≤ (c + 2) * (D.size + 1) := by
    rw [← hsum]
    nlinarith
  omega
