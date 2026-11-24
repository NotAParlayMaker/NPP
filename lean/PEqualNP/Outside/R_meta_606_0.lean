import Mathlib
import PEqualNP.Defs

/-- Reduction for shard 0 of L-meta-606.

The first child is the summed new-low-merge inequality.  The second is a linear-size
point/line presentation of a girth-at-least-five graph.  The third charges new low
merges to gates and lines in a rectangle-free incidence.  The last child bounds the
number of non-isolated vertices by the gates of a monotone edge circuit. -/
theorem PEqualNP.Outside.R_meta_606_0 :
    (∀ (P L : ℕ) (inc : Fin P → Fin L → Bool)
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C →
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
      (∀ (x : Fin P → Bool) (y : Fin L → Bool),
        C.eval (List.ofFn x ++ List.ofFn y) =
          decide (∃ (p : Fin P) (w : Fin L), inc p w = true ∧ x p = true ∧ y w = true)) →
      ((∑ w : Fin L, ∑ p : Fin P, if inc p w = true then 1 else 0) ≤
        (∑ w : Fin L, ∑ g ∈ Finset.range (P + L + C.gates.length),
          if PEqualNP.LowMerge.IsLowMerge P L inc C g w then 1 else 0) + L) ∧
      ((∑ w : Fin L, ∑ p : Fin P, if inc p w = true then 1 else 0) ≤
        (∑ w : Fin L, ∑ g ∈ Finset.range (P + L + C.gates.length),
          if PEqualNP.LowMerge.IsNewLowMerge P L inc C g w then 1 else 0) + L))
    →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D →
      PEqualNP.MetaComplexity.circuitFun n D =
        (fun x : Fin n → Bool =>
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∃ (P L : ℕ) (inc : Fin P → Fin L → Bool)
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        L = (∑ v : Fin n, if ∃ w : Fin n, G.Adj v w then 1 else 0) ∧
        (∑ w : Fin L, ∑ p : Fin P, if inc p w = true then 1 else 0) =
          2 * G.edgeFinset.card ∧
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ D.size + G.edgeFinset.card ∧
        (∀ (x : Fin P → Bool) (y : Fin L → Bool),
          C.eval (List.ofFn x ++ List.ofFn y) =
            decide (∃ (p : Fin P) (w : Fin L), inc p w = true ∧ x p = true ∧ y w = true)) ∧
        (∀ p p' : Fin P, ∀ w w' : Fin L, p ≠ p' → w ≠ w' →
          ¬ (inc p w = true ∧ inc p w' = true ∧
            inc p' w = true ∧ inc p' w' = true)))
    →
    (∀ (P L : ℕ) (inc : Fin P → Fin L → Bool)
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin P, ∀ w w' : Fin L, p ≠ p' → w ≠ w' →
        ¬ (inc p w = true ∧ inc p w' = true ∧
          inc p' w = true ∧ inc p' w' = true)) →
      PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C →
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
      (∀ (x : Fin P → Bool) (y : Fin L → Bool),
        C.eval (List.ofFn x ++ List.ofFn y) =
          decide (∃ (p : Fin P) (w : Fin L), inc p w = true ∧ x p = true ∧ y w = true)) →
      (∑ w : Fin L, ∑ g ∈ Finset.range (P + L + C.gates.length),
        if PEqualNP.LowMerge.IsNewLowMerge P L inc C g w then 1 else 0) ≤
        C.size + L)
    →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D →
      PEqualNP.MetaComplexity.circuitFun n D =
        (fun x : Fin n → Bool =>
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      (∑ v : Fin n, if ∃ w : Fin n, G.Adj v w then 1 else 0) ≤ D.size + 1)
    →
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D →
      PEqualNP.MetaComplexity.circuitFun n D =
        (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      G.edgeFinset.card ≤ c * (D.size + 1) := by
  intro hsum hlift hcharge hvertices
  refine ⟨3, ?_⟩
  intro n G _ hg D hD hfun
  obtain ⟨P, L, inc, C, hL, hinc, hmono, hsize, hcomp, hrect⟩ :=
    hlift n G hg D hD hfun
  have hC : PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C := by
    intro g hg
    exact (hmono g hg).1
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := by
    intro g hg
    exact (hmono g hg).2
  have h1 := (hsum P L inc C hC hfan hcomp).2
  have h2 := hcharge P L inc C hrect hC hfan hcomp
  have h3 := hvertices n G D hD hfun
  rw [hinc] at h1
  omega
