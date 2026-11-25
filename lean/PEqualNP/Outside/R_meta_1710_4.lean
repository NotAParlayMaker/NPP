import Mathlib
import PEqualNP.Defs

/-!
# R-meta-1710-4: the core (degree 0 or at least 3, girth at least 5) from the clean pair case

The gap `L-meta-1710` asks: for every graph with no cycle shorter than 5 and every vertex of
degree 0 or at least 3, and every AND/OR circuit of fan-in two computing the edge function, the
number of edges is at most `c * (gates + 1)` for one absolute constant `c`.

This file reduces it to two ingredients, both stated for the root model of `PEqualNP.Defs` only.
With the four-point form of `NoFourCycle` (which the girth hypothesis gives, see below),

* `block` is the CLEAN PAIR CASE: a circuit whose AND gates are false at every pair `1_uv` of
  non-adjacent vertices already has `|E| <= size + 1`. This is the sharp case; it is exactly the
  desk step `L-meta-7241` (`NoFourCycle` + `IsAO2` + edge function + clean at non-edges yields
  `|E| + tau <= size + 1`, hence `|E| <= size + 1` there), and its variant `L-meta-6369`
  (`ReadK` instead of clean). Only the four-point form of `NoFourCycle` is used, never the
  degree condition and never the vertex cover `tau`.
* `prune` is the CLEANUP step: a circuit for the edge function can be replaced by a clean one
  (all AND gates false at non-edge pairs) of no greater size, computing the same function.
  The clean hypothesis of `block` is NOT derivable from `Monotone2` plus the edge function
  alone: taking `C = AND(x1 /\ x2, OR(x3 /\ x4, <and,[]>))` (an AND gate with no input is the
  constant `true` in the root model) keeps the irrelevant gate `x3 /\ x4` on the output path,
  whose value at `1_13` is `true` although `{1,3}` is not an edge, while `C` still computes
  `x1 /\ x2`. So cleanliness has to be paid for, and `prune` is exactly that payment.

Given `block` and `prune`, the gap follows with `c = 1`: prune the given circuit, apply `block`
to the pruned circuit, and use `size (pruned) <= size`.

The girth-to-`NoFourCycle` derivation below is copied verbatim from the checked file
`PEqualNP.Outside.L_meta_1601`.
-/

theorem PEqualNP.Outside.R_meta_1710_4
    (block : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.circuitFun n C =
          (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
        (∀ k : ℕ, k < C.gates.length →
          (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ u v : Fin n, ¬ G.Adj u v →
            PEqualNP.EdgeOwnership.gateVal n C k (PEqualNP.EdgeOwnership.pairInput u v) = false) →
        G.edgeFinset.card ≤ C.size + 1)
    (prune : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.circuitFun n C =
          (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
        ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size ≤ C.size ∧
          PEqualNP.MetaComplexity.circuitFun n C' =
            (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) ∧
          (∀ k : ℕ, k < C'.gates.length →
            (PEqualNP.MetaComplexity.NestedCover.gateAt C' k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ∀ u v : Fin n, ¬ G.Adj u v →
              PEqualNP.EdgeOwnership.gateVal n C' k (PEqualNP.EdgeOwnership.pairInput u v) = false))
    : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ p : Fin n, ∀ q : G.Walk p p, q.IsCycle → 5 ≤ q.length) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.circuitFun n C =
          (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
        G.edgeFinset.card ≤ c * (C.size + 1) := by
  refine ⟨1, ?_⟩
  intro n G instG hDeg hGirth C hMono hFun
  -- the girth hypothesis gives the four-point form of `NoFourCycle`
  have hNo4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    intro a b c d hac hbd h4
    have hab : G.Adj a b := h4.1
    have hbc : G.Adj b c := h4.2.1
    have hcd : G.Adj c d := h4.2.2.1
    have hda : G.Adj d a := h4.2.2.2
    let W : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
    have hW : W.IsCycle := by
      refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [W]⟩
      simp only [W, SimpleGraph.Walk.tail_cons, SimpleGraph.Walk.isPath_copy,
        SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
      simp [hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hac.symm, hbd]
    have h5 := hGirth a W hW
    have h4l : W.length = 4 := rfl
    omega
  -- pay for cleanliness, then apply the clean pair case to the pruned circuit
  refine Exists.elim (prune n G C hMono hFun) ?_
  intro C' hC'
  have hMono' : PEqualNP.MetaComplexity.Monotone2 C' := hC'.1
  have hSize : C'.size ≤ C.size := hC'.2.1
  have hFun' : PEqualNP.MetaComplexity.circuitFun n C' =
      (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) := hC'.2.2.1
  have hClean' := hC'.2.2.2
  have hB := block n G hNo4 C' hMono' hFun' hClean'
  have h1 : G.edgeFinset.card ≤ C.size + 1 := by omega
  simpa using h1
