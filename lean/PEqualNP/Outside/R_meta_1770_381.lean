import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

-- Charge all edges with a low-degree endpoint to those endpoints. The unresolved
-- count is then only for doubly carried edges with two high-degree endpoints.
theorem PEqualNP.Outside.R_meta_1770_381
    (low : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C →
      (G.edgeFinset.filter (fun e => ¬ ∀ v ∈ e, 3 ≤ G.degree v)).card ≤ 2 * (C.size + 1))
    (high : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      IsLeastAO G C → TopForm G C →
      let B : Finset (Sym2 (Fin n)) := {x9 ∈ Ustar G C | (¬∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ tops G C, ∃ (x13 : Fin 2), ∃ x14 ∈ junk G C, x10 ∈ side C x12 x13 ∧ OrReaches n C (opnd C x12 (1 - x13)) x14 ∧ gateVal n C x14 (pairInput x10 x11) = true) ∧ ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ tops G C, ∃ x13 ∈ junk G C, ∃ x14 ∈ junk G C, x13 ≠ x14 ∧ OrReaches n C (opnd C x12 0) x13 ∧ OrReaches n C (opnd C x12 1) x14 ∧ gateVal n C x13 (pairInput x10 x11) = true ∧ gateVal n C x14 (pairInput x10 x11) = true}
      (B.filter (fun e => ∀ v ∈ e, 3 ≤ G.degree v)).card ≤ k * (C.size + 1)) :
∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | (¬∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true) ∧ ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x13 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by

  obtain ⟨k,hk⟩ := high
  refine ⟨k+2,?_⟩
  intro n G d C girth least top
  let B : Finset (Sym2 (Fin n)) := {x9 ∈ Ustar G C | (¬∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ tops G C, ∃ (x13 : Fin 2), ∃ x14 ∈ junk G C, x10 ∈ side C x12 x13 ∧ OrReaches n C (opnd C x12 (1 - x13)) x14 ∧ gateVal n C x14 (pairInput x10 x11) = true) ∧ ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ tops G C, ∃ x13 ∈ junk G C, ∃ x14 ∈ junk G C, x13 ≠ x14 ∧ OrReaches n C (opnd C x12 0) x13 ∧ OrReaches n C (opnd C x12 1) x14 ∧ gateVal n C x13 (pairInput x10 x11) = true ∧ gateVal n C x14 (pairInput x10 x11) = true}
  let pred (e : Sym2 (Fin n)) := ∀ v ∈ e, 3 ≤ G.degree v
  have part := Finset.card_filter_add_card_filter_not (s:=B) pred
  have highBound : (B.filter pred).card ≤ k * (C.size+1) := hk n G C girth least top
  have inside : B.filter (fun e => ¬ pred e) ⊆ G.edgeFinset.filter (fun e => ¬ pred e) := by
    intro e he
    obtain ⟨inB, notHigh⟩ := Finset.mem_filter.mp he
    have inU : e ∈ Ustar G C := (Finset.mem_filter.mp inB).1
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp inU).1,notHigh⟩
  have lowBound := (Finset.card_le_card inside).trans (low n G C least)
  change B.card ≤ (k+2) * (C.size+1)
  rw [Nat.add_mul]
  omega
