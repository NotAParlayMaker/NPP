import Mathlib
import PEqualNP.Defs

-- The surviving-edge argument adapts R_meta_1593_1 by trimbe.
theorem PEqualNP.Outside.R_meta_2638_217
    (strip : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (g : (Fin n → Bool) → Bool) (s : ℕ),
    (∀ i j : Fin n, H.Adj i j → i ∉ A) →
    (∃ i j : Fin n, H.Adj i j) →
    (∀ x, g x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ i j : Fin n, H.Adj i j ∧ x i = true ∧ x j = true) →
    PEqualNP.MetaComplexity.HasCircuitSize n g s →
    ∃ (t : ℕ) (h : (Fin n → Bool) → Bool), t + A.card ≤ s ∧
      (∀ x, h x = true ↔ ∃ i j : Fin n, H.Adj i j ∧ x i = true ∧ x j = true) ∧
      PEqualNP.MetaComplexity.HasCircuitSize n h t)
    (pure : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (z : Fin n) (h : (Fin n → Bool) → Bool),
    (∀ i j : Fin n, G.Adj i j → (G.neighborSet i).ncard = 3) →
    (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
    (G.neighborSet z).ncard = 3 →
    (∀ T : Finset (Fin n), (∀ i j : Fin n,
      (G.deleteEdges (G.incidenceSet z)).Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    (∀ x, h x = true ↔ ∃ i j : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i j ∧
      x i = true ∧ x j = true) →
    PEqualNP.MetaComplexity.HasCircuitSize n h s →
    (G.deleteEdges (G.incidenceSet z)).edgeSet.ncard + k ≤ s + 1) :
    ∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ) := by
  classical
  intro n k s G A z g hdeg hgirth hA hedge hz hg hcover hc
  let H := G.deleteEdges (G.incidenceSet z)
  have residual_adj (i j : Fin n) : H.Adj i j ↔ G.Adj i j ∧ i ≠ z ∧ j ≠ z :=
    SimpleGraph.deleteIncidenceSet_adj
  have hHmarked (i j : Fin n) (hij : H.Adj i j) : i ∉ A :=
    hA i j ((residual_adj i j).1 hij).1
  have hHedge : ∃ i j : Fin n, H.Adj i j := by
    obtain ⟨a, b, hab⟩ := hedge
    obtain ⟨u, huz, huA⟩ : ∃ u : Fin n, u ≠ z ∧ u ∉ A := by
      by_cases haz : a = z
      · exact ⟨b, fun hbz => hab.ne (haz.trans hbz.symm), hA b a hab.symm⟩
      · exact ⟨a, haz, hA a b hab⟩
    by_contra hnone
    have hs : G.neighborSet u ⊆ ({z} : Set (Fin n)) := by
      intro w hw
      by_contra hwn
      exact hnone ⟨u, w, (residual_adj u w).2 ⟨hw, huz, fun e => hwn (by simp [e])⟩⟩
    have hl := Set.ncard_le_ncard hs
    simp [hdeg u huA] at hl
  obtain ⟨t, h, ht, hsem, hct⟩ := strip n H A g s hHmarked hHedge hg hc
  have hbound := pure n k t G z h (fun i j hij => hdeg i (hA i j hij))
    hgirth (hdeg z hz) hcover hsem hct
  omega
