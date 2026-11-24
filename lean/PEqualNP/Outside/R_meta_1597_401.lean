import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 50000 in
theorem PEqualNP.Outside.R_meta_1597_401 :
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
       G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let J : Finset ℕ := PEqualNP.TopForm.junk G D
       let U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G D
       let R : Finset ℕ := PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D
       (∀ a ∈ T,
         let S : Fin 2 → Finset (Fin 11) := PEqualNP.TopForm.side D a
         (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
       (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J, PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       15 + T.card + J.card + R.card ≤ D.size + U.card →
       (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ T.card) →
       PEqualNP.TopForm.centreless G D = ∅ → 2 ≤ J.card → 2 ≤ R.card → 3 ≤ U.card → 22 ≤ D.size) →
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
       G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let C0 : Finset ℕ := PEqualNP.TopForm.centreless G D
       let J : Finset ℕ := PEqualNP.TopForm.junk G D
       let U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G D
       let R : Finset ℕ := PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D
       (∀ a ∈ T,
         let S : Fin 2 → Finset (Fin 11) := PEqualNP.TopForm.side D a
         (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
       (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J, PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       17 + (T \ C0).card + 2 * C0.card + R.card ≤ D.size + U.card →
       (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ C0).card) →
       1 ≤ C0.card → 1 ≤ R.card → J.card = 2 → 3 ≤ U.card → 22 ≤ D.size) →
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
       G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let C0 : Finset ℕ := PEqualNP.TopForm.centreless G D
       let J : Finset ℕ := PEqualNP.TopForm.junk G D
       let U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G D
       let R : Finset ℕ := PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D
       (∀ a ∈ T,
         let S : Fin 2 → Finset (Fin 11) := PEqualNP.TopForm.side D a
         (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
       (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J, PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       15 + (T \ C0).card + 2 * C0.card + J.card + R.card ≤ D.size + U.card →
       (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ C0).card) →
       1 ≤ C0.card → 1 ≤ R.card → 3 ≤ J.card → 4 ≤ U.card → 22 ≤ D.size) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → (∀ a ∈ PEqualNP.TopForm.tops G C, Disjoint (PEqualNP.TopForm.side (n := n) C a 0) (PEqualNP.TopForm.side (n := n) C a 1) ∧ (∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C a 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C a 1).card ≤ 1)) ∧ ∀ u v : Fin n, s(u, v) ∈ PEqualNP.TopForm.Ustar G C → ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C, PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h ∧ PEqualNP.EdgeOwnership.gateVal n C h (PEqualNP.EdgeOwnership.pairInput u v) = true) → (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card + 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧ ∀ K : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K → K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → PEqualNP.TopForm.TopForm (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → 2 ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D).card → 22 ≤ D.size := by
  intro c1 c2 c3 h1 h2 D hL hT hj2
  let _ : DecidableEq GateOp := gateOpDecEq
  have hpi_left : ∀ u v : Fin 11, pairInput u v u = true := fun _ _ => decide_eq_true (Or.inl rfl)
  have hpi_right : ∀ u v : Fin 11, pairInput u v v = true := fun _ _ => decide_eq_true (Or.inr rfl)
  have hpi_iff : ∀ u v w : Fin 11, pairInput u v w = true ↔ w = u ∨ w = v := fun _ _ _ => decide_eq_true_iff
  have horIn_self : ∀ v : Fin 11, v ∈ orIn 11 D v.val := fun v => Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl rfl⟩
  set G0 := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  change 2 ≤ (junk G0 D).card at hj2
  by_contra hDge
  have hDsz : D.size ≤ 21 := by omega
  have hnf : NoFourCycle G0 := by dsimp [G0]; decide +kernel
  have hecard : G0.edgeFinset.card = 16 := by dsimp [G0]; decide +kernel
  have hne : G0.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hstar0, hoff⟩ := h1 11 G0 D hnf hne hL hT
  obtain ⟨hcnt, hcov⟩ := h2 11 G0 D hnf hne hL hT
  rw [hecard] at hcnt
  have hstar : ∀ a ∈ tops G0 D,
      let S : Fin 2 → Finset (Fin 11) := side D a
      (∀ u ∈ S 0, ∀ v ∈ S 1, G0.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1) :=
    fun a ha => (hstar0 a ha).2
  obtain ⟨hAO, hfun, hleast⟩ := hL
  obtain ⟨hAndOr, hReads, hLen2⟩ := hAO
  let nbrsList : List (List ℕ) :=
    [[9, 10], [4, 8], [5, 10], [6, 7], [1, 8, 10], [2, 8, 9],
     [3, 7, 10], [3, 6, 9], [1, 4, 5, 9], [0, 5, 7, 8], [0, 2, 4, 6]]
  let adjN (a b : ℕ) : Bool := (nbrsList.getD a []).contains b
  have hadjN_iff : ∀ a b : Fin 11, adjN a.val b.val = true ↔ G0.Adj a b := by
    dsimp [G0, nbrsList, adjN]; decide +kernel
  have hcover_ge7 : ∀ K : Finset (Fin 11), G0.IsVertexCover (K : Set (Fin 11)) → 7 ≤ K.card := by
    intro K hK
    let w (i : Fin 11) : ℕ := if i ∈ K then 1 else 0
    have ew (u v : Fin 11) (he : G0.Adj u v) : 1 ≤ w u + w v := by
      rcases hK he with hu | hv
      · change u ∈ K at hu; simp [w, hu]
      · change v ∈ K at hv; simp [w, hv]
    have e0 := ew 1 4 ((hadjN_iff 1 4).1 rfl)
    have e1 := ew 4 8 ((hadjN_iff 4 8).1 rfl)
    have e2 := ew 8 1 ((hadjN_iff 8 1).1 rfl)
    have e3 := ew 3 6 ((hadjN_iff 3 6).1 rfl)
    have e4 := ew 6 7 ((hadjN_iff 6 7).1 rfl)
    have e5 := ew 7 3 ((hadjN_iff 7 3).1 rfl)
    have e6 := ew 0 9 ((hadjN_iff 0 9).1 rfl)
    have e7 := ew 9 5 ((hadjN_iff 9 5).1 rfl)
    have e8 := ew 5 2 ((hadjN_iff 5 2).1 rfl)
    have e9 := ew 2 10 ((hadjN_iff 2 10).1 rfl)
    have e10 := ew 10 0 ((hadjN_iff 10 0).1 rfl)
    have hw : ∑ i : Fin 11, w i = K.card := by simp [w]
    rw [Fin.sum_univ_succ] at hw
    simp [Fin.sum_univ_succ] at hw
    omega
  have hcover_S7_ge5 : ∀ K : Finset (Fin 11),
      (0 ∈ K ∨ 9 ∈ K) → (1 ∈ K ∨ 8 ∈ K) → (2 ∈ K ∨ 5 ∈ K) →
      (3 ∈ K ∨ 6 ∈ K) → (3 ∈ K ∨ 7 ∈ K) → (6 ∈ K ∨ 7 ∈ K) → 5 ≤ K.card := by
    intro K h09 h18 h25 h36 h37 h67
    let w (i : Fin 11) : ℕ := if i ∈ K then 1 else 0
    have ew (u v : Fin 11) (h : u ∈ K ∨ v ∈ K) : 1 ≤ w u + w v := by
      rcases h with hu | hv
      · simp [w, hu]
      · simp [w, hv]
    have c0 := ew 0 9 h09
    have c1 := ew 1 8 h18
    have c2 := ew 2 5 h25
    have c3 := ew 3 6 h36
    have c4 := ew 3 7 h37
    have c5 := ew 6 7 h67
    have hw : ∑ i : Fin 11, w i = K.card := by simp [w]
    rw [Fin.sum_univ_succ] at hw
    simp [Fin.sum_univ_succ] at hw
    omega
  have hcover_badpair_ge6 : ∀ (K : Finset (Fin 11)) (E : Finset (Sym2 (Fin 11))),
      (E = {s(0, 10), s(5, 8)} ∨ E = {s(1, 4), s(5, 9)} ∨
       E = {s(2, 10), s(8, 9)} ∨ E = {s(4, 10), s(5, 9)}) →
      (G0.deleteEdges ↑E).IsVertexCover (K : Set (Fin 11)) → 6 ≤ K.card := by
    intro K E hE hK
    let w (i : Fin 11) : ℕ := if i ∈ K then 1 else 0
    have ew (u v : Fin 11) (he : G0.Adj u v) (hn : s(u, v) ∉ E) : 1 ≤ w u + w v := by
      have hadj : (G0.deleteEdges ↑E).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨he, hn⟩
      rcases hK hadj with hu | hv
      · change u ∈ K at hu; simp [w, hu]
      · change v ∈ K at hv; simp [w, hv]
    have hw : ∑ i : Fin 11, w i = K.card := by simp [w]
    rw [Fin.sum_univ_succ] at hw
    simp [Fin.sum_univ_succ] at hw
    rcases hE with rfl | rfl | rfl | rfl
    · have e0 := ew 1 4 ((hadjN_iff 1 4).1 rfl) (by decide)
      have e1 := ew 4 8 ((hadjN_iff 4 8).1 rfl) (by decide)
      have e2 := ew 8 1 ((hadjN_iff 8 1).1 rfl) (by decide)
      have e3 := ew 3 6 ((hadjN_iff 3 6).1 rfl) (by decide)
      have e4 := ew 6 7 ((hadjN_iff 6 7).1 rfl) (by decide)
      have e5 := ew 7 3 ((hadjN_iff 7 3).1 rfl) (by decide)
      have e6 := ew 0 9 ((hadjN_iff 0 9).1 rfl) (by decide)
      have e7 := ew 2 5 ((hadjN_iff 2 5).1 rfl) (by decide)
      omega
    · have e0 := ew 3 6 ((hadjN_iff 3 6).1 rfl) (by decide)
      have e1 := ew 6 7 ((hadjN_iff 6 7).1 rfl) (by decide)
      have e2 := ew 7 3 ((hadjN_iff 7 3).1 rfl) (by decide)
      have e3 := ew 1 8 ((hadjN_iff 1 8).1 rfl) (by decide)
      have e4 := ew 4 10 ((hadjN_iff 4 10).1 rfl) (by decide)
      have e5 := ew 2 5 ((hadjN_iff 2 5).1 rfl) (by decide)
      have e6 := ew 0 9 ((hadjN_iff 0 9).1 rfl) (by decide)
      omega
    · have e0 := ew 1 4 ((hadjN_iff 1 4).1 rfl) (by decide)
      have e1 := ew 4 8 ((hadjN_iff 4 8).1 rfl) (by decide)
      have e2 := ew 8 1 ((hadjN_iff 8 1).1 rfl) (by decide)
      have e3 := ew 3 6 ((hadjN_iff 3 6).1 rfl) (by decide)
      have e4 := ew 6 7 ((hadjN_iff 6 7).1 rfl) (by decide)
      have e5 := ew 7 3 ((hadjN_iff 7 3).1 rfl) (by decide)
      have e6 := ew 0 9 ((hadjN_iff 0 9).1 rfl) (by decide)
      have e7 := ew 2 5 ((hadjN_iff 2 5).1 rfl) (by decide)
      omega
    · have e0 := ew 1 4 ((hadjN_iff 1 4).1 rfl) (by decide)
      have e1 := ew 4 8 ((hadjN_iff 4 8).1 rfl) (by decide)
      have e2 := ew 8 1 ((hadjN_iff 8 1).1 rfl) (by decide)
      have e3 := ew 3 6 ((hadjN_iff 3 6).1 rfl) (by decide)
      have e4 := ew 6 7 ((hadjN_iff 6 7).1 rfl) (by decide)
      have e5 := ew 7 3 ((hadjN_iff 7 3).1 rfl) (by decide)
      have e6 := ew 0 9 ((hadjN_iff 0 9).1 rfl) (by decide)
      have e7 := ew 2 5 ((hadjN_iff 2 5).1 rfl) (by decide)
      omega
  have hexMinCover : ∀ U : Finset (Sym2 (Fin 11)), ∃ K : Finset (Fin 11), IsMinCover (G0.deleteEdges ↑U) K := by
    classical
    intro U
    let H := G0.deleteEdges (↑U : Set (Sym2 (Fin 11)))
    let S : Finset (Finset (Fin 11)) := Finset.univ.filter fun K => H.IsVertexCover (K : Set (Fin 11))
    have hS : S.Nonempty := ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u _ _ => Or.inl (Finset.mem_univ u)⟩⟩
    obtain ⟨K, hK, hmin⟩ := Finset.exists_min_image S Finset.card hS
    exact ⟨K, (Finset.mem_filter.mp hK).2, fun K' hK' => hmin K' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK'⟩)⟩
  have hcover_lift : ∀ (U : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11)),
      (G0.deleteEdges ↑U).IsVertexCover (K : Set (Fin 11)) → 7 ≤ K.card + U.card := by
    intro U K hK
    let X : Finset (Fin 11) := U.image fun e => e.out.1
    have hX : X.card ≤ U.card := Finset.card_image_le
    have hfull : G0.IsVertexCover (↑(K ∪ X) : Set (Fin 11)) := by
      intro u v huv
      by_cases he : s(u, v) ∈ U
      · have hvx : s(u, v).out.1 ∈ X := Finset.mem_image_of_mem _ he
        have hh := Sym2.out_fst_mem s(u, v)
        rw [Sym2.mem_iff] at hh
        rcases hh with h | h
        · exact Or.inl (Finset.mem_union_right _ (h ▸ hvx))
        · exact Or.inr (Finset.mem_union_right _ (h ▸ hvx))
      · rcases hK (SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩) with hu | hv
        · exact Or.inl (Finset.mem_union_left X hu)
        · exact Or.inr (Finset.mem_union_left X hv)
    have h7 := hcover_ge7 (K ∪ X) hfull
    have hu := Finset.card_union_le K X
    omega
  let eList : List (Fin 11 × Fin 11) :=
    [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
     (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let eListN : List (ℕ × ℕ) :=
    [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
     (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let neqE (c v u1 v1 : ℕ) : Bool := !((c == u1 && v == v1) || (c == v1 && v == u1))
  let okHit (c v u1 v1 u2 v2 p q : ℕ) : Bool :=
    adjN c v && neqE c v u1 v1 && neqE c v u2 v2 && (v != p) && (v != q)
  let checkOne (i j p q : ℕ) : Bool :=
    let ei := eListN.getD i (0, 0)
    let ej := eListN.getD j (0, 0)
    !adjN p q &&
    (((ei.1 != ej.1 && ei.1 != ej.2) || ei.1 == p || ei.1 == q) &&
     ((ei.2 != ej.1 && ei.2 != ej.2) || ei.2 == p || ei.2 == q)) &&
    (List.range 11).all fun c =>
      !((okHit c ei.1 ei.1 ei.2 ej.1 ej.2 p q || okHit c ei.2 ei.1 ei.2 ej.1 ej.2 p q) &&
        (okHit c ej.1 ei.1 ei.2 ej.1 ej.2 p q || okHit c ej.2 ei.1 ei.2 ej.1 ej.2 p q))
  let wit : List (ℕ × ℕ × ℕ × ℕ) :=
    [(0, 1, 0, 1), (0, 2, 4, 9), (0, 3, 9, 10), (0, 4, 0, 5), (0, 5, 9, 10), (0, 6, 6, 9),
     (0, 7, 9, 10), (0, 8, 4, 9), (0, 9, 9, 10), (0, 10, 9, 10), (0, 11, 9, 10), (0, 12, 6, 8),
     (0, 13, 9, 10), (0, 14, 9, 10), (0, 15, 9, 10), (1, 2, 9, 10), (1, 3, 8, 10), (1, 4, 4, 5),
     (1, 5, 9, 10), (1, 6, 9, 10), (1, 7, 7, 10), (1, 8, 6, 8), (1, 9, 9, 10), (1, 11, 9, 10),
     (1, 12, 2, 7), (1, 13, 9, 10), (1, 14, 9, 10), (1, 15, 9, 10), (2, 3, 0, 1), (2, 4, 4, 5),
     (2, 5, 9, 10), (2, 6, 6, 8), (2, 7, 9, 10), (2, 8, 4, 5), (2, 9, 4, 5), (2, 10, 9, 10),
     (2, 12, 6, 8), (2, 13, 9, 10), (2, 14, 9, 10), (2, 15, 9, 10), (3, 4, 6, 8), (3, 5, 8, 10),
     (3, 6, 9, 10), (3, 7, 6, 8), (3, 8, 6, 8), (3, 9, 9, 10), (3, 10, 6, 8), (3, 11, 9, 10),
     (3, 12, 6, 8), (3, 13, 9, 10), (3, 14, 9, 10), (3, 15, 6, 8), (4, 5, 2, 7), (4, 6, 6, 8),
     (4, 7, 4, 5), (4, 8, 4, 5), (4, 9, 4, 5), (4, 10, 4, 5), (4, 11, 4, 5), (4, 12, 2, 7),
     (4, 13, 9, 10), (4, 14, 9, 10), (4, 15, 9, 10), (5, 6, 9, 10), (5, 7, 9, 10), (5, 8, 6, 8),
     (5, 9, 9, 10), (5, 10, 9, 10), (5, 11, 9, 10), (5, 12, 9, 10), (5, 13, 9, 10), (5, 14, 9, 10),
     (6, 7, 0, 3), (6, 8, 6, 8), (6, 9, 9, 10), (6, 10, 9, 10), (6, 11, 9, 10), (6, 12, 6, 8),
     (6, 13, 6, 8), (6, 14, 9, 10), (6, 15, 9, 10), (7, 8, 6, 8), (7, 9, 9, 10), (7, 10, 2, 7),
     (7, 11, 9, 10), (7, 12, 2, 7), (7, 13, 9, 10), (7, 14, 2, 7), (7, 15, 9, 10), (8, 9, 4, 5),
     (8, 10, 6, 8), (8, 11, 9, 10), (8, 12, 6, 8), (8, 13, 9, 10), (8, 14, 9, 10), (8, 15, 6, 8),
     (9, 10, 4, 5), (9, 12, 9, 10), (9, 13, 9, 10), (9, 14, 9, 10), (9, 15, 4, 9), (10, 11, 4, 5),
     (10, 12, 2, 7), (10, 13, 9, 10), (10, 14, 9, 10), (10, 15, 6, 8), (11, 12, 9, 10),
     (11, 13, 9, 10), (11, 14, 9, 10), (11, 15, 9, 10), (12, 13, 6, 8), (12, 14, 2, 7),
     (12, 15, 9, 10), (13, 14, 6, 9), (13, 15, 9, 10), (14, 15, 9, 10)]
  have hwit_ok : wit.all (fun t => Nat.blt t.2.2.1 11 && Nat.blt t.2.2.2 11 && checkOne t.1 t.2.1 t.2.2.1 t.2.2.2) = true := by
    dsimp only [wit, checkOne, okHit, neqE, adjN, nbrsList, eListN]; decide +kernel
  have hwit_cov : (List.range 16).all (fun i => (List.range 16).all fun j =>
      !(Nat.blt i j) || (i == 1 && j == 10) || (i == 2 && j == 11) ||
      (i == 5 && j == 15) || (i == 9 && j == 11) ||
      wit.any fun t => t.1 == i && t.2.1 == j) = true := by
    dsimp only [wit]; decide +kernel
  have heListN_eq : ∀ i : Fin 16,
      (eListN.getD i.val (0, 0)).1 = ((eList.getD i.val (0, 0)).1).val ∧
      (eListN.getD i.val (0, 0)).2 = ((eList.getD i.val (0, 0)).2).val := by
    dsimp [eList, eListN]; decide +kernel
  have h116 : ∀ i j : Fin 16, i < j →
      ((i.val = 1 ∧ j.val = 10) ∨ (i.val = 2 ∧ j.val = 11) ∨
       (i.val = 5 ∧ j.val = 15) ∨ (i.val = 9 ∧ j.val = 11)) ∨
      ∃ p q : Fin 11, ¬ G0.Adj p q ∧
        (∀ v : Fin 11,
          (v = (eList.getD i.val (0, 0)).1 ∨ v = (eList.getD i.val (0, 0)).2) →
          (v = (eList.getD j.val (0, 0)).1 ∨ v = (eList.getD j.val (0, 0)).2) →
          v = p ∨ v = q) ∧
        (∀ c : Fin 11,
          ¬ ((∃ v : Fin 11, G0.Adj c v ∧
              s(c, v) ≠ s((eList.getD i.val (0, 0)).1, (eList.getD i.val (0, 0)).2) ∧
              s(c, v) ≠ s((eList.getD j.val (0, 0)).1, (eList.getD j.val (0, 0)).2) ∧
              v ≠ p ∧ v ≠ q ∧
              (v = (eList.getD i.val (0, 0)).1 ∨ v = (eList.getD i.val (0, 0)).2)) ∧
             (∃ v : Fin 11, G0.Adj c v ∧
              s(c, v) ≠ s((eList.getD i.val (0, 0)).1, (eList.getD i.val (0, 0)).2) ∧
              s(c, v) ≠ s((eList.getD j.val (0, 0)).1, (eList.getD j.val (0, 0)).2) ∧
              v ≠ p ∧ v ≠ q ∧
              (v = (eList.getD j.val (0, 0)).1 ∨ v = (eList.getD j.val (0, 0)).2)))) := by
    intro i j hij
    have hcov_ij := List.all_eq_true.mp (List.all_eq_true.mp hwit_cov i.val (List.mem_range.mpr i.isLt))
      j.val (List.mem_range.mpr j.isLt)
    have hlt_b : Nat.blt i.val j.val = true := Nat.blt_eq.mpr hij
    simp only [hlt_b, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hcov_ij
    rcases hcov_ij with (((h1' | h2') | h3') | h4') | hfound
    · exact Or.inl (Or.inl h1')
    · exact Or.inl (Or.inr (Or.inl h2'))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h3')))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h4')))
    · right
      rw [List.any_eq_true] at hfound
      obtain ⟨t, htw, htij⟩ := hfound
      simp only [Bool.and_eq_true, beq_iff_eq] at htij
      obtain ⟨ht1, ht2⟩ := htij
      have htok := List.all_eq_true.mp hwit_ok t htw
      simp only [Bool.and_eq_true, Nat.blt_eq] at htok
      obtain ⟨⟨hp11, hq11⟩, hchk⟩ := htok
      rw [ht1, ht2] at hchk
      let p : Fin 11 := ⟨t.2.2.1, hp11⟩
      let q : Fin 11 := ⟨t.2.2.2, hq11⟩
      have hei := heListN_eq i
      have hej := heListN_eq j
      dsimp [checkOne] at hchk
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hchk
      obtain ⟨⟨hna, hsing1, hsing2⟩, hcent⟩ := hchk
      refine ⟨p, q, ?_, ?_, ?_⟩
      · intro hadj
        have := (hadjN_iff p q).2 hadj
        rw [hna] at this; exact Bool.false_ne_true this
      · intro v hvi hvj
        rcases hvi with rfl | rfl
        · simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hsing1
          rcases hsing1 with (⟨h1', h2'⟩ | hp) | hq
          · rcases hvj with h | h
            · exact absurd (by rw [hei.1, hej.1, h]) h1'
            · exact absurd (by rw [hei.1, hej.2, h]) h2'
          · exact Or.inl (Fin.ext (hei.1.symm.trans hp))
          · exact Or.inr (Fin.ext (hei.1.symm.trans hq))
        · simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hsing2
          rcases hsing2 with (⟨h1', h2'⟩ | hp) | hq
          · rcases hvj with h | h
            · exact absurd (by rw [hei.2, hej.1, h]) h1'
            · exact absurd (by rw [hei.2, hej.2, h]) h2'
          · exact Or.inl (Fin.ext (hei.2.symm.trans hp))
          · exact Or.inr (Fin.ext (hei.2.symm.trans hq))
      · intro c hc_both
        obtain ⟨⟨v1, hv1a, hv1i, hv1j, hv1p, hv1q, hv1e⟩, ⟨v2, hv2a, hv2i, hv2j, hv2p, hv2q, hv2e⟩⟩ := hc_both
        have hmk : ∀ (v : Fin 11), G0.Adj c v →
            s(c, v) ≠ s((eList.getD i.val (0, 0)).1, (eList.getD i.val (0, 0)).2) →
            s(c, v) ≠ s((eList.getD j.val (0, 0)).1, (eList.getD j.val (0, 0)).2) →
            v ≠ p → v ≠ q →
            okHit c.val v.val (eListN.getD i.val (0, 0)).1 (eListN.getD i.val (0, 0)).2
              (eListN.getD j.val (0, 0)).1 (eListN.getD j.val (0, 0)).2 p.val q.val = true := by
          intro v hva hvi hvj hvp hvq
          simp only [okHit, neqE, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
            Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_iff_ne]
          refine ⟨⟨⟨⟨(hadjN_iff c v).2 hva, ?_⟩, ?_⟩, Fin.val_ne_of_ne hvp⟩, Fin.val_ne_of_ne hvq⟩
          · rw [hei.1, hei.2]
            constructor
            · by_cases h1' : c = (eList.getD i.val (0, 0)).1
              · right; intro h2'; exact hvi (by rw [h1', Fin.ext h2'])
              · exact Or.inl (Fin.val_ne_of_ne h1')
            · by_cases h1' : c = (eList.getD i.val (0, 0)).2
              · right; intro h2'; exact hvi (by rw [h1', Fin.ext h2', Sym2.eq_swap])
              · exact Or.inl (Fin.val_ne_of_ne h1')
          · rw [hej.1, hej.2]
            constructor
            · by_cases h1' : c = (eList.getD j.val (0, 0)).1
              · right; intro h2'; exact hvj (by rw [h1', Fin.ext h2'])
              · exact Or.inl (Fin.val_ne_of_ne h1')
            · by_cases h1' : c = (eList.getD j.val (0, 0)).2
              · right; intro h2'; exact hvj (by rw [h1', Fin.ext h2', Sym2.eq_swap])
              · exact Or.inl (Fin.val_ne_of_ne h1')
        have hok1 := hmk v1 hv1a hv1i hv1j hv1p hv1q
        have hok2 := hmk v2 hv2a hv2i hv2j hv2p hv2q
        have hc' := hcent c.val (List.mem_range.mpr c.isLt)
        dsimp only [p, q] at hok1 hok2
        rcases hv1e with rfl | rfl <;> rcases hv2e with rfl | rfl <;>
          simp only [← hei.1, ← hei.2, ← hej.1, ← hej.2] at hok1 hok2 <;>
          (rw [hok1, hok2] at hc'; simp at hc')
  have heList_mem : ∀ u v : Fin 11, G0.Adj u v →
      ∃ i : Fin 16, s(u, v) = s((eList.getD i.val (0, 0)).1, (eList.getD i.val (0, 0)).2) := by
    have haux : ∀ u v : Fin 11, adjN u.val v.val = true →
        (List.finRange 16).any (fun i =>
          let e := eListN.getD i.val (0, 0)
          (u.val == e.1 && v.val == e.2) || (u.val == e.2 && v.val == e.1)) = true := by
      dsimp [eListN, nbrsList, adjN]; decide +kernel
    intro u v huv
    have h1' := haux u v ((hadjN_iff u v).2 huv)
    rw [List.any_eq_true] at h1'
    obtain ⟨i, _, hi⟩ := h1'
    have hei := heListN_eq i
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, hei.1, hei.2] at hi
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨i, by rw [Fin.ext h1, Fin.ext h2]⟩
    · exact ⟨i, by rw [Fin.ext h1, Fin.ext h2, Sym2.eq_swap]⟩
  let ValidWire (U : Finset (Sym2 (Fin 11))) (S : Finset (Fin 11)) : Prop :=
    (∃ v : Fin 11, S = {v}) ∨ (∃ c : Fin 11, ∀ v ∈ S, G0.Adj c v ∧ s(c, v) ∉ U)
  have hValidObs : ∀ (U E : Finset (Sym2 (Fin 11))) (F : Finset (Finset (Fin 11))),
      E ⊆ U → (∀ e ∈ E, e ∈ G0.edgeFinset) →
      (∀ S ∈ F, ValidWire U S) →
      (∀ u v : Fin 11, s(u, v) ∈ E → ∀ S ∈ F, u ∈ S ∨ v ∈ S) →
      (∀ p q : Fin 11, ¬ G0.Adj p q → ∃ S ∈ F, p ∉ S ∧ q ∉ S) →
      E.card ≤ 1 ∨
        (E = {s(0, 10), s(5, 8)} ∨ E = {s(1, 4), s(5, 9)} ∨
         E = {s(2, 10), s(8, 9)} ∨ E = {s(4, 10), s(5, 9)}) := by
    intro U E F hEU hEG hFvalid hFcov hFclean
    have hpair_bad : ∀ i j : Fin 16, i < j →
        s((eList.getD i.val (0, 0)).1, (eList.getD i.val (0, 0)).2) ∈ E →
        s((eList.getD j.val (0, 0)).1, (eList.getD j.val (0, 0)).2) ∈ E →
        (i.val = 1 ∧ j.val = 10) ∨ (i.val = 2 ∧ j.val = 11) ∨
        (i.val = 5 ∧ j.val = 15) ∨ (i.val = 9 ∧ j.val = 11) := by
      intro i j hij hiE hjE
      rcases h116 i j hij with hbad | ⟨p, q, hna, hsing, hcent⟩
      · exact hbad
      · exfalso
        obtain ⟨S, hSF, hpS, hqS⟩ := hFclean p q hna
        have hSi := hFcov _ _ hiE S hSF
        have hSj := hFcov _ _ hjE S hSF
        rcases hFvalid S hSF with ⟨v, rfl⟩ | ⟨c, hc⟩
        · simp only [Finset.mem_singleton] at hSi hSj hpS hqS
          rcases hsing v (hSi.imp Eq.symm Eq.symm) (hSj.imp Eq.symm Eq.symm) with rfl | rfl
          · exact hpS rfl
          · exact hqS rfl
        · apply hcent c
          constructor
          · rcases hSi with hu | hv
            · exact ⟨_, (hc _ hu).1, fun he => (hc _ hu).2 (he ▸ hEU hiE),
                fun he => (hc _ hu).2 (he ▸ hEU hjE), fun h => hpS (h ▸ hu),
                fun h => hqS (h ▸ hu), Or.inl rfl⟩
            · exact ⟨_, (hc _ hv).1, fun he => (hc _ hv).2 (he ▸ hEU hiE),
                fun he => (hc _ hv).2 (he ▸ hEU hjE), fun h => hpS (h ▸ hv),
                fun h => hqS (h ▸ hv), Or.inr rfl⟩
          · rcases hSj with hu | hv
            · exact ⟨_, (hc _ hu).1, fun he => (hc _ hu).2 (he ▸ hEU hiE),
                fun he => (hc _ hu).2 (he ▸ hEU hjE), fun h => hpS (h ▸ hu),
                fun h => hqS (h ▸ hu), Or.inl rfl⟩
            · exact ⟨_, (hc _ hv).1, fun he => (hc _ hv).2 (he ▸ hEU hiE),
                fun he => (hc _ hv).2 (he ▸ hEU hjE), fun h => hpS (h ▸ hv),
                fun h => hqS (h ▸ hv), Or.inr rfl⟩
    by_cases hle1 : E.card ≤ 1
    · exact Or.inl hle1
    · right
      have hidx : ∀ e ∈ E, ∃ i : Fin 16, e = s((eList.getD i.val (0, 0)).1, (eList.getD i.val (0, 0)).2) := by
        intro e he
        have heg := SimpleGraph.mem_edgeFinset.mp (hEG e he)
        induction e using Sym2.ind with
        | _ u v => exact heList_mem u v heg
      have h2 : 1 < E.card := by omega
      obtain ⟨e1, he1, e2, he2, hne12⟩ := Finset.one_lt_card.mp h2
      obtain ⟨i1, rfl⟩ := hidx e1 he1
      obtain ⟨i2, rfl⟩ := hidx e2 he2
      have hi12 : i1 ≠ i2 := fun h => hne12 (by rw [h])
      have hord : ∃ a b : Fin 16, a < b ∧
          s((eList.getD a.val (0, 0)).1, (eList.getD a.val (0, 0)).2) ∈ E ∧
          s((eList.getD b.val (0, 0)).1, (eList.getD b.val (0, 0)).2) ∈ E := by
        rcases lt_or_gt_of_ne hi12 with hlt | hlt
        · exact ⟨i1, i2, hlt, he1, he2⟩
        · exact ⟨i2, i1, hlt, he2, he1⟩
      obtain ⟨a, b, hab, haE, hbE⟩ := hord
      have hsub : E ⊆ {s((eList.getD a.val (0, 0)).1, (eList.getD a.val (0, 0)).2),
                       s((eList.getD b.val (0, 0)).1, (eList.getD b.val (0, 0)).2)} := by
        intro e he
        obtain ⟨k, rfl⟩ := hidx e he
        by_contra hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        have hka : k ≠ a := fun h => hnot.1 (by rw [h])
        have hkb : k ≠ b := fun h => hnot.2 (by rw [h])
        have h1' := hpair_bad a b hab haE hbE
        rcases lt_or_gt_of_ne hka with h1 | h1
        · have h2' := hpair_bad k a h1 he haE
          have h3' := hpair_bad k b (lt_trans h1 hab) he hbE
          omega
        · rcases lt_or_gt_of_ne hkb with h2 | h2
          · have h2' := hpair_bad a k h1 haE he
            have h3' := hpair_bad k b h2 he hbE
            omega
          · have h2' := hpair_bad a k h1 haE he
            have h3' := hpair_bad b k h2 hbE he
            omega
      have hEq : E = {s((eList.getD a.val (0, 0)).1, (eList.getD a.val (0, 0)).2),
                      s((eList.getD b.val (0, 0)).1, (eList.getD b.val (0, 0)).2)} := by
        apply Finset.Subset.antisymm hsub
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact haE
        · exact hbE
      have hbad := hpair_bad a b hab haE hbE
      rw [hEq]
      rcases hbad with ⟨ha1, hb10⟩ | ⟨ha2, hb11⟩ | ⟨ha5, hb15⟩ | ⟨ha9, hb11⟩
      · left; simp [ha1, hb10, eList]
      · right; left; simp [ha2, hb11, eList]
      · right; right; left; simp [ha5, hb15, eList]
      · right; right; right; simp [ha9, hb11, eList]
  let stepW (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hfoldW_len : ∀ (gs : List Gate) (w : List Bool), (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; simp only [List.foldl_cons]; rw [ih]; simp [stepW]; omega
  have hfoldW_getD : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih (stepW w g) i (by simp [stepW]; omega)]
      simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hwire_input : ∀ (C : Circuit) (x : Fin 11 → Bool) (v : Fin 11), wireVal 11 C v.val x = x v := by
    intro C x v
    change (C.gates.foldl stepW (List.ofFn x)).getD v.val false = x v
    rw [hfoldW_getD C.gates (List.ofFn x) v.val (by simp)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [v.isLt]
  have hgate_eval : ∀ (C : Circuit) (x : Fin 11 → Bool) (k : ℕ), k < C.gates.length →
      gateVal 11 C k x = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
        if i < 11 + k then wireVal 11 C i x else false) := by
    intro C x k hk
    let gk : Gate := C.gates[k]
    have hsplit : C.gates = C.gates.take k ++ gk :: C.gates.drop (k + 1) := by
      simp only [gk]
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hga : gateAt C k = gk := by
      unfold gateAt; simp only [gk, List.getD_eq_getElem?_getD, hk, List.getElem?_eq_getElem, Option.getD_some]
    rw [hga]
    let w0 := (C.gates.take k).foldl stepW (List.ofFn x)
    have hw0_len : w0.length = 11 + k := by
      simp [w0, hfoldW_len, Nat.min_eq_left hk.le]
    have h1' : gateVal 11 C k x = gk.op.eval (gk.inputs.map fun i => w0.getD i false) := by
      change (C.gates.foldl stepW (List.ofFn x)).getD (11 + k) false = _
      rw [hsplit, List.foldl_append, List.foldl_cons]
      rw [hfoldW_getD (C.gates.drop (k + 1)) (stepW w0 gk) (11 + k) (by simp [stepW]; omega)]
      simp [stepW, List.getD_eq_getElem?_getD, hw0_len]
    rw [h1']
    congr 1
    refine List.map_congr_left fun i _ => ?_
    by_cases hi : i < 11 + k
    · simp only [hi, ↓reduceIte]
      change w0.getD i false = (C.gates.foldl stepW (List.ofFn x)).getD i false
      rw [hsplit, List.foldl_append]
      exact (hfoldW_getD _ w0 i (by omega)).symm
    · simp only [hi, ↓reduceIte]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show w0.length ≤ i by omega)]
  have hgateAt_mem : ∀ k < D.gates.length, gateAt D k ∈ D.gates := by
    intro k hk
    have : gateAt D k = D.gates[k] := by
      unfold gateAt; simp only [List.getD_eq_getElem?_getD, hk, List.getElem?_eq_getElem, Option.getD_some]
    rw [this]
    exact List.getElem_mem hk
  have hinputs_eq : ∀ k < D.gates.length, (gateAt D k).inputs = [opnd D k 0, opnd D k 1] := by
    intro k hk
    have hl : (gateAt D k).inputs.length = 2 := hLen2 _ (hgateAt_mem k hk)
    rcases h : (gateAt D k).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · rw [h] at hl; simp at hl
    · rw [h] at hl; simp at hl
    · unfold opnd; rw [h]; rfl
    · rw [h] at hl; simp at hl
  have hopnd_lt : ∀ k < D.gates.length, ∀ b : Fin 2, opnd D k b < 11 + k := by
    intro k hk b
    apply hReads k hk
    rw [hinputs_eq k hk]
    fin_cases b <;> simp
  have hgate_and : ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ x : Fin 11 → Bool,
      gateVal 11 D k x = (wireVal 11 D (opnd D k 0) x && wireVal 11 D (opnd D k 1) x) := by
    intro k hk hop x
    rw [hgate_eval D x k hk, hop, hinputs_eq k hk]
    dsimp only [GateOp.eval]
    simp only [List.map_cons, List.map_nil, hopnd_lt k hk 0, hopnd_lt k hk 1, ↓reduceIte,
      List.all_cons, List.all_nil, id_eq, Bool.and_true]
  have hgate_or : ∀ k < D.gates.length, (gateAt D k).op = GateOp.or → ∀ x : Fin 11 → Bool,
      gateVal 11 D k x = (wireVal 11 D (opnd D k 0) x || wireVal 11 D (opnd D k 1) x) := by
    intro k hk hop x
    rw [hgate_eval D x k hk, hop, hinputs_eq k hk]
    dsimp only [GateOp.eval]
    simp only [List.map_cons, List.map_nil, hopnd_lt k hk 0, hopnd_lt k hk 1, ↓reduceIte,
      List.any_cons, List.any_nil, id_eq, Bool.or_false]
  have horFold_len : ∀ (gs : List Gate) (cs : List (List ℕ)), (gs.foldl (orStep 11) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs; simp only [List.foldl_cons]; rw [ih]
      change (cs ++ [_]).length + gs.length = _
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have horFold_getD : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ), k < cs.length →
      (gs.foldl (orStep 11) cs).getD k [] = cs.getD k [] := by
    intro gs
    induction gs with
    | nil => intro cs k _; rfl
    | cons g gs ih =>
      intro cs k hk
      simp only [List.foldl_cons]
      have hlen1 : k < (orStep 11 cs g).length := by
        change k < (cs ++ [_]).length
        simp only [List.length_append, List.length_singleton]; omega
      rw [ih (orStep 11 cs g) k hlen1]
      unfold orStep
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have horSets_mem_iff : ∀ k < D.gates.length, ∀ g : ℕ,
      g ∈ (orSets 11 D).getD k [] ↔ g = k ∨ ((gateAt D k).op = GateOp.or ∧
        ∃ w ∈ (gateAt D k).inputs, 11 ≤ w ∧ w < 11 + k ∧ g ∈ (orSets 11 D).getD (w - 11) []) := by
    intro k hk g
    let gk : Gate := D.gates[k]
    have hsplit : D.gates = D.gates.take k ++ gk :: D.gates.drop (k + 1) := by
      simp only [gk]
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hga : gateAt D k = gk := by
      unfold gateAt; simp only [gk, List.getD_eq_getElem?_getD, hk, List.getElem?_eq_getElem, Option.getD_some]
    rw [hga]
    let pre := (D.gates.take k).foldl (orStep 11) []
    have hpre_len : pre.length = k := by simp [pre, horFold_len, Nat.min_eq_left hk.le]
    have hc : orSets 11 D = (D.gates.drop (k + 1)).foldl (orStep 11) (orStep 11 pre gk) := by
      unfold orSets; rw (occs := [1]) [hsplit]; rw [List.foldl_append, List.foldl_cons]
    have hstep_len : (orStep 11 pre gk).length = k + 1 := by
      change (pre ++ [_]).length = k + 1
      simp only [List.length_append, List.length_singleton, hpre_len]
    have h1' : (orSets 11 D).getD k [] = (orStep 11 pre gk).getD k [] := by
      rw [hc, horFold_getD _ _ k (by omega)]
    have h2' : ∀ m < k, (orSets 11 D).getD m [] = pre.getD m [] := by
      intro m hm
      rw [hc, horFold_getD _ _ m (by omega)]
      unfold orStep
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show m < pre.length by omega)]
    rw [h1']
    have hget : (orStep 11 pre gk).getD k [] =
        k :: (if gk.op = GateOp.or then
          (gk.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + k))).flatMap (fun w => pre.getD (w - 11) [])
          else []) := by
      unfold orStep
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right hpre_len.le, hpre_len, Nat.sub_self]
      simp
    rw [hget]
    by_cases hop : gk.op = GateOp.or
    · simp only [hop, ↓reduceIte, true_and, List.mem_cons, List.mem_flatMap, List.mem_filter,
        decide_eq_true_eq]
      constructor
      · rintro (rfl | ⟨w, ⟨hw, h11, hlt⟩, hg⟩)
        · exact Or.inl rfl
        · refine Or.inr ⟨w, hw, h11, hlt, ?_⟩
          rw [h2' (w - 11) (by omega)]
          exact hg
      · rintro (rfl | ⟨w, hw, h11, hlt, hg⟩)
        · exact Or.inl rfl
        · refine Or.inr ⟨w, ⟨hw, h11, hlt⟩, ?_⟩
          rw [h2' (w - 11) (by omega)] at hg
          exact hg
    · simp [hop]
  have horReaches_iff : ∀ k < D.gates.length, ∀ g : ℕ,
      OrReaches 11 D (11 + k) g ↔ g = k ∨ ((gateAt D k).op = GateOp.or ∧
        (OrReaches 11 D (opnd D k 0) g ∨ OrReaches 11 D (opnd D k 1) g)) := by
    intro k hk g
    unfold OrReaches
    simp only [Nat.le_add_right, true_and, Nat.add_sub_cancel_left]
    rw [horSets_mem_iff k hk g, hinputs_eq k hk]
    constructor
    · rintro (rfl | ⟨hop, w, hw, h11, hlt, hg⟩)
      · exact Or.inl rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inr ⟨hop, Or.inl ⟨h11, hg⟩⟩
        · exact Or.inr ⟨hop, Or.inr ⟨h11, hg⟩⟩
    · rintro (rfl | ⟨hop, ⟨h11, hg⟩ | ⟨h11, hg⟩⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hop, opnd D k 0, by simp, h11, hopnd_lt k hk 0, hg⟩
      · exact Or.inr ⟨hop, opnd D k 1, by simp, h11, hopnd_lt k hk 1, hg⟩
  have horReaches_bounds : ∀ w g : ℕ, OrReaches 11 D w g → 11 + g ≤ w ∧ g < D.gates.length ∧ w < 11 + D.gates.length := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro g hr
      obtain ⟨h11, hmem⟩ := hr
      have hwlt : w - 11 < D.gates.length := by
        by_contra hge
        have hlen : (orSets 11 D).length = D.gates.length := by
          unfold orSets; simpa using horFold_len D.gates []
        have : (orSets 11 D).getD (w - 11) [] = [] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (orSets 11 D).length ≤ w - 11 by omega)]
          rfl
        rw [this] at hmem
        simp at hmem
      have hwk : w = 11 + (w - 11) := by omega
      rw [hwk] at hmem ⊢
      have hr' : OrReaches 11 D (11 + (w - 11)) g := ⟨by omega, by simpa using hmem⟩
      rw [horReaches_iff (w - 11) hwlt g] at hr'
      rcases hr' with rfl | ⟨_, h0 | h1'⟩
      · exact ⟨by omega, hwlt, by omega⟩
      · have hlt := hopnd_lt (w - 11) hwlt 0
        have hb := ih (opnd D (w - 11) 0) (by omega) g h0
        omega
      · have hlt := hopnd_lt (w - 11) hwlt 1
        have hb := ih (opnd D (w - 11) 1) (by omega) g h1'
        omega
  have horReaches_trans : ∀ w k g : ℕ, OrReaches 11 D w k → OrReaches 11 D (11 + k) g → OrReaches 11 D w g := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro k g hr1 hr2
      have hb := horReaches_bounds w k hr1
      have hwk : w = 11 + (w - 11) := by omega
      have hwl : w - 11 < D.gates.length := by omega
      rw [hwk] at hr1 ⊢
      rw [horReaches_iff (w - 11) hwl k] at hr1
      rcases hr1 with rfl | ⟨hop, h0 | h1'⟩
      · exact hr2
      · rw [horReaches_iff (w - 11) hwl g]
        exact Or.inr ⟨hop, Or.inl (ih _ (by have := hopnd_lt (w - 11) hwl 0; omega) k g h0 hr2)⟩
      · rw [horReaches_iff (w - 11) hwl g]
        exact Or.inr ⟨hop, Or.inr (ih _ (by have := hopnd_lt (w - 11) hwl 1; omega) k g h1' hr2)⟩
  have horReaches_val : ∀ w g : ℕ, OrReaches 11 D w g → ∀ x : Fin 11 → Bool,
      gateVal 11 D g x = true → wireVal 11 D w x = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro g hr x hg
      have hb := horReaches_bounds w g hr
      have hwk : w = 11 + (w - 11) := by omega
      have hwl : w - 11 < D.gates.length := by omega
      rw [hwk] at hr ⊢
      rw [horReaches_iff (w - 11) hwl g] at hr
      rcases hr with rfl | ⟨hop, h0 | h1'⟩
      · exact hg
      · change gateVal 11 D (w - 11) x = true
        rw [hgate_or (w - 11) hwl hop x]
        have := ih _ (by have := hopnd_lt (w - 11) hwl 0; omega) g h0 x hg
        simp [this]
      · change gateVal 11 D (w - 11) x = true
        rw [hgate_or (w - 11) hwl hop x]
        have := ih _ (by have := hopnd_lt (w - 11) hwl 1; omega) g h1' x hg
        simp [this]
  have hconeFold_len : ∀ (gs : List Gate) (cs : List (List ℕ)), (gs.foldl (coneStep 11) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs; simp only [List.foldl_cons]; rw [ih]
      change (cs ++ [_]).length + gs.length = _
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hconeFold_getD : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ), k < cs.length →
      (gs.foldl (coneStep 11) cs).getD k [] = cs.getD k [] := by
    intro gs
    induction gs with
    | nil => intro cs k _; rfl
    | cons g gs ih =>
      intro cs k hk
      simp only [List.foldl_cons]
      have hlen1 : k < (coneStep 11 cs g).length := by
        change k < (cs ++ [_]).length
        simp only [List.length_append, List.length_singleton]; omega
      rw [ih (coneStep 11 cs g) k hlen1]
      unfold coneStep
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have hinCone_iff : ∀ k < D.gates.length, ∀ i : ℕ,
      InCone 11 D i k ↔ ∃ w ∈ (gateAt D k).inputs, 11 ≤ w ∧ w < 11 + k ∧ (i = w - 11 ∨ InCone 11 D i (w - 11)) := by
    intro k hk i
    unfold InCone
    let gk : Gate := D.gates[k]
    have hsplit : D.gates = D.gates.take k ++ gk :: D.gates.drop (k + 1) := by
      simp only [gk]
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hga : gateAt D k = gk := by
      unfold gateAt; simp only [gk, List.getD_eq_getElem?_getD, hk, List.getElem?_eq_getElem, Option.getD_some]
    rw [hga]
    let pre := (D.gates.take k).foldl (coneStep 11) []
    have hpre_len : pre.length = k := by simp [pre, hconeFold_len, Nat.min_eq_left hk.le]
    have hc : cones 11 D = (D.gates.drop (k + 1)).foldl (coneStep 11) (coneStep 11 pre gk) := by
      unfold cones; rw (occs := [1]) [hsplit]; rw [List.foldl_append, List.foldl_cons]
    have hstep_len : (coneStep 11 pre gk).length = k + 1 := by
      change (pre ++ [_]).length = k + 1
      simp only [List.length_append, List.length_singleton, hpre_len]
    have h1' : (cones 11 D).getD k [] = (coneStep 11 pre gk).getD k [] := by
      rw [hc, hconeFold_getD _ _ k (by omega)]
    have h2' : ∀ m < k, (cones 11 D).getD m [] = pre.getD m [] := by
      intro m hm
      rw [hc, hconeFold_getD _ _ m (by omega)]
      unfold coneStep
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show m < pre.length by omega)]
    rw [h1']
    have hget : (coneStep 11 pre gk).getD k [] =
        (gk.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + k))).flatMap
          (fun w => (w - 11) :: pre.getD (w - 11) []) := by
      unfold coneStep
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right hpre_len.le, hpre_len, Nat.sub_self]
      simp
    rw [hget]
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ⟨w, ⟨hw, h11, hlt⟩, rfl | hi⟩
      · exact ⟨w, hw, h11, hlt, Or.inl rfl⟩
      · refine ⟨w, hw, h11, hlt, Or.inr ?_⟩
        rw [h2' (w - 11) (by omega)]
        exact hi
    · rintro ⟨w, hw, h11, hlt, rfl | hi⟩
      · exact ⟨w, ⟨hw, h11, hlt⟩, Or.inl rfl⟩
      · refine ⟨w, ⟨hw, h11, hlt⟩, Or.inr ?_⟩
        rw [h2' (w - 11) (by omega)] at hi
        exact hi
  have hinCone_step : ∀ k < D.gates.length, ∀ b : Fin 2, ∀ j i : ℕ,
      opnd D k b = 11 + j → (i = j ∨ InCone 11 D i j) → InCone 11 D i k := by
    intro k hk b j i hop hij
    rw [hinCone_iff k hk i]
    have hlt := hopnd_lt k hk b
    refine ⟨opnd D k b, ?_, by omega, hlt, ?_⟩
    · rw [hinputs_eq k hk]; fin_cases b <;> simp
    · simpa [hop] using hij
  have hinCone_trans : ∀ k j i : ℕ, InCone 11 D i j → InCone 11 D j k → InCone 11 D i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro j i hij hjk
      have hkl : k < D.gates.length := by
        by_contra hge
        have hlen : (cones 11 D).length = D.gates.length := by
          unfold cones; simpa using hconeFold_len D.gates []
        unfold InCone at hjk
        have : (cones 11 D).getD k [] = [] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (cones 11 D).length ≤ k by omega)]
          rfl
        rw [this] at hjk; simp at hjk
      rw [hinCone_iff k hkl j] at hjk
      obtain ⟨w, hw, h11, hlt, hjk'⟩ := hjk
      rw [hinCone_iff k hkl i]
      refine ⟨w, hw, h11, hlt, Or.inr ?_⟩
      rcases hjk' with rfl | hjk''
      · exact hij
      · exact ih (w - 11) (by omega) j i hij hjk''
  have horReaches_inCone : ∀ k < D.gates.length, ∀ g : ℕ,
      OrReaches 11 D (11 + k) g → g = k ∨ InCone 11 D g k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk g hr
      rw [horReaches_iff k hk g] at hr
      rcases hr with rfl | ⟨_, h0 | h1'⟩
      · exact Or.inl rfl
      · have hb := horReaches_bounds _ g h0
        have hlt := hopnd_lt k hk 0
        have h0' : OrReaches 11 D (11 + (opnd D k 0 - 11)) g := by
          have : 11 + (opnd D k 0 - 11) = opnd D k 0 := by omega
          rwa [this]
        have hrec := ih (opnd D k 0 - 11) (by omega) (by omega) g h0'
        exact Or.inr (hinCone_step k hk 0 (opnd D k 0 - 11) g (by omega) hrec)
      · have hb := horReaches_bounds _ g h1'
        have hlt := hopnd_lt k hk 1
        have h1'' : OrReaches 11 D (11 + (opnd D k 1 - 11)) g := by
          have : 11 + (opnd D k 1 - 11) = opnd D k 1 := by omega
          rwa [this]
        have hrec := ih (opnd D k 1 - 11) (by omega) (by omega) g h1''
        exact Or.inr (hinCone_step k hk 1 (opnd D k 1 - 11) g (by omega) hrec)
  have horIn_val : ∀ (w : ℕ) (v : Fin 11) (x : Fin 11 → Bool),
      v ∈ orIn 11 D w → x v = true → wireVal 11 D w x = true := by
    intro w v x hv hxv
    unfold orIn at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hv with rfl | ⟨k, hk, hr, hop, hvin⟩
    · exact (hwire_input D x v).trans hxv
    · have hgk : gateVal 11 D k x = true := by
        rw [hgate_or k hk hop x]
        rw [hinputs_eq k hk] at hvin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hvin
        rcases hvin with h | h
        · rw [← h, hwire_input D x v, hxv]; rfl
        · rw [← h, hwire_input D x v, hxv]; simp
      exact horReaches_val w k hr x hgk
  have horIn_mono : ∀ w k : ℕ, OrReaches 11 D w k → orIn 11 D (11 + k) ⊆ orIn 11 D w := by
    intro w k hr v hv
    unfold orIn at hv ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rcases hv with hlt | ⟨j, hj, hrj, hop, hvin⟩
    · omega
    · exact Or.inr ⟨j, hj, horReaches_trans w k j hr hrj, hop, hvin⟩
  have horIn_and : ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → orIn 11 D (11 + k) = ∅ := by
    intro k hk hop
    ext v
    unfold orIn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_or]
    refine ⟨by omega, ?_⟩
    rintro ⟨j, hj, hr, hopj, _⟩
    rw [horReaches_iff k hk j] at hr
    rcases hr with rfl | ⟨hor, _⟩
    · rw [hop] at hopj; cases hopj
    · rw [hop] at hor; cases hor
  have horIn_or_eq : ∀ k < D.gates.length, (gateAt D k).op = GateOp.or →
      orIn 11 D (11 + k) = orIn 11 D (opnd D k 0) ∪ orIn 11 D (opnd D k 1) := by
    intro k hk hop
    ext v
    unfold orIn
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | ⟨j, hj, hr, hopj, hvin⟩)
      · omega
      · rw [horReaches_iff k hk j] at hr
        rcases hr with hjk | ⟨_, h0 | h1'⟩
        · subst hjk
          rw [hinputs_eq j hj] at hvin
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hvin
          rcases hvin with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)
        · exact Or.inl (Or.inr ⟨j, hj, h0, hopj, hvin⟩)
        · exact Or.inr (Or.inr ⟨j, hj, h1', hopj, hvin⟩)
    · rintro ((h | ⟨j, hj, hr, hopj, hvin⟩) | (h | ⟨j, hj, hr, hopj, hvin⟩))
      · refine Or.inr ⟨k, hk, (horReaches_iff k hk k).2 (Or.inl rfl), hop, ?_⟩
        rw [hinputs_eq k hk, h]; simp
      · exact Or.inr ⟨j, hj, (horReaches_iff k hk j).2 (Or.inr ⟨hop, Or.inl hr⟩), hopj, hvin⟩
      · refine Or.inr ⟨k, hk, (horReaches_iff k hk k).2 (Or.inl rfl), hop, ?_⟩
        rw [hinputs_eq k hk, h]; simp
      · exact Or.inr ⟨j, hj, (horReaches_iff k hk j).2 (Or.inr ⟨hop, Or.inr hr⟩), hopj, hvin⟩
  have hpair_false : ∀ p q : Fin 11, ¬ G0.Adj p q → graphFun G0 ∅ (pairInput p q) = false := by
    intro p q hna
    unfold graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_false_iff_not, not_exists, not_and]
    intro u v huv hu hv
    rw [hpi_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact G0.loopless.irrefl _ huv
    · exact hna huv
    · exact hna huv.symm
    · exact G0.loopless.irrefl _ huv
  have horIn_belowF_empty : ∀ k < D.gates.length, BelowF G0 D k → orIn 11 D (11 + k) = ∅ := by
    intro k hk hb
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    have hgv : gateVal 11 D k (pairInput v v) = true :=
      horIn_val (11 + k) v (pairInput v v) hv (hpi_left v v)
    have hgf := hb (pairInput v v) hgv
    rw [hpair_false v v (G0.loopless.irrefl v)] at hgf
    exact Bool.false_ne_true hgf
  have hall_true : ∀ w < 11 + D.gates.length, wireVal 11 D w (fun _ => true) = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases h11 : w < 11
      · exact hwire_input D (fun _ => true) ⟨w, h11⟩
      · have hwl : w - 11 < D.gates.length := by omega
        have hwk : w = 11 + (w - 11) := by omega
        rw [hwk]
        rcases hAndOr _ (hgateAt_mem (w - 11) hwl) with hop | hop
        · change gateVal 11 D (w - 11) (fun _ => true) = true
          rw [hgate_and (w - 11) hwl hop]
          rw [ih _ (by have := hopnd_lt (w - 11) hwl 0; omega) (by have := hopnd_lt (w - 11) hwl 0; omega)]
          rw [ih _ (by have := hopnd_lt (w - 11) hwl 1; omega) (by have := hopnd_lt (w - 11) hwl 1; omega)]
          rfl
        · change gateVal 11 D (w - 11) (fun _ => true) = true
          rw [hgate_or (w - 11) hwl hop]
          rw [ih _ (by have := hopnd_lt (w - 11) hwl 0; omega) (by have := hopnd_lt (w - 11) hwl 0; omega)]
          rfl
  have hbelowF_has_top : ∀ k < D.gates.length, BelowF G0 D k → ∃ t ∈ tops G0 D, t = k ∨ InCone 11 D t k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hb
      rcases hAndOr _ (hgateAt_mem k hk) with hop | hop
      · exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, hb⟩, Or.inl rfl⟩
      · have htrue : gateVal 11 D k (fun _ => true) = true := hall_true (11 + k) (by omega)
        have hlt0 := hopnd_lt k hk 0
        by_cases h0 : opnd D k 0 < 11
        · exfalso
          have hv : (⟨opnd D k 0, h0⟩ : Fin 11) ∈ orIn 11 D (11 + k) := by
            rw [horIn_or_eq k hk hop]
            exact Finset.mem_union_left _ (horIn_self ⟨opnd D k 0, h0⟩)
          rw [horIn_belowF_empty k hk hb] at hv
          exact Finset.notMem_empty _ hv
        · have hjlt : opnd D k 0 - 11 < k := by omega
          have hjb : BelowF G0 D (opnd D k 0 - 11) := by
            intro x hx
            apply hb x
            rw [hgate_or k hk hop x]
            have : wireVal 11 D (opnd D k 0) x = true := by
              have heq : 11 + (opnd D k 0 - 11) = opnd D k 0 := by omega
              rw [← heq]; exact hx
            simp [this]
          obtain ⟨t, ht, htj⟩ := ih (opnd D k 0 - 11) hjlt (by omega) hjb
          exact ⟨t, ht, Or.inr (hinCone_step k hk 0 (opnd D k 0 - 11) t (by omega) htj)⟩
  have hand_no_belowF_cone : ∀ a < D.gates.length, (gateAt D a).op = GateOp.and →
      ∀ j < D.gates.length, InCone 11 D j a → ¬ BelowF G0 D j := by
    intro a ha hop j hj hja hjb
    obtain ⟨t, ht, htj⟩ := hbelowF_has_top j hj hjb
    have ht' := Finset.mem_filter.mp ht
    have htl : t < D.gates.length := Finset.mem_range.mp ht'.1
    have hta : InCone 11 D t a := by
      rcases htj with rfl | htinc
      · exact hja
      · exact hinCone_trans a j t htinc hja
    exact hT t htl a ha ht'.2.1 ht'.2.2 hop hta
  have hlam_no_belowF_cone : ∀ k ∈ lam G0 D, ∀ j < D.gates.length,
      (j = k ∨ InCone 11 D j k) → ¬ BelowF G0 D j := by
    intro k hk j hj hjk
    have hk' := Finset.mem_filter.mp hk
    have hk_orN := Finset.mem_filter.mp hk'.1
    have hkl : k < D.gates.length := Finset.mem_range.mp hk_orN.1
    obtain ⟨_, _, a, ha, b, _, hr⟩ := hk'.2
    have ha' := Finset.mem_filter.mp ha
    have hal : a < D.gates.length := Finset.mem_range.mp ha'.1
    have hba := horReaches_bounds _ k hr
    have hlt := hopnd_lt a hal b
    have hr' : OrReaches 11 D (11 + (opnd D a b - 11)) k := by
      have : 11 + (opnd D a b - 11) = opnd D a b := by omega
      rwa [this]
    have hka : InCone 11 D k a :=
      hinCone_step a hal b (opnd D a b - 11) k (by omega) (horReaches_inCone (opnd D a b - 11) (by omega) k hr')
    have hja : InCone 11 D j a := by
      rcases hjk with rfl | hjk'
      · exact hka
      · exact hinCone_trans a k j hjk' hka
    exact hand_no_belowF_cone a hal ha'.2.1 j hj hja
  have hreaders_nonempty : ∀ j < D.gates.length, ¬ BelowF G0 D j → (readers 11 D j).Nonempty := by
    intro j hj hnb
    have hne_out : 11 + j ≠ D.output := by
      intro heq
      apply hnb
      intro x hx
      have hfx : circuitFun 11 D x = graphFun G0 ∅ x := congrFun hfun x
      rw [← hfx]
      change (D.wires (List.ofFn x)).getD D.output false = true
      rw [← heq]
      exact hx
    have hout_lt : D.output < 11 + D.gates.length := by
      by_contra hge
      have hfx := congrFun hfun (pairInput (0 : Fin 11) (9 : Fin 11))
      have h0 : circuitFun 11 D (pairInput (0 : Fin 11) (9 : Fin 11)) = false := by
        change (D.gates.foldl stepW (List.ofFn (pairInput (0 : Fin 11) (9 : Fin 11)))).getD D.output false = false
        have hlen := hfoldW_len D.gates (List.ofFn (pairInput (0 : Fin 11) (9 : Fin 11)))
        simp only [List.length_ofFn] at hlen
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      have h1' : graphFun G0 ∅ (pairInput (0 : Fin 11) (9 : Fin 11)) = true := by
        unfold graphFun
        simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
          decide_eq_true_eq]
        exact ⟨0, 9, (hadjN_iff 0 9).1 rfl, hpi_left 0 9, hpi_right 0 9⟩
      rw [h0, h1'] at hfx
      exact Bool.false_ne_true hfx
    by_contra hemp
    have hremp : readers 11 D j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
    have hno_read : ∀ k < D.gates.length, 11 + j ∉ (gateAt D k).inputs := by
      intro k hk hmem
      have : k ∈ readers 11 D j := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hmem⟩
      rw [hremp] at this
      exact Finset.notMem_empty _ this
    let sh (w : ℕ) : ℕ := if w < 11 + j then w else w - 1
    let gs' : List Gate := (D.gates.take j ++ D.gates.drop (j + 1)).map fun g => ⟨g.op, g.inputs.map sh⟩
    let D' : Circuit := ⟨gs', sh D.output⟩
    have hgs'_len : D'.gates.length = D.gates.length - 1 := by
      simp [D', gs', Nat.min_eq_left hj.le]; omega
    have hgs'_lt : ∀ k < j, gateAt D' k = ⟨(gateAt D k).op, (gateAt D k).inputs.map sh⟩ := by
      intro k hk
      have hk1 : k < D'.gates.length := by omega
      have hk2 : k < (D.gates.take j).length := by simp [Nat.min_eq_left hj.le]; omega
      have hgaD : gateAt D k = D.gates[k]'(by omega) := by
        unfold gateAt; simp only [List.getD_eq_getElem?_getD, show k < D.gates.length by omega,
          List.getElem?_eq_getElem, Option.getD_some]
      rw [hgaD]
      unfold gateAt
      simp only [List.getD_eq_getElem?_getD, hk1, List.getElem?_eq_getElem, Option.getD_some]
      simp only [D', gs', List.getElem_map]
      rw [List.getElem_append_left hk2]
      simp
    have hgs'_ge : ∀ k, j ≤ k → k < D'.gates.length →
        gateAt D' k = ⟨(gateAt D (k + 1)).op, (gateAt D (k + 1)).inputs.map sh⟩ := by
      intro k hjk hk1
      have hkp : k + 1 < D.gates.length := by omega
      have htl : (D.gates.take j).length = j := by simp [Nat.min_eq_left hj.le]
      have hgaD : gateAt D (k + 1) = D.gates[k + 1] := by
        unfold gateAt; simp only [List.getD_eq_getElem?_getD, hkp, List.getElem?_eq_getElem, Option.getD_some]
      rw [hgaD]
      unfold gateAt
      simp only [List.getD_eq_getElem?_getD, hk1, List.getElem?_eq_getElem, Option.getD_some]
      simp only [D', gs', List.getElem_map]
      rw [List.getElem_append_right (by omega)]
      simp only [htl, List.getElem_drop]
      have hidx2 : j + 1 + (k - j) = k + 1 := by omega
      simp [hidx2]
    have hAO' : IsAO2 11 D' := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [D', gs', List.mem_map, List.mem_append] at hg
        obtain ⟨g0, hg0 | hg0, rfl⟩ := hg
        · exact hAndOr g0 (List.mem_of_mem_take hg0)
        · exact hAndOr g0 (List.mem_of_mem_drop hg0)
      · intro k hk w hw
        by_cases hkj : k < j
        · rw [hgs'_lt k hkj] at hw
          simp only [List.mem_map] at hw
          obtain ⟨w0, hw0, rfl⟩ := hw
          have hlt := hReads k (by omega) w0 hw0
          dsimp [sh]; split_ifs <;> omega
        · rw [hgs'_ge k (by omega) hk] at hw
          simp only [List.mem_map] at hw
          obtain ⟨w0, hw0, rfl⟩ := hw
          have hlt := hReads (k + 1) (by omega) w0 hw0
          have hne0 : w0 ≠ 11 + j := fun h => hno_read (k + 1) (by omega) (h ▸ hw0)
          dsimp [sh]; split_ifs <;> omega
      · intro g hg
        simp only [D', gs', List.mem_map, List.mem_append] at hg
        obtain ⟨g0, hg0 | hg0, rfl⟩ := hg
        · simpa using hLen2 g0 (List.mem_of_mem_take hg0)
        · simpa using hLen2 g0 (List.mem_of_mem_drop hg0)
    have heval' : ∀ (x : Fin 11 → Bool) (w : ℕ), w < 11 + D.gates.length → w ≠ 11 + j →
        wireVal 11 D' (sh w) x = wireVal 11 D w x := by
      intro x w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hwn
        by_cases h11 : w < 11
        · have hsh : sh w = w := by dsimp [sh]; split_ifs <;> omega
          rw [hsh]
          have hv := hwire_input D x ⟨w, h11⟩
          have hv' := hwire_input D' x ⟨w, h11⟩
          exact hv'.trans hv.symm
        · obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
          have hkl : k < D.gates.length := by omega
          by_cases hkj : k < j
          · have hsh : sh (11 + k) = 11 + k := by dsimp [sh]; split_ifs <;> omega
            rw [hsh]
            change gateVal 11 D' k x = gateVal 11 D k x
            rw [hgate_eval D' x k (by omega), hgate_eval D x k hkl, hgs'_lt k hkj]
            simp only [List.map_map]
            congr 1
            refine List.map_congr_left fun i hi => ?_
            have hilt := hReads k hkl i hi
            have hshi : sh i = i := by dsimp [sh]; split_ifs <;> omega
            simp only [Function.comp_apply, hshi, hilt, ↓reduceIte]
            simpa [hshi] using ih i (by omega) (by omega) (by omega)
          · have hkgt : j < k := by omega
            have hsh : sh (11 + k) = 11 + (k - 1) := by dsimp [sh]; split_ifs <;> omega
            rw [hsh]
            change gateVal 11 D' (k - 1) x = gateVal 11 D k x
            have hk1l : k - 1 < D'.gates.length := by omega
            rw [hgate_eval D' x (k - 1) hk1l, hgate_eval D x k hkl, hgs'_ge (k - 1) (by omega) hk1l]
            have hkm : k - 1 + 1 = k := by omega
            rw [hkm]
            simp only [List.map_map]
            congr 1
            refine List.map_congr_left fun i hi => ?_
            have hilt := hReads k hkl i hi
            have hine : i ≠ 11 + j := fun h => hno_read k hkl (h ▸ hi)
            have hshlt : sh i < 11 + (k - 1) := by dsimp [sh]; split_ifs <;> omega
            simp only [Function.comp_apply, hshlt, hilt, ↓reduceIte]
            exact ih i (by omega) (by omega) hine
    have hfun' : circuitFun 11 D' = graphFun G0 ∅ := by
      funext x
      rw [← congrFun hfun x]
      exact heval' x D.output hout_lt hne_out.symm
    have hle := hleast D' hAO' hfun'
    change D.gates.length ≤ D'.gates.length at hle
    omega
  have hwire_rep : ∀ (M : ℕ), M ≤ D.gates.length →
      (∀ k < M, k ∉ orN G0 D \ lam G0 D) →
      (∀ k < M, (gateAt D k).op = GateOp.or → ∀ h ∈ junk G0 D, ¬ OrReaches 11 D (11 + k) h) ∧
      (∀ w < 11 + M, (w < 11 ∨ (∃ k < M, w = 11 + k ∧ ¬ BelowF G0 D k)) →
        ∃ F : Finset (Finset (Fin 11)), (∀ S ∈ F, ValidWire (Ustar G0 D) S) ∧
          ∀ x : Fin 11 → Bool, wireVal 11 D w x = true ↔ ∀ S ∈ F, ∃ v ∈ S, x v = true) := by
    intro M hM hnoR
    have hno_or_j : ∀ k < M, (gateAt D k).op = GateOp.or → ∀ h ∈ junk G0 D, ¬ OrReaches 11 D (11 + k) h := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hkM hop h hh hr
        have hkl : k < D.gates.length := by omega
        have hh' := (Finset.mem_filter.mp hh).2
        have hknb : ¬ BelowF G0 D k := by
          intro hb
          obtain ⟨x, hgx, hfx⟩ := hh'.2.2
          have hkx := horReaches_val (11 + k) h hr x hgx
          have hfx' := hb x hkx
          rw [hfx] at hfx'; exact Bool.false_ne_true hfx'
        have hk_orN : k ∈ orN G0 D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl, hop, hknb⟩
        have hk_lam : k ∈ lam G0 D := by
          by_contra hnl
          exact hnoR k hkM (Finset.mem_sdiff.mpr ⟨hk_orN, hnl⟩)
        have hlam_p := (Finset.mem_filter.mp hk_lam).2
        rw [horReaches_iff k hkl h] at hr
        rcases hr with rfl | ⟨_, h0 | h1'⟩
        · have hopj := hh'.1; rw [hop] at hopj; cases hopj
        · have hb := horReaches_bounds _ h h0
          have hlt := hopnd_lt k hkl 0
          have h0_eq : 11 + (opnd D k 0 - 11) = opnd D k 0 := by omega
          rcases hAndOr _ (hgateAt_mem (opnd D k 0 - 11) (by omega)) with hop0 | hop0
          · have hemp := horIn_and (opnd D k 0 - 11) (by omega) hop0
            rw [h0_eq] at hemp
            exact Finset.not_nonempty_empty (hemp ▸ hlam_p.1)
          · exact ih (opnd D k 0 - 11) (by omega) (by omega) hop0 h hh (by rwa [h0_eq])
        · have hb := horReaches_bounds _ h h1'
          have hlt := hopnd_lt k hkl 1
          have h1_eq : 11 + (opnd D k 1 - 11) = opnd D k 1 := by omega
          rcases hAndOr _ (hgateAt_mem (opnd D k 1 - 11) (by omega)) with hop1 | hop1
          · have hemp := horIn_and (opnd D k 1 - 11) (by omega) hop1
            rw [h1_eq] at hemp
            exact Finset.not_nonempty_empty (hemp ▸ hlam_p.2.1)
          · exact ih (opnd D k 1 - 11) (by omega) (by omega) hop1 h hh (by rwa [h1_eq])
    refine ⟨hno_or_j, ?_⟩
    have hlam_eval : ∀ k < M, k ∈ lam G0 D → ∀ x : Fin 11 → Bool,
        gateVal 11 D k x = true ↔ ∃ v ∈ orIn 11 D (11 + k), x v = true := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hkM hklm x
        have hk_orN := (Finset.mem_filter.mp hklm).1
        have hk_p := Finset.mem_filter.mp hk_orN
        have hkl : k < D.gates.length := Finset.mem_range.mp hk_p.1
        have hop : (gateAt D k).op = GateOp.or := hk_p.2.1
        constructor
        · intro hgx
          rw [hgate_or k hkl hop x, Bool.or_eq_true] at hgx
          have hstep : ∀ b : Fin 2, wireVal 11 D (opnd D k b) x = true → ∃ v ∈ orIn 11 D (11 + k), x v = true := by
            intro b hwb
            have hlt := hopnd_lt k hkl b
            by_cases h11 : opnd D k b < 11
            · refine ⟨⟨opnd D k b, h11⟩, ?_, ?_⟩
              · rw [horIn_or_eq k hkl hop]
                fin_cases b
                · exact Finset.mem_union_left _ (horIn_self ⟨opnd D k 0, h11⟩)
                · exact Finset.mem_union_right _ (horIn_self ⟨opnd D k 1, h11⟩)
              · exact (hwire_input D x ⟨opnd D k b, h11⟩).symm.trans hwb
            · let k' := opnd D k b - 11
              have hk'eq : 11 + k' = opnd D k b := by omega
              have hk'lt : k' < k := by omega
              have hk'l : k' < D.gates.length := by omega
              have hk'nb : ¬ BelowF G0 D k' :=
                hlam_no_belowF_cone k hklm k' hk'l (Or.inr (hinCone_step k hkl b k' k' hk'eq.symm (Or.inl rfl)))
              rcases hAndOr _ (hgateAt_mem k' hk'l) with hop' | hop'
              · exfalso
                have hk'j : k' ∈ junk G0 D := by
                  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk'l, hop', hk'l, ?_⟩
                  by_contra hnot
                  apply hk'nb
                  intro z hz
                  cases hfz : graphFun G0 ∅ z
                  · exact absurd ⟨z, hz, hfz⟩ hnot
                  · rfl
                have hr' : OrReaches 11 D (11 + k) k' := by
                  rw [horReaches_iff k hkl k']
                  refine Or.inr ⟨hop, ?_⟩
                  have hself : OrReaches 11 D (11 + k') k' := (horReaches_iff k' hk'l k').2 (Or.inl rfl)
                  rw [hk'eq] at hself
                  fin_cases b
                  · exact Or.inl hself
                  · exact Or.inr hself
                exact hno_or_j k hkM hop k' hk'j hr'
              · have hk'orN : k' ∈ orN G0 D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk'l, hop', hk'nb⟩
                have hk'lam : k' ∈ lam G0 D := by
                  by_contra hnl
                  exact hnoR k' (by omega) (Finset.mem_sdiff.mpr ⟨hk'orN, hnl⟩)
                have hgk' : gateVal 11 D k' x = true := by rwa [← hk'eq] at hwb
                obtain ⟨v, hv, hxv⟩ := (ih k' hk'lt (by omega) hk'lam x).1 hgk'
                refine ⟨v, ?_, hxv⟩
                rw [horIn_or_eq k hkl hop]
                fin_cases b
                · exact Finset.mem_union_left _ (by rwa [hk'eq] at hv)
                · exact Finset.mem_union_right _ (by rwa [hk'eq] at hv)
          rcases hgx with h0 | h1'
          · exact hstep 0 h0
          · exact hstep 1 h1'
        · rintro ⟨v, hv, hxv⟩
          exact horIn_val (11 + k) v x hv hxv
    have hlam_valid : ∀ k ∈ lam G0 D, ValidWire (Ustar G0 D) (orIn 11 D (11 + k)) := by
      intro k hklm
      obtain ⟨_, _, a, ha, b, hcard1, hr⟩ := (Finset.mem_filter.mp hklm).2
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
      right
      refine ⟨c, fun v hv => ?_⟩
      have hvs : v ∈ side D a b := horIn_mono (opnd D a b) k hr hv
      have hcs : c ∈ side D a (1 - b) := by rw [hc]; exact Finset.mem_singleton_self c
      have hadj : G0.Adj c v := by
        have hst := (hstar0 a ha).2.1
        fin_cases b
        · exact (hst v hvs c hcs).symm
        · exact hst c hcs v hvs
      have hstar_e : s(c, v) ∈ starEdges G0 D := by
        refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ?_⟩
        fin_cases b
        · exact ⟨(v, c), Finset.mem_product.mpr ⟨hvs, hcs⟩, Sym2.eq_swap⟩
        · exact ⟨(c, v), Finset.mem_product.mpr ⟨hcs, hvs⟩, rfl⟩
      exact ⟨hadj, fun hu => (Finset.mem_sdiff.mp hu).2 hstar_e⟩
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hwM hcond
      rcases hcond with h11 | ⟨k, hkM, rfl, hknb⟩
      · refine ⟨{{⟨w, h11⟩}}, ?_, ?_⟩
        · intro S hS
          rw [Finset.mem_singleton.mp hS]
          exact Or.inl ⟨⟨w, h11⟩, rfl⟩
        · intro x
          simp only [Finset.mem_singleton, forall_eq, exists_eq_left]
          rw [hwire_input D x ⟨w, h11⟩]
      · have hkl : k < D.gates.length := by omega
        rcases hAndOr _ (hgateAt_mem k hkl) with hop | hop
        · have hsub_cond : ∀ b : Fin 2, opnd D k b < 11 ∨ ∃ k' < M, opnd D k b = 11 + k' ∧ ¬ BelowF G0 D k' := by
            intro b
            have hlt := hopnd_lt k hkl b
            by_cases h11 : opnd D k b < 11
            · exact Or.inl h11
            · right
              refine ⟨opnd D k b - 11, by omega, by omega, ?_⟩
              exact hand_no_belowF_cone k hkl hop (opnd D k b - 11) (by omega)
                (hinCone_step k hkl b (opnd D k b - 11) (opnd D k b - 11) (by omega) (Or.inl rfl))
          obtain ⟨F0, hF0v, hF0e⟩ := ih (opnd D k 0) (hopnd_lt k hkl 0) (by have := hopnd_lt k hkl 0; omega) (hsub_cond 0)
          obtain ⟨F1, hF1v, hF1e⟩ := ih (opnd D k 1) (hopnd_lt k hkl 1) (by have := hopnd_lt k hkl 1; omega) (hsub_cond 1)
          refine ⟨F0 ∪ F1, ?_, ?_⟩
          · intro S hS
            rcases Finset.mem_union.mp hS with h0 | h1'
            · exact hF0v S h0
            · exact hF1v S h1'
          · intro x
            change gateVal 11 D k x = true ↔ _
            rw [hgate_and k hkl hop x, Bool.and_eq_true, hF0e x, hF1e x]
            simp only [Finset.mem_union]
            constructor
            · rintro ⟨h0, h1'⟩ S (hS | hS)
              · exact h0 S hS
              · exact h1' S hS
            · intro h
              exact ⟨fun S hS => h S (Or.inl hS), fun S hS => h S (Or.inr hS)⟩
        · have hkorN : k ∈ orN G0 D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl, hop, hknb⟩
          have hklam : k ∈ lam G0 D := by
            by_contra hnl
            exact hnoR k hkM (Finset.mem_sdiff.mpr ⟨hkorN, hnl⟩)
          refine ⟨{orIn 11 D (11 + k)}, ?_, ?_⟩
          · intro S hS
            rw [Finset.mem_singleton.mp hS]
            exact hlam_valid k hklam
          · intro x
            simp only [Finset.mem_singleton, forall_eq]
            exact hlam_eval k hkM hklam x
  have hR_pos : 1 ≤ (orN G0 D \ lam G0 D).card := by
    by_contra hR0
    have hRemp : orN G0 D \ lam G0 D = ∅ := Finset.card_eq_zero.mp (by omega)
    have hnoR : ∀ k < D.gates.length, k ∉ orN G0 D \ lam G0 D := by
      intro k _; rw [hRemp]; exact Finset.notMem_empty k
    obtain ⟨hno_or_j, hrep⟩ := hwire_rep D.gates.length le_rfl hnoR
    have hU_by_C0 : ∀ u v : Fin 11, s(u, v) ∈ Ustar G0 D →
        ∃ a ∈ centreless G0 D, gateVal 11 D a (pairInput u v) = true := by
      intro u v huv
      obtain ⟨a, ha, b, h, hh, hga, hr, _⟩ := hoff u v huv
      have hb := horReaches_bounds (opnd D a b) h hr
      have hwb_eq : opnd D a b = 11 + h := by
        by_contra hne'
        have hlt : opnd D a b - 11 < D.gates.length := by omega
        have h11 : 11 + (opnd D a b - 11) = opnd D a b := by omega
        rcases hAndOr _ (hgateAt_mem (opnd D a b - 11) hlt) with hop | hop
        · have hr' : OrReaches 11 D (11 + (opnd D a b - 11)) h := by rwa [h11]
          rw [horReaches_iff (opnd D a b - 11) hlt h] at hr'
          rcases hr' with rfl | ⟨hor, _⟩
          · exact hne' h11.symm
          · rw [hop] at hor; cases hor
        · exact hno_or_j (opnd D a b - 11) hlt hop h hh (by rwa [h11])
      have hh' := Finset.mem_filter.mp hh
      have hhl : h < D.gates.length := Finset.mem_range.mp hh'.1
      have hside_emp : side (n := 11) D a b = ∅ := by
        unfold side
        rw [hwb_eq]
        exact horIn_and h hhl hh'.2.1
      have haC0 : a ∈ centreless G0 D := by
        refine Finset.mem_filter.mpr ⟨ha, ?_⟩
        fin_cases b
        · exact Or.inl hside_emp
        · exact Or.inr hside_emp
      exact ⟨a, haC0, hga⟩
    let Ea (a : ℕ) : Finset (Sym2 (Fin 11)) :=
      (Ustar G0 D).filter fun e => ∃ u v : Fin 11, e = s(u, v) ∧ gateVal 11 D a (pairInput u v) = true
    have hEa_obs : ∀ a ∈ centreless G0 D,
        (Ea a).card ≤ 1 ∨
          (Ea a = {s(0, 10), s(5, 8)} ∨ Ea a = {s(1, 4), s(5, 9)} ∨
           Ea a = {s(2, 10), s(8, 9)} ∨ Ea a = {s(4, 10), s(5, 9)}) := by
      intro a haC0
      have ha := (Finset.mem_filter.mp haC0).1
      have ha' := Finset.mem_filter.mp ha
      have hal : a < D.gates.length := Finset.mem_range.mp ha'.1
      have hop : (gateAt D a).op = GateOp.and := ha'.2.1
      have hab : BelowF G0 D a := ha'.2.2
      have hsub_cond : ∀ b : Fin 2, opnd D a b < 11 ∨ ∃ k' < D.gates.length, opnd D a b = 11 + k' ∧ ¬ BelowF G0 D k' := by
        intro b
        have hlt := hopnd_lt a hal b
        by_cases h11 : opnd D a b < 11
        · exact Or.inl h11
        · right
          refine ⟨opnd D a b - 11, by omega, by omega, ?_⟩
          exact hand_no_belowF_cone a hal hop (opnd D a b - 11) (by omega)
            (hinCone_step a hal b (opnd D a b - 11) (opnd D a b - 11) (by omega) (Or.inl rfl))
      obtain ⟨F0, hF0v, hF0e⟩ := hrep (opnd D a 0) (by have := hopnd_lt a hal 0; omega) (hsub_cond 0)
      obtain ⟨F1, hF1v, hF1e⟩ := hrep (opnd D a 1) (by have := hopnd_lt a hal 1; omega) (hsub_cond 1)
      have hFa_eval : ∀ x : Fin 11 → Bool, gateVal 11 D a x = true ↔ ∀ S ∈ F0 ∪ F1, ∃ v ∈ S, x v = true := by
        intro x
        rw [hgate_and a hal hop x, Bool.and_eq_true, hF0e x, hF1e x]
        simp only [Finset.mem_union]
        exact ⟨fun h01 S hS => hS.elim (h01.1 S) (h01.2 S),
               fun h => ⟨fun S hS => h S (Or.inl hS), fun S hS => h S (Or.inr hS)⟩⟩
      apply hValidObs (Ustar G0 D) (Ea a) (F0 ∪ F1) (Finset.filter_subset _ _)
      · intro e he
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1
      · intro S hS
        exact (Finset.mem_union.mp hS).elim (hF0v S) (hF1v S)
      · intro u v huv S hS
        obtain ⟨u', v', heq, hgv⟩ := (Finset.mem_filter.mp huv).2
        have hpi : pairInput u v = pairInput u' v' := by
          funext w
          have hmem : w ∈ s(u, v) ↔ w ∈ s(u', v') := by rw [heq]
          simp only [Sym2.mem_iff] at hmem
          unfold pairInput
          exact decide_eq_decide.mpr hmem
        rw [← hpi] at hgv
        obtain ⟨z, hzS, hzp⟩ := (hFa_eval (pairInput u v)).1 hgv S hS
        rw [hpi_iff] at hzp
        rcases hzp with rfl | rfl
        · exact Or.inl hzS
        · exact Or.inr hzS
      · intro p q hna
        by_contra hall
        have hga : gateVal 11 D a (pairInput p q) = true := by
          rw [hFa_eval]
          intro S hS
          by_cases hp : p ∈ S
          · exact ⟨p, hp, hpi_left p q⟩
          · by_cases hq : q ∈ S
            · exact ⟨q, hq, hpi_right p q⟩
            · exact absurd ⟨S, hS, hp, hq⟩ hall
        have hgf := hab (pairInput p q) hga
        rw [hpair_false p q hna] at hgf
        exact Bool.false_ne_true hgf
    let C1 := (centreless G0 D).filter fun a => (Ea a).card ≤ 1
    let C2 := (centreless G0 D).filter fun a => ¬ (Ea a).card ≤ 1
    have hC12 : C1.card + C2.card = (centreless G0 D).card :=
      Finset.card_filter_add_card_filter_not _
    let U1 := C1.biUnion Ea
    let U2 := C2.biUnion Ea
    have hU1_card : U1.card ≤ C1.card := by
      calc U1.card ≤ ∑ a ∈ C1, (Ea a).card := Finset.card_biUnion_le
        _ ≤ ∑ _a ∈ C1, 1 := Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2
        _ = C1.card := by simp
    have hU2_card : U2.card ≤ 2 * C2.card := by
      calc U2.card ≤ ∑ a ∈ C2, (Ea a).card := Finset.card_biUnion_le
        _ ≤ ∑ _a ∈ C2, 2 := by
            refine Finset.sum_le_sum fun a ha => ?_
            have ha' := Finset.mem_filter.mp ha
            rcases hEa_obs a ha'.1 with h1' | (h | h | h | h)
            · exact absurd h1' ha'.2
            · rw [h]; decide
            · rw [h]; decide
            · rw [h]; decide
            · rw [h]; decide
        _ = 2 * C2.card := by simp [mul_comm]
    have hU_sub : Ustar G0 D ⊆ U1 ∪ U2 := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨a, haC0, hga⟩ := hU_by_C0 u v he
        have heEa : s(u, v) ∈ Ea a := Finset.mem_filter.mpr ⟨he, u, v, rfl, hga⟩
        by_cases h1' : (Ea a).card ≤ 1
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨haC0, h1'⟩, heEa⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨haC0, h1'⟩, heEa⟩)
    have hU_card : (Ustar G0 D).card ≤ C1.card + 2 * C2.card := by
      calc (Ustar G0 D).card ≤ (U1 ∪ U2).card := Finset.card_le_card hU_sub
        _ ≤ U1.card + U2.card := Finset.card_union_le U1 U2
        _ ≤ C1.card + 2 * C2.card := by omega
    obtain ⟨K, hKmin⟩ := hexMinCover (Ustar G0 D)
    have hKT := hcov K hKmin
    by_cases hC2_zero : C2.card = 0
    · have hlift := hcover_lift (Ustar G0 D) K hKmin.1
      omega
    · let X1 : Finset (Fin 11) := U1.image fun e => e.out.1
      have hX1 : X1.card ≤ U1.card := Finset.card_image_le
      have hU2_avoids : ∀ e ∈ U2, e ≠ s(0, 9) ∧ e ≠ s(1, 8) ∧ e ≠ s(2, 5) ∧
          e ≠ s(3, 6) ∧ e ≠ s(3, 7) ∧ e ≠ s(6, 7) := by
        intro e he
        obtain ⟨a, ha2, heEa⟩ := Finset.mem_biUnion.mp he
        have ha' := Finset.mem_filter.mp ha2
        rcases hEa_obs a ha'.1 with h1' | (h | h | h | h)
        · exact absurd h1' ha'.2
        · rw [h] at heEa; simp only [Finset.mem_insert, Finset.mem_singleton] at heEa
          rcases heEa with rfl | rfl <;> decide
        · rw [h] at heEa; simp only [Finset.mem_insert, Finset.mem_singleton] at heEa
          rcases heEa with rfl | rfl <;> decide
        · rw [h] at heEa; simp only [Finset.mem_insert, Finset.mem_singleton] at heEa
          rcases heEa with rfl | rfl <;> decide
        · rw [h] at heEa; simp only [Finset.mem_insert, Finset.mem_singleton] at heEa
          rcases heEa with rfl | rfl <;> decide
      have hKX1_cov : ∀ u v : Fin 11, G0.Adj u v → s(u, v) ∉ U2 → u ∈ K ∪ X1 ∨ v ∈ K ∪ X1 := by
        intro u v huv hnot2
        by_cases hU : s(u, v) ∈ Ustar G0 D
        · have hU1 : s(u, v) ∈ U1 := by
            rcases Finset.mem_union.mp (hU_sub hU) with h | h
            · exact h
            · exact absurd h hnot2
          have hvx : s(u, v).out.1 ∈ X1 := Finset.mem_image_of_mem _ hU1
          have hh := Sym2.out_fst_mem s(u, v)
          rw [Sym2.mem_iff] at hh
          rcases hh with h | h
          · exact Or.inl (Finset.mem_union_right _ (h ▸ hvx))
          · exact Or.inr (Finset.mem_union_right _ (h ▸ hvx))
        · rcases hKmin.1 (SimpleGraph.deleteEdges_adj.mpr ⟨huv, hU⟩) with hu | hv
          · exact Or.inl (Finset.mem_union_left X1 hu)
          · exact Or.inr (Finset.mem_union_left X1 hv)
      have h5 : 5 ≤ (K ∪ X1).card := by
        apply hcover_S7_ge5 (K ∪ X1)
        · exact hKX1_cov 0 9 ((hadjN_iff 0 9).1 rfl) fun h => (hU2_avoids _ h).1 rfl
        · exact hKX1_cov 1 8 ((hadjN_iff 1 8).1 rfl) fun h => (hU2_avoids _ h).2.1 rfl
        · exact hKX1_cov 2 5 ((hadjN_iff 2 5).1 rfl) fun h => (hU2_avoids _ h).2.2.1 rfl
        · exact hKX1_cov 3 6 ((hadjN_iff 3 6).1 rfl) fun h => (hU2_avoids _ h).2.2.2.1 rfl
        · exact hKX1_cov 3 7 ((hadjN_iff 3 7).1 rfl) fun h => (hU2_avoids _ h).2.2.2.2.1 rfl
        · exact hKX1_cov 6 7 ((hadjN_iff 6 7).1 rfl) fun h => (hU2_avoids _ h).2.2.2.2.2 rfl
      have hu := Finset.card_union_le K X1
      omega
  have hC0_or_R2 : (centreless G0 D).Nonempty ∨ 2 ≤ (orN G0 D \ lam G0 D).card := by
    by_contra hnot
    have hC0emp : centreless G0 D = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun h => hnot (Or.inl h)
    have hR1 : (orN G0 D \ lam G0 D).card = 1 := by
      have : ¬ 2 ≤ (orN G0 D \ lam G0 D).card := fun h => hnot (Or.inr h)
      omega
    obtain ⟨m, hmset⟩ := Finset.card_eq_one.mp hR1
    have hm_in : m ∈ orN G0 D \ lam G0 D := by rw [hmset]; exact Finset.mem_singleton_self m
    have hm_orN := (Finset.mem_sdiff.mp hm_in).1
    have hm_p := Finset.mem_filter.mp hm_orN
    have hml : m < D.gates.length := Finset.mem_range.mp hm_p.1
    have hm_op : (gateAt D m).op = GateOp.or := hm_p.2.1
    have hm_nb : ¬ BelowF G0 D m := hm_p.2.2
    have hJne : (junk G0 D).Nonempty := Finset.card_pos.mp (by omega)
    let gmax := (junk G0 D).max' hJne
    have hgmax_in : gmax ∈ junk G0 D := Finset.max'_mem (junk G0 D) hJne
    have hgmax_max : ∀ g ∈ junk G0 D, g ≤ gmax := fun g hg => Finset.le_max' (junk G0 D) g hg
    have hgmax_p := (Finset.mem_filter.mp hgmax_in).2
    have hgmax_l : gmax < D.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hgmax_in).1
    have hgmax_nb : ¬ BelowF G0 D gmax := by
      intro hb
      obtain ⟨x, hgx, hfx⟩ := hgmax_p.2.2
      have := hb x hgx
      rw [hfx] at this; exact Bool.false_ne_true this
    obtain ⟨rm, hrm⟩ := hreaders_nonempty gmax hgmax_l hgmax_nb
    have hrm_p := Finset.mem_filter.mp hrm
    have hrm_l : rm < D.gates.length := Finset.mem_range.mp hrm_p.1
    have hrm_in : 11 + gmax ∈ (gateAt D rm).inputs := hrm_p.2
    have hrm_gt : gmax < rm := by
      have := hReads rm hrm_l (11 + gmax) hrm_in
      omega
    have hrm_eq_m : rm = m := by
      have hrm_nb : ¬ BelowF G0 D rm := by
        intro hb
        rcases hAndOr _ (hgateAt_mem rm hrm_l) with hop | hop
        · have hrm_top : rm ∈ tops G0 D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrm_l, hop, hb⟩
          rw [hinputs_eq rm hrm_l] at hrm_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hrm_in
          have hside0 : side (n := 11) D rm 0 = ∅ ∨ side (n := 11) D rm 1 = ∅ := by
            rcases hrm_in with h | h
            · exact Or.inl (by unfold side; rw [← h]; exact horIn_and gmax hgmax_l hgmax_p.1)
            · exact Or.inr (by unfold side; rw [← h]; exact horIn_and gmax hgmax_l hgmax_p.1)
          have : rm ∈ centreless G0 D := Finset.mem_filter.mpr ⟨hrm_top, hside0⟩
          rw [hC0emp] at this; exact Finset.notMem_empty _ this
        · obtain ⟨x, hgx, hfx⟩ := hgmax_p.2.2
          have hrmx : gateVal 11 D rm x = true := by
            rw [hgate_or rm hrm_l hop x]
            rw [hinputs_eq rm hrm_l] at hrm_in
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hrm_in
            rcases hrm_in with h | h
            · rw [← h]; change (gateVal 11 D gmax x || _) = true; rw [hgx]; rfl
            · rw [← h]; change (_ || gateVal 11 D gmax x) = true; rw [hgx]; exact Bool.or_true _
          have := hb x hrmx
          rw [hfx] at this; exact Bool.false_ne_true this
      rcases hAndOr _ (hgateAt_mem rm hrm_l) with hop | hop
      · exfalso
        have hrm_j : rm ∈ junk G0 D := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrm_l, hop, hrm_l, ?_⟩
          by_contra hall
          apply hrm_nb; intro x hx
          cases hf : graphFun G0 ∅ x
          · exact absurd ⟨x, hx, hf⟩ hall
          · rfl
        have := hgmax_max rm hrm_j
        omega
      · have hrm_orN : rm ∈ orN G0 D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrm_l, hop, hrm_nb⟩
        have hrm_nlam : rm ∉ lam G0 D := by
          intro hlm
          have hlp := (Finset.mem_filter.mp hlm).2
          rw [hinputs_eq rm hrm_l] at hrm_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hrm_in
          rcases hrm_in with h | h
          · have hemp := horIn_and gmax hgmax_l hgmax_p.1
            rw [h] at hemp
            exact Finset.not_nonempty_empty (hemp ▸ hlp.1)
          · have hemp := horIn_and gmax hgmax_l hgmax_p.1
            rw [h] at hemp
            exact Finset.not_nonempty_empty (hemp ▸ hlp.2.1)
        have hrm_R : rm ∈ orN G0 D \ lam G0 D := Finset.mem_sdiff.mpr ⟨hrm_orN, hrm_nlam⟩
        rw [hmset] at hrm_R
        exact Finset.mem_singleton.mp hrm_R
    subst hrm_eq_m
    have hm_in_g : ∃ bm : Fin 2, opnd D rm bm = 11 + gmax := by
      rw [hinputs_eq rm hrm_l] at hrm_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrm_in
      rcases hrm_in with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
    obtain ⟨bm, hbm⟩ := hm_in_g
    have hm_orIn_ne : (orIn 11 D (opnd D rm (1 - bm))).Nonempty := by
      by_contra hemp
      have h0 : orIn 11 D (opnd D rm (1 - bm)) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
      have h1' : orIn 11 D (opnd D rm bm) = ∅ := by rw [hbm]; exact horIn_and gmax hgmax_l hgmax_p.1
      have hm_emp : orIn 11 D (11 + rm) = ∅ := by
        rw [horIn_or_eq rm hrm_l hm_op, Finset.union_eq_empty]
        fin_cases bm
        · exact ⟨h1', h0⟩
        · exact ⟨h0, h1'⟩
      obtain ⟨r2, hr2⟩ := hreaders_nonempty rm hrm_l hm_nb
      have hr2_p := Finset.mem_filter.mp hr2
      have hr2_l : r2 < D.gates.length := Finset.mem_range.mp hr2_p.1
      have hr2_in : 11 + rm ∈ (gateAt D r2).inputs := hr2_p.2
      have hr2_gt : rm < r2 := by have := hReads r2 hr2_l (11 + rm) hr2_in; omega
      have hr2_nb : ¬ BelowF G0 D r2 := by
        intro hb
        rcases hAndOr _ (hgateAt_mem r2 hr2_l) with hop | hop
        · have hr2_top : r2 ∈ tops G0 D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr2_l, hop, hb⟩
          rw [hinputs_eq r2 hr2_l] at hr2_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2_in
          have hside0 : side (n := 11) D r2 0 = ∅ ∨ side (n := 11) D r2 1 = ∅ := by
            rcases hr2_in with h | h
            · exact Or.inl (by unfold side; rw [← h]; exact hm_emp)
            · exact Or.inr (by unfold side; rw [← h]; exact hm_emp)
          have : r2 ∈ centreless G0 D := Finset.mem_filter.mpr ⟨hr2_top, hside0⟩
          rw [hC0emp] at this; exact Finset.notMem_empty _ this
        · apply hm_nb
          intro x hx
          apply hb x
          rw [hgate_or r2 hr2_l hop x]
          rw [hinputs_eq r2 hr2_l] at hr2_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2_in
          rcases hr2_in with h | h
          · rw [← h]; change (gateVal 11 D rm x || _) = true; rw [hx]; rfl
          · rw [← h]; change (_ || gateVal 11 D rm x) = true; rw [hx]; exact Bool.or_true _
      rcases hAndOr _ (hgateAt_mem r2 hr2_l) with hop | hop
      · have hr2_j : r2 ∈ junk G0 D := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr2_l, hop, hr2_l, ?_⟩
          by_contra hall
          apply hr2_nb; intro x hx
          cases hf : graphFun G0 ∅ x
          · exact absurd ⟨x, hx, hf⟩ hall
          · rfl
        have := hgmax_max r2 hr2_j
        omega
      · have hr2_orN : r2 ∈ orN G0 D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr2_l, hop, hr2_nb⟩
        have hr2_nlam : r2 ∉ lam G0 D := by
          intro hlm
          have hlp := (Finset.mem_filter.mp hlm).2
          rw [hinputs_eq r2 hr2_l] at hr2_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2_in
          rcases hr2_in with h | h
          · rw [h] at hm_emp; exact Finset.not_nonempty_empty (hm_emp ▸ hlp.1)
          · rw [h] at hm_emp; exact Finset.not_nonempty_empty (hm_emp ▸ hlp.2.1)
        have hr2_R : r2 ∈ orN G0 D \ lam G0 D := Finset.mem_sdiff.mpr ⟨hr2_orN, hr2_nlam⟩
        rw [hmset] at hr2_R
        have := Finset.mem_singleton.mp hr2_R
        omega
    obtain ⟨x0, hx0⟩ := hm_orIn_ne
    have hx0_m : x0 ∈ orIn 11 D (11 + rm) := by
      rw [horIn_or_eq rm hrm_l hm_op]
      fin_cases bm
      · exact Finset.mem_union_right _ hx0
      · exact Finset.mem_union_left _ hx0
    have hnoR_lt : ∀ k < rm, k ∉ orN G0 D \ lam G0 D := by
      intro k hk hmem
      rw [hmset] at hmem
      have := Finset.mem_singleton.mp hmem
      omega
    obtain ⟨hno_or_j_lt, hrep_lt⟩ := hwire_rep rm hrm_l.le hnoR_lt
    have hor_reach_m : ∀ k < D.gates.length, (gateAt D k).op = GateOp.or →
        ∀ h ∈ junk G0 D, OrReaches 11 D (11 + k) h → h = gmax ∧ OrReaches 11 D (11 + k) rm := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hkl hop h hh hr
        by_cases hkm : k = rm
        · subst hkm
          rw [horReaches_iff k hkl h] at hr
          rcases hr with rfl | ⟨_, h0 | h1'⟩
          · have hopj := (Finset.mem_filter.mp hh).2.1; rw [hm_op] at hopj; cases hopj
          · have hcase : ∀ b : Fin 2, OrReaches 11 D (opnd D k b) h → h = gmax := by
              intro b hrb
              by_cases hbb : b = bm
              · subst hbb
                rw [hbm] at hrb
                rw [horReaches_iff gmax hgmax_l h] at hrb
                rcases hrb with rfl | ⟨hor, _⟩
                · rfl
                · rw [hgmax_p.1] at hor; cases hor
              · exfalso
                have hb1 : b = 1 - bm := by
                  fin_cases b <;> fin_cases bm <;> first | rfl | exact absurd rfl hbb
                rw [hb1] at hrb
                have hlt := hopnd_lt k hkl (1 - bm)
                have hbd := horReaches_bounds _ h hrb
                have hkeq : 11 + (opnd D k (1 - bm) - 11) = opnd D k (1 - bm) := by omega
                rcases hAndOr _ (hgateAt_mem (opnd D k (1 - bm) - 11) (by omega)) with hop' | hop'
                · have hemp := horIn_and (opnd D k (1 - bm) - 11) (by omega) hop'
                  rw [hkeq] at hemp
                  rw [hemp] at hx0
                  exact Finset.notMem_empty _ hx0
                · exact hno_or_j_lt (opnd D k (1 - bm) - 11) (by omega) hop' h hh (by rwa [hkeq])
            exact ⟨hcase 0 h0, (horReaches_iff k hkl k).2 (Or.inl rfl)⟩
          · have hcase : ∀ b : Fin 2, OrReaches 11 D (opnd D k b) h → h = gmax := by
              intro b hrb
              by_cases hbb : b = bm
              · subst hbb
                rw [hbm] at hrb
                rw [horReaches_iff gmax hgmax_l h] at hrb
                rcases hrb with rfl | ⟨hor, _⟩
                · rfl
                · rw [hgmax_p.1] at hor; cases hor
              · exfalso
                have hb1 : b = 1 - bm := by
                  fin_cases b <;> fin_cases bm <;> first | rfl | exact absurd rfl hbb
                rw [hb1] at hrb
                have hlt := hopnd_lt k hkl (1 - bm)
                have hbd := horReaches_bounds _ h hrb
                have hkeq : 11 + (opnd D k (1 - bm) - 11) = opnd D k (1 - bm) := by omega
                rcases hAndOr _ (hgateAt_mem (opnd D k (1 - bm) - 11) (by omega)) with hop' | hop'
                · have hemp := horIn_and (opnd D k (1 - bm) - 11) (by omega) hop'
                  rw [hkeq] at hemp
                  rw [hemp] at hx0
                  exact Finset.notMem_empty _ hx0
                · exact hno_or_j_lt (opnd D k (1 - bm) - 11) (by omega) hop' h hh (by rwa [hkeq])
            exact ⟨hcase 1 h1', (horReaches_iff k hkl k).2 (Or.inl rfl)⟩
        · have hh' := (Finset.mem_filter.mp hh).2
          have hknb : ¬ BelowF G0 D k := by
            intro hb
            obtain ⟨x, hgx, hfx⟩ := hh'.2.2
            have hkx := horReaches_val (11 + k) h hr x hgx
            have hfx' := hb x hkx
            rw [hfx] at hfx'; exact Bool.false_ne_true hfx'
          have hkorN : k ∈ orN G0 D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl, hop, hknb⟩
          have hklam : k ∈ lam G0 D := by
            by_contra hnl
            have hmem : k ∈ orN G0 D \ lam G0 D := Finset.mem_sdiff.mpr ⟨hkorN, hnl⟩
            rw [hmset] at hmem
            exact hkm (Finset.mem_singleton.mp hmem)
          have hlp := (Finset.mem_filter.mp hklam).2
          rw [horReaches_iff k hkl h] at hr
          rcases hr with rfl | ⟨_, h0 | h1'⟩
          · have hopj := hh'.1; rw [hop] at hopj; cases hopj
          · have hbd := horReaches_bounds _ h h0
            have hlt := hopnd_lt k hkl 0
            have hkeq : 11 + (opnd D k 0 - 11) = opnd D k 0 := by omega
            rcases hAndOr _ (hgateAt_mem (opnd D k 0 - 11) (by omega)) with hop' | hop'
            · have hemp := horIn_and (opnd D k 0 - 11) (by omega) hop'
              rw [hkeq] at hemp
              exact absurd (hemp ▸ hlp.1) Finset.not_nonempty_empty
            · obtain ⟨hhg, hrm'⟩ := ih (opnd D k 0 - 11) (by omega) (by omega) hop' h hh (by rwa [hkeq])
              exact ⟨hhg, (horReaches_iff k hkl rm).2 (Or.inr ⟨hop, Or.inl (by rwa [← hkeq])⟩)⟩
          · have hbd := horReaches_bounds _ h h1'
            have hlt := hopnd_lt k hkl 1
            have hkeq : 11 + (opnd D k 1 - 11) = opnd D k 1 := by omega
            rcases hAndOr _ (hgateAt_mem (opnd D k 1 - 11) (by omega)) with hop' | hop'
            · have hemp := horIn_and (opnd D k 1 - 11) (by omega) hop'
              rw [hkeq] at hemp
              exact absurd (hemp ▸ hlp.2.1) Finset.not_nonempty_empty
            · obtain ⟨hhg, hrm'⟩ := ih (opnd D k 1 - 11) (by omega) (by omega) hop' h hh (by rwa [hkeq])
              exact ⟨hhg, (horReaches_iff k hkl rm).2 (Or.inr ⟨hop, Or.inr (by rwa [← hkeq])⟩)⟩
    have hor_no_junk_eval : ∀ w < 11 + D.gates.length,
        (∀ h ∈ junk G0 D, ¬ OrReaches 11 D w h) →
        (∀ k < D.gates.length, OrReaches 11 D w k → ¬ BelowF G0 D k) →
        ∀ x : Fin 11 → Bool, wireVal 11 D w x = true → ∃ v ∈ orIn 11 D w, x v = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hnoj hnob x hwx
        by_cases h11 : w < 11
        · refine ⟨⟨w, h11⟩, horIn_self ⟨w, h11⟩, ?_⟩
          exact (hwire_input D x ⟨w, h11⟩).symm.trans hwx
        · let k := w - 11
          have hkeq : 11 + k = w := by omega
          have hkl : k < D.gates.length := by omega
          rw [← hkeq] at hnoj hnob hwx ⊢
          have hself : OrReaches 11 D (11 + k) k := (horReaches_iff k hkl k).2 (Or.inl rfl)
          have hknb : ¬ BelowF G0 D k := hnob k hkl hself
          rcases hAndOr _ (hgateAt_mem k hkl) with hop | hop
          · exfalso
            have hkj : k ∈ junk G0 D := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl, hop, hkl, ?_⟩
              by_contra hall
              apply hknb; intro z hz
              cases hf : graphFun G0 ∅ z
              · exact absurd ⟨z, hz, hf⟩ hall
              · rfl
            exact hnoj k hkj hself
          · change gateVal 11 D k x = true at hwx
            rw [hgate_or k hkl hop x, Bool.or_eq_true] at hwx
            rcases hwx with h0 | h1'
            · have hlt := hopnd_lt k hkl 0
              have hnoj0 : ∀ h ∈ junk G0 D, ¬ OrReaches 11 D (opnd D k 0) h :=
                fun h hh hr => hnoj h hh ((horReaches_iff k hkl h).2 (Or.inr ⟨hop, Or.inl hr⟩))
              have hnob0 : ∀ j < D.gates.length, OrReaches 11 D (opnd D k 0) j → ¬ BelowF G0 D j :=
                fun j hj hr => hnob j hj ((horReaches_iff k hkl j).2 (Or.inr ⟨hop, Or.inl hr⟩))
              obtain ⟨v, hv, hxv⟩ := ih (opnd D k 0) (by omega) (by omega) hnoj0 hnob0 x h0
              exact ⟨v, by rw [horIn_or_eq k hkl hop]; exact Finset.mem_union_left _ hv, hxv⟩
            · have hlt := hopnd_lt k hkl 1
              have hnoj1 : ∀ h ∈ junk G0 D, ¬ OrReaches 11 D (opnd D k 1) h :=
                fun h hh hr => hnoj h hh ((horReaches_iff k hkl h).2 (Or.inr ⟨hop, Or.inr hr⟩))
              have hnob1 : ∀ j < D.gates.length, OrReaches 11 D (opnd D k 1) j → ¬ BelowF G0 D j :=
                fun j hj hr => hnob j hj ((horReaches_iff k hkl j).2 (Or.inr ⟨hop, Or.inr hr⟩))
              obtain ⟨v, hv, hxv⟩ := ih (opnd D k 1) (by omega) (by omega) hnoj1 hnob1 x h1'
              exact ⟨v, by rw [horIn_or_eq k hkl hop]; exact Finset.mem_union_right _ hv, hxv⟩
    let Sx : Finset (Fin 11) := (Finset.univ.filter (G0.Adj x0)) ∩ wmax G0 D gmax
    have hU_props : ∀ u v : Fin 11, s(u, v) ∈ Ustar G0 D →
        gateVal 11 D gmax (pairInput u v) = true ∧ u ≠ x0 ∧ v ≠ x0 ∧ (u ∈ Sx ∨ v ∈ Sx) := by
      intro u v huv
      obtain ⟨a, ha, b, h, hh, hga, hr, hgh⟩ := hoff u v huv
      have ha' := Finset.mem_filter.mp ha
      have hal : a < D.gates.length := Finset.mem_range.mp ha'.1
      have ha_nc0 : a ∉ centreless G0 D := by rw [hC0emp]; exact Finset.notMem_empty a
      have hsb_ne : (side (n := 11) D a b).Nonempty := by
        by_contra hemp
        have h0 := Finset.not_nonempty_iff_eq_empty.mp hemp
        apply ha_nc0
        refine Finset.mem_filter.mpr ⟨ha, ?_⟩
        fin_cases b
        · exact Or.inl h0
        · exact Or.inr h0
      have hbd := horReaches_bounds (opnd D a b) h hr
      let k := opnd D a b - 11
      have hkeq : 11 + k = opnd D a b := by omega
      have hkl : k < D.gates.length := by omega
      have hkop : (gateAt D k).op = GateOp.or := by
        rcases hAndOr _ (hgateAt_mem k hkl) with hop | hop
        · exfalso
          have hemp := horIn_and k hkl hop
          rw [hkeq] at hemp
          unfold side at hsb_ne
          exact Finset.not_nonempty_empty (hemp ▸ hsb_ne)
        · exact hop
      obtain ⟨hhg, hrm'⟩ := hor_reach_m k hkl hkop h hh (by rwa [hkeq])
      subst hhg
      have hx0_sb : x0 ∈ side (n := 11) D a b := by
        unfold side
        rw [← hkeq]
        exact horIn_mono (11 + k) rm hrm' hx0_m
      have hdisj : Disjoint (side (n := 11) D a b) (side (n := 11) D a (1 - b)) := by
        have hd := (hstar0 a ha).1
        fin_cases b
        · exact hd
        · exact hd.symm
      have hx0_not_other : x0 ∉ side (n := 11) D a (1 - b) :=
        Finset.disjoint_left.mp hdisj hx0_sb
      have hother_noj : ∀ h' ∈ junk G0 D, ¬ OrReaches 11 D (opnd D a (1 - b)) h' := by
        intro h' hh' hr'
        have hso_ne : (side (n := 11) D a (1 - b)).Nonempty := by
          by_contra hemp
          have h0 := Finset.not_nonempty_iff_eq_empty.mp hemp
          apply ha_nc0
          refine Finset.mem_filter.mpr ⟨ha, ?_⟩
          fin_cases b
          · exact Or.inr h0
          · exact Or.inl h0
        have hbd' := horReaches_bounds _ h' hr'
        let k' := opnd D a (1 - b) - 11
        have hk'eq : 11 + k' = opnd D a (1 - b) := by omega
        have hk'l : k' < D.gates.length := by omega
        have hk'op : (gateAt D k').op = GateOp.or := by
          rcases hAndOr _ (hgateAt_mem k' hk'l) with hop | hop
          · exfalso
            have hemp := horIn_and k' hk'l hop
            rw [hk'eq] at hemp
            unfold side at hso_ne
            exact Finset.not_nonempty_empty (hemp ▸ hso_ne)
          · exact hop
        obtain ⟨_, hrm''⟩ := hor_reach_m k' hk'l hk'op h' hh' (by rwa [hk'eq])
        have : x0 ∈ side (n := 11) D a (1 - b) := by
          unfold side; rw [← hk'eq]
          exact horIn_mono (11 + k') rm hrm'' hx0_m
        exact hx0_not_other this
      have hother_nob : ∀ j < D.gates.length, OrReaches 11 D (opnd D a (1 - b)) j → ¬ BelowF G0 D j := by
        intro j hj hrj
        have hbd' := horReaches_bounds _ j hrj
        have hkeq' : 11 + (opnd D a (1 - b) - 11) = opnd D a (1 - b) := by omega
        have hlt' := hopnd_lt a hal (1 - b)
        have hja : InCone 11 D j a :=
          hinCone_step a hal (1 - b) (opnd D a (1 - b) - 11) j hkeq'.symm
            (horReaches_inCone (opnd D a (1 - b) - 11) (by omega) j (by rwa [hkeq']))
        exact hand_no_belowF_cone a hal ha'.2.1 j hj hja
      have hother_true : wireVal 11 D (opnd D a (1 - b)) (pairInput u v) = true := by
        rw [hgate_and a hal ha'.2.1, Bool.and_eq_true] at hga
        fin_cases b
        · exact hga.2
        · exact hga.1
      obtain ⟨w, hw_so, hwp⟩ := hor_no_junk_eval (opnd D a (1 - b))
        (by have := hopnd_lt a hal (1 - b); omega) hother_noj hother_nob (pairInput u v) hother_true
      have hw_adj : G0.Adj x0 w := by
        have hst := (hstar0 a ha).2.1
        fin_cases b
        · exact hst x0 hx0_sb w hw_so
        · exact (hst w hw_so x0 hx0_sb).symm
      have hw_wmax : w ∈ wmax G0 D gmax := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ w, fun z hgz hzw => ?_⟩
        apply ha'.2.2 z
        rw [hgate_and a hal ha'.2.1 z, Bool.and_eq_true]
        have h1' : wireVal 11 D (opnd D a b) z = true := horReaches_val (opnd D a b) gmax hr z hgz
        have h2' : wireVal 11 D (opnd D a (1 - b)) z = true := horIn_val (opnd D a (1 - b)) w z hw_so hzw
        fin_cases b
        · exact ⟨h1', h2'⟩
        · exact ⟨h2', h1'⟩
      have hw_Sx : w ∈ Sx := Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw_adj⟩, hw_wmax⟩
      have hsxw_star : s(x0, w) ∈ starEdges G0 D := by
        refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ?_⟩
        fin_cases b
        · exact ⟨(x0, w), Finset.mem_product.mpr ⟨hx0_sb, hw_so⟩, rfl⟩
        · exact ⟨(w, x0), Finset.mem_product.mpr ⟨hw_so, hx0_sb⟩, Sym2.eq_swap⟩
      rw [hpi_iff] at hwp
      rcases hwp with hwu | hwv
      · subst hwu
        have hux : w ≠ x0 := fun h => hx0_not_other (h ▸ hw_so)
        have hvx : v ≠ x0 := fun h => (Finset.mem_sdiff.mp huv).2 (by rw [h, Sym2.eq_swap]; exact hsxw_star)
        exact ⟨hgh, hux, hvx, Or.inl hw_Sx⟩
      · subst hwv
        have hvx : w ≠ x0 := fun h => hx0_not_other (h ▸ hw_so)
        have hux : u ≠ x0 := fun h => (Finset.mem_sdiff.mp huv).2 (by rw [h]; exact hsxw_star)
        exact ⟨hgh, hux, hvx, Or.inr hw_Sx⟩
    obtain ⟨Fg, hFgv, hFge⟩ := hrep_lt (11 + gmax) (by omega) (Or.inr ⟨gmax, hrm_gt, rfl, hgmax_nb⟩)
    have hSx_valid : ValidWire (Ustar G0 D) Sx := by
      right
      refine ⟨x0, fun w hw => ?_⟩
      have hadj := (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2
      exact ⟨hadj, fun hU => (hU_props x0 w hU).2.1 rfl⟩
    have hU_obs : (Ustar G0 D).card ≤ 1 ∨
        (Ustar G0 D = {s(0, 10), s(5, 8)} ∨ Ustar G0 D = {s(1, 4), s(5, 9)} ∨
         Ustar G0 D = {s(2, 10), s(8, 9)} ∨ Ustar G0 D = {s(4, 10), s(5, 9)}) := by
      apply hValidObs (Ustar G0 D) (Ustar G0 D) (insert Sx Fg) (Finset.Subset.refl _)
      · intro e he; exact (Finset.mem_sdiff.mp he).1
      · intro S hS
        rcases Finset.mem_insert.mp hS with rfl | hSg
        · exact hSx_valid
        · exact hFgv S hSg
      · intro u v huv S hS
        have hp := hU_props u v huv
        rcases Finset.mem_insert.mp hS with rfl | hSg
        · exact hp.2.2.2
        · obtain ⟨z, hzS, hzp⟩ := (hFge (pairInput u v)).1 hp.1 S hSg
          rw [hpi_iff] at hzp
          rcases hzp with rfl | rfl
          · exact Or.inl hzS
          · exact Or.inr hzS
      · intro p q hna
        by_contra hall
        have hgpq : gateVal 11 D gmax (pairInput p q) = true := by
          change wireVal 11 D (11 + gmax) (pairInput p q) = true
          rw [hFge]
          intro S hS
          by_cases hp : p ∈ S
          · exact ⟨p, hp, hpi_left p q⟩
          · by_cases hq : q ∈ S
            · exact ⟨q, hq, hpi_right p q⟩
            · exact absurd ⟨S, Finset.mem_insert_of_mem hS, hp, hq⟩ hall
        by_cases hp : p ∈ Sx
        · have hw := (Finset.mem_filter.mp (Finset.mem_inter.mp hp).2).2 (pairInput p q) hgpq (hpi_left p q)
          rw [hpair_false p q hna] at hw; exact Bool.false_ne_true hw
        · by_cases hq : q ∈ Sx
          · have hw := (Finset.mem_filter.mp (Finset.mem_inter.mp hq).2).2 (pairInput p q) hgpq (hpi_right p q)
            rw [hpair_false p q hna] at hw; exact Bool.false_ne_true hw
          · exact absurd ⟨Sx, Finset.mem_insert_self Sx Fg, hp, hq⟩ hall
    obtain ⟨K, hKmin⟩ := hexMinCover (Ustar G0 D)
    have hKT := hcov K hKmin
    have hC0card : (centreless G0 D).card = 0 := by rw [hC0emp]; rfl
    rcases hU_obs with hUle1 | hUbad
    · have hlift := hcover_lift (Ustar G0 D) K hKmin.1
      omega
    · have h6 := hcover_badpair_ge6 K (Ustar G0 D) hUbad hKmin.1
      have hU2 : (Ustar G0 D).card = 2 := by
        rcases hUbad with h | h | h | h <;> (rw [h]; decide)
      omega
  obtain ⟨K, hKmin⟩ := hexMinCover (Ustar G0 D)
  have hKT := hcov K hKmin
  have hlift := hcover_lift (Ustar G0 D) K hKmin.1
  have hU_ge3 : 3 ≤ (Ustar G0 D).card := by
    by_contra hlt
    rcases hC0_or_R2 with hC0ne | hR2
    · have hC0pos : 1 ≤ (centreless G0 D).card := Finset.card_pos.mpr hC0ne
      omega
    · omega
  by_cases hC0ne : (centreless G0 D).Nonempty
  · have hC0pos : 1 ≤ (centreless G0 D).card := Finset.card_pos.mpr hC0ne
    by_cases hj3 : 3 ≤ (junk G0 D).card
    · have hU_ge4 : 4 ≤ (Ustar G0 D).card := by omega
      have hcnt3 : 15 + (tops G0 D \ centreless G0 D).card + 2 * (centreless G0 D).card +
          (junk G0 D).card + (orN G0 D \ lam G0 D).card ≤ D.size + (Ustar G0 D).card := by omega
      exact hDge (c3 G0 D rfl ⟨⟨hAndOr, hReads, hLen2⟩, hfun, hleast⟩ hT hstar hoff hcnt3 hcov hC0pos hR_pos hj3 hU_ge4)
    · have hj_eq2 : (junk G0 D).card = 2 := by omega
      have hcnt2 : 17 + (tops G0 D \ centreless G0 D).card + 2 * (centreless G0 D).card +
          (orN G0 D \ lam G0 D).card ≤ D.size + (Ustar G0 D).card := by omega
      exact hDge (c2 G0 D rfl ⟨⟨hAndOr, hReads, hLen2⟩, hfun, hleast⟩ hT hstar hoff hcnt2 hcov hC0pos hR_pos hj_eq2 hU_ge3)
  · have hC0emp : centreless G0 D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC0ne
    have hR2 : 2 ≤ (orN G0 D \ lam G0 D).card := hC0_or_R2.resolve_left hC0ne
    have hC0card : (centreless G0 D).card = 0 := by rw [hC0emp]; rfl
    have hTdiff : tops G0 D \ centreless G0 D = tops G0 D := by rw [hC0emp, Finset.sdiff_empty]
    have hcnt1 : 15 + (tops G0 D).card + (junk G0 D).card +
        (orN G0 D \ lam G0 D).card ≤ D.size + (Ustar G0 D).card := by
      rw [hTdiff, hC0card] at hcnt
      omega
    have hcov1 : ∀ K : Finset (Fin 11), IsMinCover (G0.deleteEdges ↑(Ustar G0 D)) K → K.card ≤ (tops G0 D).card := by
      intro K' hK'
      have := hcov K' hK'
      rwa [hTdiff] at this
    exact hDge (c1 G0 D rfl ⟨⟨hAndOr, hReads, hLen2⟩, hfun, hleast⟩ hT hstar hoff hcnt1 hcov1 hC0emp hj2 hR2 hU_ge3)
