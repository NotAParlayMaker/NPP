import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

-- Three disjoint dirt pairs admit twelve possible common neighbors across their six ends.
-- The second child pays for edges with an endpoint of degree at most two.
theorem PEqualNP.Outside.R_meta_5330_923
    (geometry : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∀ v : Fin n, ∀ p : G.Walk v v, p.IsCycle → 5 ≤ p.length) → IsAO2 n C →
      let val := fun (j : ℕ) (u v : Fin n) => gateVal n C j (pairInput u v)
      let hit := fun (j : ℕ) => ∃ S : Finset (Fin n), S.card ≤ 12 ∧
        ∀ u v : Fin n, ¬G.Adj u v → val j u v = true → u ∈ S ∨ v ∈ S
      ∀ t g h, t ∈ tops G C → OrReaches n C (opnd C t 0) g → OrReaches n C (opnd C t 1) h → hit g ∨ hit h)
    (sparse : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), IsLeastAO G C →
      (G.edgeFinset.filter fun e => ∃ v : Fin n, G.degree v ≤ 2 ∧ e ∈ G.incidenceFinset v).card ≤
        2 * (C.size + 1))
    (remaining : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∀ v : Fin n, ∀ p : G.Walk v v, p.IsCycle → 5 ≤ p.length) → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      let val := fun (j : ℕ) (u v : Fin n) => gateVal n C j (pairInput u v)
      let outside := fun (j : ℕ) (u v : Fin n) => decide (∃ S : Finset (Fin n), S.card ≤ 12 ∧
        (u ∉ S ∨ v ∉ S) ∧ ∀ x y : Fin n, ¬G.Adj x y → val j x y = true → x ∈ S ∨ y ∈ S)
      ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u,v) ∧ 2 < G.degree u ∧ 2 < G.degree v ∧
        ∃ t ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C, g ≠ h ∧
        OrReaches n C (opnd C t 0) g ∧ OrReaches n C (opnd C t 1) h ∧
        (∀ j ∈ [g,h], val j u v = true ∧ val j u u = false ∧ val j v v = false) ∧ (outside g u v ∨ outside h u v))).card ≤ k * (C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x13 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨k, bound⟩ := remaining
  refine ⟨2+144+k,?_⟩
  intro n G _ C girth least topForm
  classical
  let val := fun (j : ℕ) (u v : Fin n) => gateVal n C j (pairInput u v)
  let hit := fun (j : ℕ) => ∃ S : Finset (Fin n), S.card ≤ 12 ∧
    ∀ u v : Fin n, ¬G.Adj u v → val j u v = true → u ∈ S ∨ v ∈ S
  let low := G.edgeFinset.filter fun e => ∃ v : Fin n, G.degree v ≤ 2 ∧ e ∈ G.incidenceFinset v
  let outside := fun (j : ℕ) (u v : Fin n) => decide (∃ S : Finset (Fin n), S.card ≤ 12 ∧
    (u ∉ S ∨ v ∉ S) ∧ ∀ x y : Fin n, ¬G.Adj x y → val j x y = true → x ∈ S ∨ y ∈ S)
  let high := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u,v) ∧ 2 < G.degree u ∧ 2 < G.degree v ∧
        ∃ t ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C, g ≠ h ∧
        OrReaches n C (opnd C t 0) g ∧ OrReaches n C (opnd C t 1) h ∧
        (∀ j ∈ [g,h], val j u v = true ∧ val j u u = false ∧ val j v v = false) ∧ (outside g u v ∨ outside h u v))
  have lowBound : low.card ≤ 2 * (C.size+1) := sparse n G C least
  have highBound : high.card ≤ k * (C.size+1) := bound n G C girth least topForm
  let B (j : ℕ) : Finset (Fin n) := if ok : hit j then Classical.choose ok else ∅
  have spec (j : ℕ) (ok : hit j) : (B j).card ≤ 12 ∧
      ∀ x y : Fin n, ¬G.Adj x y → val j x y = true → x ∈ B j ∨ y ∈ B j := by
    simpa only [B, dif_pos ok] using Classical.choose_spec ok
  let pairs (j : ℕ) := (B j ×ˢ B j).image (fun p => s(p.1,p.2))
  let paid := (Finset.range C.size).biUnion pairs
  have paidBound : paid.card ≤ 144 * (C.size+1) := by
    have hc (j : ℕ) : (B j).card ≤ 12 := by
      by_cases ok : hit j
      · exact (spec j ok).1
      · simp [B, ok]
    have aux : paid.card ≤ (Finset.range C.size).card * 144 := by
      apply Finset.card_biUnion_le_card_mul
      intro j _
      have h := Finset.card_image_le (f := fun p : Fin n × Fin n => s(p.1,p.2)) (s := B j ×ˢ B j)
      rw [Finset.card_product] at h
      exact h.trans (Nat.mul_le_mul (hc j) (hc j))
    rw [Finset.card_range] at aux
    omega
  apply (Finset.card_le_card (t := (low ∪ paid) ∪ high) ?_).trans
  · have a := Finset.card_union_le low paid
    have b := Finset.card_union_le (low ∪ paid) high
    simp only [Nat.add_mul]
    omega
  · intro e he
    obtain ⟨he, u,v,rfl,t,ht,g,hg,h,hh,neq,lg,rh,gpair,hpair,gu,gv,hu,hv⟩ := Finset.mem_filter.mp he
    have edge : s(u,v) ∈ G.edgeFinset := (Finset.mem_sdiff.mp he).1
    by_cases du : G.degree u ≤ 2
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨edge,u,du,?_⟩
      rw [G.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr ⟨edge, by simp⟩
    by_cases dv : G.degree v ≤ 2
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨edge,v,dv,?_⟩
      rw [G.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr ⟨edge, by simp⟩
    have hitOr : hit g ∨ hit h := geometry n G C girth least.1 t g h ht lg rh
    have choice (j : ℕ) (hj : j ∈ junk G C) (ok : hit j) :
        s(u,v) ∈ paid ∨ outside j u v := by
      by_cases both : u ∈ B j ∧ v ∈ B j
      · left
        have hj' : j < C.size := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        apply Finset.mem_biUnion.mpr
        exact ⟨j,Finset.mem_range.mpr hj', Finset.mem_image.mpr
          ⟨(u,v),Finset.mem_product.mpr both,rfl⟩⟩
      · right
        exact decide_eq_true ⟨B j,(spec j ok).1,by tauto,(spec j ok).2⟩
    have cases' : s(u,v) ∈ paid ∨ outside g u v ∨ outside h u v := by
      rcases hitOr with ok|ok
      · rcases choice g hg ok with paid|out
        · exact Or.inl paid
        · exact Or.inr (Or.inl out)
      · rcases choice h hh ok with paid|out
        · exact Or.inl paid
        · exact Or.inr (Or.inr out)
    rcases cases' with already|unpaid
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ already)
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨he, u,v,rfl, Nat.lt_of_not_ge du, Nat.lt_of_not_ge dv, t,ht,g,hg,h,hh,neq,lg,rh,?_,?_⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl|rfl
      · exact ⟨gpair,gu,gv⟩
      · exact ⟨hpair,hu,hv⟩
    · exact unpaid
