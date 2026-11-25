import PEqualNP.Defs

/-!
R_meta_612_8: L-meta-612 reduced to obligations at the last vertex.

Write w for the last vertex of a graph with no four cycle.  The proof is a strong induction
on the number of edges, and the case split is on the degree of w and on how many gates read
the input wire of w.

The leaf branch and the branch with degree two and at least two readers are closed here.  The
former uses the obligation that fixing that input to false saves one gate, the latter the
obligation that with two readers it saves two.  The rest is arithmetic on the edge count and
the cover number.  The remaining branches are the obligations of the cut.

Every auxiliary statement is proved inside the one declaration, since a reduction file holds a
single declaration only.
-/

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise

theorem PEqualNP.Outside.R_meta_612_8
    (counting : ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
      G.edgeSet.ncard = (G.comap Fin.castSucc).edgeSet.ncard + Nat.card (G.neighborSet (Fin.last n)))
    (isolated : ∀ (n t : ℕ) (G : SimpleGraph (Fin (n + 1)))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin (n + 1), G.Adj u v) →
      (∀ a b c d : Fin (n + 1), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S : Finset (Fin (n + 1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧
        S.card = t) →
      (∀ S : Finset (Fin (n + 1)),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin (n + 1) → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin (n + 1), G.Adj u v ∧ x u = true ∧ x v = true)) →
      Nat.card (G.neighborSet (Fin.last n)) = 0 →
      G.edgeSet.ncard + t ≤ C.size + 1)
    (high : ∀ (n t : ℕ) (G : SimpleGraph (Fin (n + 1)))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin (n + 1), G.Adj u v) →
      (∀ a b c d : Fin (n + 1), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S : Finset (Fin (n + 1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧
        S.card = t) →
      (∀ S : Finset (Fin (n + 1)),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin (n + 1) → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin (n + 1), G.Adj u v ∧ x u = true ∧ x v = true)) →
      3 ≤ Nat.card (G.neighborSet (Fin.last n)) →
      G.edgeSet.ncard + t ≤ C.size + 1)
    (drops : ∀ (n t : ℕ) (G : SimpleGraph (Fin (n + 1)))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin (n + 1), G.Adj u v) →
      (∀ a b c d : Fin (n + 1), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S : Finset (Fin (n + 1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧
        S.card = t) →
      (∀ S : Finset (Fin (n + 1)),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin (n + 1) → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin (n + 1), G.Adj u v ∧ x u = true ∧ x v = true)) →
      Nat.card (G.neighborSet (Fin.last n)) ≤ 2 →
      (∃ S : Finset (Fin n),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (G.comap Fin.castSucc) S ∧
        S.card + 1 = t) →
      G.edgeSet.ncard + t ≤ C.size + 1)
    (single : ∀ (n t : ℕ) (G : SimpleGraph (Fin (n + 1)))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin (n + 1), G.Adj u v) →
      (∀ a b c d : Fin (n + 1), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S : Finset (Fin (n + 1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧
        S.card = t) →
      (∀ S : Finset (Fin (n + 1)),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin (n + 1) → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin (n + 1), G.Adj u v ∧ x u = true ∧ x v = true)) →
      Nat.card (G.neighborSet (Fin.last n)) = 2 →
      (C.gates.filter (fun g => n ∈ g.inputs)).length ≤ 1 →
      G.edgeSet.ncard + t ≤ C.size + 1)
    (elimOne : ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1)))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin (n + 1), G.Adj u v) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin (n + 1) → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin (n + 1), G.Adj u v ∧ x u = true ∧ x v = true)) →
      Nat.card (G.neighborSet (Fin.last n)) = 1 →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (s' : ℕ),
        PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ s' ∧ s' + 1 ≤ C.size ∧
        ∀ y : Fin n → Bool, (D.eval (List.ofFn y) = true ↔
          ∃ u v : Fin n, (G.comap Fin.castSucc).Adj u v ∧ y u = true ∧ y v = true))
    (elimTwo : ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1)))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin (n + 1), G.Adj u v) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin (n + 1) → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin (n + 1), G.Adj u v ∧ x u = true ∧ x v = true)) →
      Nat.card (G.neighborSet (Fin.last n)) = 2 →
      2 ≤ (C.gates.filter (fun g => n ∈ g.inputs)).length →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (s' : ℕ),
        PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ s' ∧ s' + 2 ≤ C.size ∧
        ∀ y : Fin n → Bool, (D.eval (List.ofFn y) = true ↔
          ∃ u v : Fin n, (G.comap Fin.castSucc).Adj u v ∧ y u = true ∧ y v = true)) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧
        S.card = t) →
      (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S →
        t ≤ S.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  intro n t G C hEdge hFour hcov hmin hmono hfun
  have mem_del : ∀ {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (a b : Fin n),
      s(a, b) ∈ (G.comap Fin.castSucc).edgeSet ↔ G.Adj a.castSucc b.castSucc := by
    intro n G a b
    rw [SimpleGraph.mem_edgeSet]
    rfl
  have cover_del : ∀ {n : ℕ} (G : SimpleGraph (Fin (n + 1))) {S : Finset (Fin n)},
      IsVertexCover (G.comap Fin.castSucc) S →
      IsVertexCover G (S.image Fin.castSucc ∪ {Fin.last n}) := by
    intro n G S hS u v huv
    obtain ⟨i, rfl⟩ | hu := Fin.eq_castSucc_or_eq_last u
    · obtain ⟨j, rfl⟩ | hv := Fin.eq_castSucc_or_eq_last v
      · rcases hS i j (mem_del G i j |>.mpr huv) with h | h
        · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))
        · exact Or.inr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_singleton.mpr hv))
    · exact Or.inl (Finset.mem_union_right _ (Finset.mem_singleton.mpr hu))
  have card_cover_del : ∀ {n : ℕ} {S : Finset (Fin n)},
      (S.image Fin.castSucc ∪ {Fin.last n}).card ≤ S.card + 1 := by
    intro n S
    calc (S.image Fin.castSucc ∪ {Fin.last n}).card
        ≤ (S.image Fin.castSucc).card + ({Fin.last n} : Finset (Fin (n + 1))).card :=
          Finset.card_union_le _ _
      _ ≤ S.card + 1 := by
          have h := Finset.card_image_le (s := S) (f := (Fin.castSucc : Fin n → Fin (n + 1)))
          simp only [Finset.card_singleton]
          omega
  have cover_univ : ∀ {n : ℕ} (H : SimpleGraph (Fin n)), IsVertexCover H Finset.univ := by
    intro n H i j _
    exact Or.inl (Finset.mem_univ i)
  have min_cover : ∀ {n : ℕ} (H : SimpleGraph (Fin n)),
      (∃ S : Finset (Fin n), IsVertexCover H S) →
      ∃ t' : ℕ, (∃ S : Finset (Fin n), IsVertexCover H S ∧ S.card = t') ∧
        ∀ S : Finset (Fin n), IsVertexCover H S → t' ≤ S.card := by
    intro n H h
    classical
    have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), IsVertexCover H S ∧ S.card = k := by
      obtain ⟨S, hS⟩ := h
      exact ⟨S.card, S, hS, rfl⟩
    obtain ⟨S0, hS0, hcard0⟩ := Nat.find_spec hex
    refine ⟨Nat.find hex, ⟨S0, hS0, hcard0⟩, ?_⟩
    intro S hS
    exact Nat.find_min' hex ⟨S, hS, rfl⟩
  have four_del : ∀ {n : ℕ} {G : SimpleGraph (Fin (n + 1))},
      (∀ a b c d : Fin (n + 1), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        (G.comap Fin.castSucc).Adj a b → (G.comap Fin.castSucc).Adj b c →
        (G.comap Fin.castSucc).Adj c d → ¬ (G.comap Fin.castSucc).Adj d a := by
    intro n G h a b c d hab hac had hbc hbd hcd h1 h2 h3 h4
    exact h a.castSucc b.castSucc c.castSucc d.castSucc
      (by simpa using hab) (by simpa using hac) (by simpa using had)
      (by simpa using hbc) (by simpa using hbd) (by simpa using hcd) h1 h2 h3 h4
  have exists_adj : ∀ {n : ℕ} (G : SimpleGraph (Fin (n + 1))),
      0 < (G.comap Fin.castSucc).edgeSet.ncard → ∃ u v : Fin n, (G.comap Fin.castSucc).Adj u v := by
    intro n G h
    have hne : (G.comap Fin.castSucc).edgeSet.Nonempty := (Set.ncard_pos).mp h
    obtain ⟨e, he⟩ := hne
    revert he
    refine Sym2.ind (fun a b hmem => ?_) e
    rw [SimpleGraph.mem_edgeSet] at hmem
    exact ⟨a, b, hmem⟩
  have key : ∀ m : ℕ, ∀ (n t : ℕ) (G : SimpleGraph (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      G.edgeSet.ncard = m →
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧
        S.card = t) →
      (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S →
        t ≤ S.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      G.edgeSet.ncard + t ≤ C.size + 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro n t G C hm hEdge hFour hcov hmin hmono hfun
      cases n with
      | zero =>
        exact Fin.elim0 hEdge.choose
      | succ k =>
        haveI : DecidableRel G.Adj := Classical.decRel _
        have hedge := counting k G
        rcases Nat.lt_or_ge (Nat.card (G.neighborSet (Fin.last k))) 1 with h0 | h0
        · exact isolated k t G C hEdge hFour hcov hmin hmono hfun (by omega)
        rcases Nat.lt_or_ge (Nat.card (G.neighborSet (Fin.last k))) 2 with h1 | h1
        · have hdeg : Nat.card (G.neighborSet (Fin.last k)) = 1 := by omega
          by_cases hdr : ∃ S : Finset (Fin k),
              PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (G.comap Fin.castSucc) S ∧
              S.card + 1 = t
          · exact drops k t G C hEdge hFour hcov hmin hmono hfun (by omega) hdr
          · obtain ⟨D, s', hmonoD, hszD, hstepD, hfunD⟩ := elimOne k G C hEdge hmono hfun hdeg
            obtain ⟨t', ⟨S', hS'cov, hS'card⟩, hS'min⟩ :=
              min_cover (G.comap Fin.castSucc) ⟨Finset.univ, cover_univ _⟩
            have htle : t ≤ t' := by
              by_contra hcon
              rw [not_le] at hcon
              have hcovG : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G
                  (S'.image Fin.castSucc ∪ {Fin.last k}) := cover_del G hS'cov
              have hle := hmin _ hcovG
              have hle' := card_cover_del (n := k) (S := S')
              have hcard : S'.card + 1 = t := by omega
              exact hdr ⟨S', hS'cov, hcard⟩
            have hpos : 0 < (G.comap Fin.castSucc).edgeSet.ncard := by
              rcases Nat.eq_zero_or_pos (G.comap Fin.castSucc).edgeSet.ncard with hz | hp
              · exfalso
                have hempty : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
                    (G.comap Fin.castSucc) (∅ : Finset (Fin k)) := by
                  intro i j hij
                  have hpos : 0 < (G.comap Fin.castSucc).edgeSet.ncard :=
                    (Set.ncard_pos).mpr ⟨s(i, j), mem_del G i j |>.mpr hij⟩
                  omega
                have hzero' : t' = 0 := by simpa using hS'min ∅ hempty
                have hcard0 : S'.card = 0 := by omega
                have ht1 : 1 ≤ t := by
                  obtain ⟨S, hS, hSc⟩ := hcov
                  rcases Nat.eq_zero_or_pos t with ht0 | htpos
                  · exfalso
                    have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
                    obtain ⟨u, v, huv⟩ := hEdge
                    have hmem := hS u v huv
                    rw [hSe] at hmem
                    exact absurd hmem (by simp)
                  · exact htpos
                have hcard : S'.card + 1 = t := by omega
                exact hdr ⟨S', hS'cov, hcard⟩
              · exact hp
            have hgt : G.edgeSet.ncard = (G.comap Fin.castSucc).edgeSet.ncard + 1 := by
              omega
            have hlt : (G.comap Fin.castSucc).edgeSet.ncard < m := by omega
            have hIH := ih _ hlt k t' (G.comap Fin.castSucc) D rfl
              (exists_adj G hpos)
              (four_del hFour)
              ⟨S', hS'cov, hS'card⟩ hS'min hmonoD hfunD
            omega
        rcases Nat.lt_or_ge (Nat.card (G.neighborSet (Fin.last k))) 3 with h2 | h2
        · have hdeg : Nat.card (G.neighborSet (Fin.last k)) = 2 := by omega
          by_cases hdr : ∃ S : Finset (Fin k),
              PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (G.comap Fin.castSucc) S ∧
              S.card + 1 = t
          · exact drops k t G C hEdge hFour hcov hmin hmono hfun (by omega) hdr
          by_cases hread : 2 ≤ (C.gates.filter (fun g => k ∈ g.inputs)).length
          · obtain ⟨D, s', hmonoD, hszD, hstepD, hfunD⟩ :=
              elimTwo k G C hEdge hmono hfun hdeg hread
            obtain ⟨t', ⟨S', hS'cov, hS'card⟩, hS'min⟩ :=
              min_cover (G.comap Fin.castSucc) ⟨Finset.univ, cover_univ _⟩
            have htle : t ≤ t' := by
              by_contra hcon
              rw [not_le] at hcon
              have hcovG : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G
                  (S'.image Fin.castSucc ∪ {Fin.last k}) := cover_del G hS'cov
              have hle := hmin _ hcovG
              have hle' := card_cover_del (n := k) (S := S')
              have hcard : S'.card + 1 = t := by omega
              exact hdr ⟨S', hS'cov, hcard⟩
            have hpos : 0 < (G.comap Fin.castSucc).edgeSet.ncard := by
              rcases Nat.eq_zero_or_pos (G.comap Fin.castSucc).edgeSet.ncard with hz | hp
              · exfalso
                have hempty : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
                    (G.comap Fin.castSucc) (∅ : Finset (Fin k)) := by
                  intro i j hij
                  have hpos : 0 < (G.comap Fin.castSucc).edgeSet.ncard :=
                    (Set.ncard_pos).mpr ⟨s(i, j), mem_del G i j |>.mpr hij⟩
                  omega
                have hzero' : t' = 0 := by simpa using hS'min ∅ hempty
                have hcard0 : S'.card = 0 := by omega
                have ht1 : 1 ≤ t := by
                  obtain ⟨S, hS, hSc⟩ := hcov
                  rcases Nat.eq_zero_or_pos t with ht0 | htpos
                  · exfalso
                    have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
                    obtain ⟨u, v, huv⟩ := hEdge
                    have hmem := hS u v huv
                    rw [hSe] at hmem
                    exact absurd hmem (by simp)
                  · exact htpos
                have hcard : S'.card + 1 = t := by omega
                exact hdr ⟨S', hS'cov, hcard⟩
              · exact hp
            have hgt : G.edgeSet.ncard = (G.comap Fin.castSucc).edgeSet.ncard + 2 := by
              omega
            have hlt : (G.comap Fin.castSucc).edgeSet.ncard < m := by omega
            have hIH := ih _ hlt k t' (G.comap Fin.castSucc) D rfl
              (exists_adj G hpos)
              (four_del hFour)
              ⟨S', hS'cov, hS'card⟩ hS'min hmonoD hfunD
            omega
          · exact single k t G C hEdge hFour hcov hmin hmono hfun hdeg (by omega)
        · exact high k t G C hEdge hFour hcov hmin hmono hfun (by omega)
  exact key _ n t G C rfl hEdge hFour hcov hmin hmono hfun
