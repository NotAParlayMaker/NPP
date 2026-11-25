import PEqualNP.Defs

/-!
R_meta_612_8: L-meta-612 reduced to six obligations at the last vertex

`L-meta-612` says: for a graph `G` with no four cycle, every AND/OR circuit of fan-in at
most two for the edge function has at least `|E| + tau - 1` gates.

This file proves it from six obligations.  Write `w` for the last vertex.  The proof is a
strong induction on the number of edges, and the case split is on the degree of `w` and on
how many gates read the input wire of `w`.

The two branches that are closed here are the leaf branch, where fixing `x w` to false saves
one gate, and the branch where `deg w = 2` and at least two gates read the input of `w`,
where the fixing saves two.  Both need the circuit elimination as an obligation, since the
elimination machine of the library lives outside the whitelist of this step.

The remaining four branches are the isolated vertex, the vertex of degree at least three,
the vertex of degree at most two where the cover number drops, and the vertex of degree two
that only one gate reads.  The third of these is the case where the two branches of a single
elimination are both too small, and the fourth is its companion.
-/

namespace PEqualNP.Outside.R_meta_612_8

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.CoverPromise

variable {n : ℕ}

/-- The graph `G` with its last vertex deleted, renumbered by `Fin n`. -/
def delGraph (G : SimpleGraph (Fin (n + 1))) : SimpleGraph (Fin n) :=
  G.comap Fin.castSucc

/-- The embedding of `Fin n` into the vertices of `Fin (n + 1)` other than the last. -/
def delEmb : Fin n → ↥({Fin.last n}ᶜ : Set (Fin (n + 1))) :=
  fun i => ⟨i.castSucc, by simp⟩

lemma delEmb_injective : Function.Injective (delEmb (n := n)) := by
  intro a b h
  have hv : (delEmb a).val = (delEmb b).val := congrArg Subtype.val h
  simpa [delEmb] using hv

lemma delEmb_surjective : ∀ u : ↥({Fin.last n}ᶜ : Set (Fin (n + 1))),
    ∃ a : Fin n, delEmb a = u := by
  intro u
  have hu : u.val ≠ Fin.last n := fun h => u.2 (by simp [h])
  obtain ⟨i, hi⟩ | hlast := Fin.eq_castSucc_or_eq_last u.val
  · exact ⟨i, Subtype.ext (by simp [delEmb, hi])⟩
  · exact absurd hlast hu

lemma mem_delGraph_edgeSet (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
    (a b : Fin n) :
    s(a, b) ∈ (delGraph G).edgeSet ↔ G.Adj a.castSucc b.castSucc := by
  rw [SimpleGraph.mem_edgeSet]
  rfl

lemma mem_induce_edgeSet (G : SimpleGraph (Fin (n + 1)))
    (u v : ↥({Fin.last n}ᶜ : Set (Fin (n + 1)))) :
    s(u, v) ∈ (G.induce {Fin.last n}ᶜ).edgeSet ↔ G.Adj u.val v.val := by
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj]

lemma image_delEmb_edges (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    Sym2.map (delEmb (n := n)) '' (delGraph G).edgeSet
      = (G.induce {Fin.last n}ᶜ).edgeSet := by
  apply Set.Subset.antisymm
  · rintro e ⟨y, hy, rfl⟩
    induction y using Sym2.ind with
    | _ a b =>
      rw [mem_delGraph_edgeSet] at hy
      rw [Sym2.map_mk, mem_induce_edgeSet]
      exact hy
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_induce_edgeSet] at he
      obtain ⟨a, ha⟩ := delEmb_surjective u
      obtain ⟨b, hb⟩ := delEmb_surjective v
      refine ⟨s(a, b), ?_, ?_⟩
      · rw [mem_delGraph_edgeSet]
        rw [← ha, ← hb] at he
        exact he
      · rw [Sym2.map_mk, ha, hb]

/-- Edge count: the edges of `G` are the edges of the deleted graph plus the degree of `w`. -/
lemma edge_ncard_del (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    G.edgeSet.ncard = (delGraph G).edgeSet.ncard + G.degree (Fin.last n) := by
  have h1 : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have h2 : (G.induce {Fin.last n}ᶜ).edgeSet.ncard = (G.induce {Fin.last n}ᶜ).edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have hbridge : (delGraph G).edgeSet.ncard = (G.induce {Fin.last n}ᶜ).edgeSet.ncard := by
    rw [← image_delEmb_edges (G := G)]
    exact (Set.InjOn.ncard_image (Sym2.map.injective delEmb_injective).injOn).symm
  have h3 : (G.induce {Fin.last n}ᶜ).edgeFinset.card
      = (G.deleteIncidenceSet (Fin.last n)).edgeFinset.card :=
    SimpleGraph.card_edgeFinset_induce_compl_singleton G (Fin.last n)
  have h4 : (G.deleteIncidenceSet (Fin.last n)).edgeFinset
      = G.edgeFinset \ G.incidenceFinset (Fin.last n) :=
    SimpleGraph.edgeFinset_deleteIncidenceSet_eq_sdiff G (Fin.last n)
  have h5 : (G.incidenceFinset (Fin.last n)).card = G.degree (Fin.last n) :=
    SimpleGraph.card_incidenceFinset_eq_degree G (Fin.last n)
  have h6 := Finset.card_sdiff_add_card_eq_card
    (SimpleGraph.incidenceFinset_subset G (Fin.last n))
  rw [hbridge, h2, h1, h3, h4]
  omega

/-- A vertex cover of the deleted graph, together with `w`, covers `G`. -/
lemma cover_del (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
    {S : Finset (Fin n)}
    (hS : IsVertexCover (delGraph G) S) :
    IsVertexCover G (S.image Fin.castSucc ∪ {Fin.last n}) := by
  intro u v huv
  obtain ⟨i, rfl⟩ | hu := Fin.eq_castSucc_or_eq_last u
  · obtain ⟨j, rfl⟩ | hv := Fin.eq_castSucc_or_eq_last v
    · rcases hS i j (mem_delGraph_edgeSet G i j |>.mpr huv) with h | h
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))
      · exact Or.inr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))
    · exact Or.inr (Finset.mem_union_right _ (Finset.mem_singleton.mpr hv))
  · exact Or.inl (Finset.mem_union_right _ (Finset.mem_singleton.mpr hu))

/-- That cover is at most one larger than the cover of the deleted graph. -/
lemma card_cover_del {S : Finset (Fin n)} :
    (S.image Fin.castSucc ∪ {Fin.last n}).card ≤ S.card + 1 := by
  calc (S.image Fin.castSucc ∪ {Fin.last n}).card
      ≤ (S.image Fin.castSucc).card + ({Fin.last n} : Finset (Fin (n + 1))).card :=
        Finset.card_union_le _ _
    _ ≤ S.card + 1 := by
        have h := Finset.card_image_le (s := S) (f := (Fin.castSucc : Fin n → Fin (n + 1)))
        simp only [Finset.card_singleton]
        omega

/-- The whole vertex set covers every edge. -/
lemma cover_univ (H : SimpleGraph (Fin n)) : IsVertexCover H Finset.univ := by
  intro i j _
  exact Or.inl (Finset.mem_univ i)

/-- A cover of the middle size: some size is attained and no cover is smaller. -/
lemma min_cover (H : SimpleGraph (Fin n)) (h : ∃ S : Finset (Fin n), IsVertexCover H S) :
    ∃ t' : ℕ, (∃ S : Finset (Fin n), IsVertexCover H S ∧ S.card = t') ∧
      ∀ S : Finset (Fin n), IsVertexCover H S → t' ≤ S.card := by
  classical
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), IsVertexCover H S ∧ S.card = k := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S.card, S, hS, rfl⟩
  obtain ⟨S0, hS0, hcard0⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, ⟨S0, hS0, hcard0⟩, ?_⟩
  intro S hS
  exact Nat.find_min' hex ⟨S, hS, rfl⟩

/-- The no-four-cycle hypothesis descends to the deleted graph. -/
lemma four_del {G : SimpleGraph (Fin (n + 1))}
    (h : ∀ a b c d : Fin (n + 1), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : (delGraph G).Adj a b) (h2 : (delGraph G).Adj b c) (h3 : (delGraph G).Adj c d) :
    ¬ (delGraph G).Adj d a := by
  intro h4
  exact h a.castSucc b.castSucc c.castSucc d.castSucc
    (by simpa using hab) (by simpa using hac) (by simpa using had)
    (by simpa using hbc) (by simpa using hbd) (by simpa using hcd) h1 h2 h3 h4

/-- An adjacency in the deleted graph gives an edge, so its edge set is not empty. -/
lemma exists_adj_of_ncard_pos (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
    (h : 0 < (delGraph G).edgeSet.ncard) :
    ∃ u v : Fin n, (delGraph G).Adj u v := by
  by_contra hcon
  push Not at hcon
  have hempty : (delGraph G).edgeSet = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      exact hcon a b he
  rw [hempty] at h
  exact absurd h (by simp)

end PEqualNP.Outside.R_meta_612_8

open PEqualNP.Outside.R_meta_612_8

theorem PEqualNP.Outside.R_meta_612_8
    (isolated : ∀ (n t : ℕ) (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
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
      G.degree (Fin.last n) = 0 →
      G.edgeSet.ncard + t ≤ C.size + 1)
    (high : ∀ (n t : ℕ) (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
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
      3 ≤ G.degree (Fin.last n) →
      G.edgeSet.ncard + t ≤ C.size + 1)
    (drops : ∀ (n t : ℕ) (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
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
      G.degree (Fin.last n) ≤ 2 →
      (∃ S : Finset (Fin n),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (G.comap Fin.castSucc) S ∧
        S.card + 1 = t) →
      G.edgeSet.ncard + t ≤ C.size + 1)
    (single : ∀ (n t : ℕ) (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
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
      G.degree (Fin.last n) = 2 →
      (C.gates.filter (fun g => n ∈ g.inputs)).length ≤ 1 →
      G.edgeSet.ncard + t ≤ C.size + 1)
    (elimOne : ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin (n + 1), G.Adj u v) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin (n + 1) → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin (n + 1), G.Adj u v ∧ x u = true ∧ x v = true)) →
      G.degree (Fin.last n) = 1 →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (s' : ℕ),
        PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ s' ∧ s' + 1 ≤ C.size ∧
        ∀ y : Fin n → Bool, (D.eval (List.ofFn y) = true ↔
          ∃ u v : Fin n, (G.comap Fin.castSucc).Adj u v ∧ y u = true ∧ y v = true))
    (elimTwo : ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin (n + 1), G.Adj u v) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin (n + 1) → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin (n + 1), G.Adj u v ∧ x u = true ∧ x v = true)) →
      G.degree (Fin.last n) = 2 →
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
        rcases Nat.lt_or_ge (G.degree (Fin.last k)) 1 with h0 | h0
        · exact isolated k t G C hEdge hFour hcov hmin hmono hfun (by omega)
        rcases Nat.lt_or_ge (G.degree (Fin.last k)) 2 with h1 | h1
        · -- degree one: the leaf branch
          have hdeg : G.degree (Fin.last k) = 1 := by omega
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
              have : S'.card + 1 = t := by omega
              exact hdr ⟨S', hS'cov, this⟩
            have hdel : 0 < (delGraph G).edgeSet.ncard := by
              rcases Nat.eq_zero_or_pos (delGraph G).edgeSet.ncard with hz | hp
              · exfalso
                have hempty : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (delGraph G)
                    (∅ : Finset (Fin k)) := by
                  intro i j hij
                  have hmem : s(i, j) ∈ (delGraph G).edgeSet := by
                    rw [SimpleGraph.mem_edgeSet]
                    exact hij
                  have hpos : 0 < (delGraph G).edgeSet.ncard :=
                    (Set.ncard_pos (s := (delGraph G).edgeSet)).mpr ⟨_, hmem⟩
                  omega
                have hz' : t' = 0 := by simpa using hS'min ∅ hempty
                have hcard : S'.card = 0 := by omega
                have ht1 : 1 ≤ t := by
                  obtain ⟨S, hS, hSc⟩ := hcov
                  rcases Nat.eq_zero_or_pos t with ht0 | htpos
                  · exfalso
                    have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
                    obtain ⟨u, v, huv⟩ := hEdge
                    have := hS u v huv
                    rw [hSe] at this
                    exact absurd this (by simp)
                  · exact htpos
                have : S'.card + 1 = t := by omega
                exact hdr ⟨S', hS'cov, this⟩
              · exact hp
            have hlt : (delGraph G).edgeSet.ncard < m := by
              have := edge_ncard_del G
              omega
            have hIH := ih _ hlt k t' (delGraph G) D rfl
              (exists_adj_of_ncard_pos G hdel)
              (fun a b c d hab hac had hbc hbd hcd h1 h2 h3 =>
                four_del hFour hab hac had hbc hbd hcd h1 h2 h3)
              ⟨S', hS'cov, hS'card⟩ hS'min hmonoD hfunD
            have hedge := edge_ncard_del G
            omega
        rcases Nat.lt_or_ge (G.degree (Fin.last k)) 3 with h2 | h2
        · -- degree two
          have hdeg : G.degree (Fin.last k) = 2 := by omega
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
              have : S'.card + 1 = t := by omega
              exact hdr ⟨S', hS'cov, this⟩
            have hdel : 0 < (delGraph G).edgeSet.ncard := by
              rcases Nat.eq_zero_or_pos (delGraph G).edgeSet.ncard with hz | hp
              · exfalso
                have hempty : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (delGraph G)
                    (∅ : Finset (Fin k)) := by
                  intro i j hij
                  have hmem : s(i, j) ∈ (delGraph G).edgeSet := by
                    rw [SimpleGraph.mem_edgeSet]
                    exact hij
                  have hpos : 0 < (delGraph G).edgeSet.ncard :=
                    (Set.ncard_pos (s := (delGraph G).edgeSet)).mpr ⟨_, hmem⟩
                  omega
                have hz' : t' = 0 := by simpa using hS'min ∅ hempty
                have hcard : S'.card = 0 := by omega
                have ht1 : 1 ≤ t := by
                  obtain ⟨S, hS, hSc⟩ := hcov
                  rcases Nat.eq_zero_or_pos t with ht0 | htpos
                  · exfalso
                    have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
                    obtain ⟨u, v, huv⟩ := hEdge
                    have := hS u v huv
                    rw [hSe] at this
                    exact absurd this (by simp)
                  · exact htpos
                have : S'.card + 1 = t := by omega
                exact hdr ⟨S', hS'cov, this⟩
              · exact hp
            have hlt : (delGraph G).edgeSet.ncard < m := by
              have := edge_ncard_del G
              omega
            have hIH := ih _ hlt k t' (delGraph G) D rfl
              (exists_adj_of_ncard_pos G hdel)
              (fun a b c d hab hac had hbc hbd hcd h1 h2 h3 =>
                four_del hFour hab hac had hbc hbd hcd h1 h2 h3)
              ⟨S', hS'cov, hS'card⟩ hS'min hmonoD hfunD
            have hedge := edge_ncard_del G
            omega
          · exact single k t G C hEdge hFour hcov hmin hmono hfun hdeg (by omega)
        · exact high k t G C hEdge hFour hcov hmin hmono hfun (by omega)
  exact key _ n t G C rfl hEdge hFour hcov hmin hmono hfun
