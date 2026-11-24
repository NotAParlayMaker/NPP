import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- The separator and its remaining matching give a cover of the residual graph.
-- Use the whole-graph cover bound to handle low deficit before the circuit cases.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_2704_619
    (positive : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
        fun e => (e / 11, e % 11)) →
      IsLeastAO G C → TopForm G C → (Ustar G C).Nonempty →
      0 < 2 * (centreless G C).card + (orN G C \ lam G C).card)
    (two : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
        fun e => (e / 11, e % 11)) →
      IsLeastAO G C → TopForm G C → C.size < 22 →
      (∃ i j, junk G C = {i,j} ∧ InCone 11 C i j) →
      let U := Ustar G C
      U.card = 2 → centreless G C = ∅ → (orN G C \ lam G C).card = 1 →
      ∀ K : Finset (Fin 11), (G.deleteEdges (U : Set (Sym2 (Fin 11)))).IsVertexCover (K : Set (Fin 11)) →
      K.card = 5 → False)
    (larger : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
        fun e => (e / 11, e % 11)) →
      IsLeastAO G C → TopForm G C → C.size < 22 →
      (∃ i j, junk G C = {i,j} ∧ InCone 11 C i j) →
      let U := Ustar G C
      let P := 2 * (centreless G C).card + (orN G C \ lam G C).card
      3 ≤ U.card → 0 < P → P + 2 < 2 * U.card →
      ∀ K : Finset (Fin 11), (G.deleteEdges (U : Set (Sym2 (Fin 11)))).IsVertexCover (K : Set (Fin 11)) →
      7 ≤ K.card + U.card → 5 + U.card ≤ K.card + P) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →             have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             let x10 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x9;             have x11 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};             have x12 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};             ∀ x13 ⊆ x11,               (∀ x15 ∈ x11 \ x13, ∀ x17 ∈ x11 \ x13, ¬x10.Adj x15 x17) →                 have x16 : Finset (Fin (11 : ℕ)) := {x16 ∈ Finset.univ \ x11 | ∃ x17 ∈ x11 \ x13, x10.Adj x17 x16};                 have x17 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x17 ∈ x12 | x10.Adj x17.1 x17.2 ∧ x17.1 ∉ x16 ∧ x17.2 ∉ x16};                 (5 : ℕ) + x9.card ≤ x13.card + x16.card + x17.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  classical
  let V := Fin 11

  let edges : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let G₀ := edgeGraph 11 edges

  let cut : Finset V := {3,8,9,10}

  let matching : Finset (V × V) := {(1,4),(2,5),(6,7)}

  have listedShape (u v : V) (listed : (u.val,v.val) ∈ edges) :
      u ∈ cut ∨ v ∈ cut ∨ (u,v) ∈ matching ∨ (v,u) ∈ matching := by
    have atVal (x : V) (m : ℕ) (eq : x.val = m) : x = Fin.ofNat 11 m := by
      subst m
      exact (Fin.ofNat_val_eq_self x).symm
    simp only [edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
    rcases listed with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      (obtain ⟨hu, hv⟩ := h
       rw [atVal u _ hu, atVal v _ hv]
       decide +kernel)
  have graphShape (u v : V) (adj : G₀.Adj u v) :
      u ∈ cut ∨ v ∈ cut ∨ (u,v) ∈ matching ∨ (v,u) ∈ matching := by
    change u ≠ v ∧ ((u.val,v.val) ∈ edges ∨ (v.val,u.val) ∈ edges) at adj
    rcases adj.2 with forward | backward
    · exact listedShape u v forward
    · rcases listedShape v u backward with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))

  have noSmallCover : ∀ K : Finset V,
      (∀ a b : V, G₀.Adj a b → a ∈ K ∨ b ∈ K) → 7 ≤ K.card := by
    -- Two disjoint triangles and a disjoint five-cycle require 2, 2 and 3 vertices.
    let first : Fin 3 → V := ![1,4,8]
    let second : Fin 3 → V := ![3,6,7]
    let cycle : Fin 5 → V := ![0,9,5,2,10]
    have triangleBound : ∀ J : Finset (Fin 3),
        (∀ i : Fin 3, i ∈ J ∨ i + 1 ∈ J) → 2 ≤ J.card := by
      decide +kernel
    have cycleBound : ∀ J : Finset (Fin 5),
        (∀ i : Fin 5, i ∈ J ∨ i + 1 ∈ J) → 3 ≤ J.card := by
      decide +kernel
    intro K covers
    let hit {k : ℕ} (f : Fin k → V) := Finset.univ.filter fun i => f i ∈ K
    have hits {k : ℕ} [NeZero k] (f : Fin k → V)
        (adj : ∀ i : Fin k, G₀.Adj (f i) (f (i + 1))) :
        ∀ i : Fin k, i ∈ hit f ∨ i + 1 ∈ hit f := by
      intro i
      simpa [hit] using covers (f i) (f (i + 1)) (adj i)
    have inside {k : ℕ} (f : Fin k → V) : (hit f).image f ⊆ K := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hi).2
    have separate {k l : ℕ} (f : Fin k → V) (g : Fin l → V)
        (apart : ∀ i j, f i ≠ g j) : Disjoint ((hit f).image f) ((hit g).image g) := by
      refine Finset.disjoint_left.mpr ?_
      intro v hv hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j, _, h⟩ := Finset.mem_image.mp hw
      exact apart i j h.symm
    have b₁ := triangleBound (hit first) (hits first (by decide +kernel))
    have b₂ := triangleBound (hit second) (hits second (by decide +kernel))
    have b₃ := cycleBound (hit cycle) (hits cycle (by decide +kernel))
    have c₁ := Finset.card_image_of_injective (hit first) (f := first) (by decide +kernel)
    have c₂ := Finset.card_image_of_injective (hit second) (f := second) (by decide +kernel)
    have c₃ := Finset.card_image_of_injective (hit cycle) (f := cycle) (by decide +kernel)
    have d₁₂ := separate first second (by decide +kernel)
    have d₁₃ := separate first cycle (by decide +kernel)
    have d₂₃ := separate second cycle (by decide +kernel)
    have unionBound := Finset.card_le_card
      (Finset.union_subset (Finset.union_subset (inside first) (inside second)) (inside cycle))
    calc
      7 = 2 + 2 + 3 := rfl
      _ ≤ (hit first).card + (hit second).card + (hit cycle).card :=
        Nat.add_le_add (Nat.add_le_add b₁ b₂) b₃
      _ = (((hit first).image first ∪ (hit second).image second) ∪ (hit cycle).image cycle).card := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d₁₃, d₂₃⟩),
          Finset.card_union_of_disjoint d₁₂, c₁, c₂, c₃]
      _ ≤ K.card := unionBound

  have graph_deletion_cover (U : Finset (Sym2 V)) (K : Finset V)
      (covered : (G₀.deleteEdges (↑U : Set (Sym2 V))).IsVertexCover (↑K : Set V)) :
      7 ≤ K.card + U.card := by
    classical
    let extra := U.image (fun e => (Quot.out e).1)
    have full : ∀ a b : V, G₀.Adj a b → a ∈ K ∪ extra ∨ b ∈ K ∪ extra := by
      intro a b adj
      by_cases deleted : s(a,b) ∈ U
      · have proved : (Quot.out s(a,b)).1 ∈ extra := Finset.mem_image_of_mem _ deleted
        have out : s((Quot.out s(a,b)).1, (Quot.out s(a,b)).2) = s(a,b) := Quot.out_eq _
        rw [Sym2.eq_iff] at out
        rcases out with ⟨eq, _⟩ | ⟨eq, _⟩
        · exact Or.inl (Finset.mem_union_right _ (eq ▸ proved))
        · exact Or.inr (Finset.mem_union_right _ (eq ▸ proved))
      · have h : (G₀.deleteEdges (↑U : Set (Sym2 V))).Adj a b :=
          SimpleGraph.deleteEdges_adj.mpr ⟨adj, deleted⟩
        exact (covered h).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    have ecard : extra.card ≤ U.card := Finset.card_image_le
    exact (noSmallCover _ full).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left ecard _))

  let forced (H : SimpleGraph V) [DecidableRel H.Adj] (B : Finset V) : Finset V :=
    (Finset.univ \ cut).filter fun v => ∃ u ∈ cut \ B, H.Adj u v

  let remaining (H : SimpleGraph V) [DecidableRel H.Adj] (B : Finset V) : Finset (V × V) :=
    matching.filter fun e => H.Adj e.1 e.2 ∧ e.1 ∉ forced H B ∧ e.2 ∉ forced H B

  have cut_witness (H : SimpleGraph V) [DecidableRel H.Adj] (B : Finset V)
      (shape : ∀ u v : V, H.Adj u v →
        u ∈ cut ∨ v ∈ cut ∨ (u,v) ∈ matching ∨ (v,u) ∈ matching)
      (outsideIndependent : ∀ u ∈ cut \ B, ∀ v ∈ cut \ B, ¬ H.Adj u v) :
      ∃ K : Finset V, H.IsVertexCover (↑K : Set V) ∧
        K.card ≤ B.card + (forced H B).card + (remaining H B).card := by
    classical
    let F := forced H B
    let R := (remaining H B).image Prod.fst
    let K := (B ∪ F) ∪ R
    have intoB {u : V} (h : u ∈ B) : u ∈ K :=
      Finset.mem_union_left _ (Finset.mem_union_left _ h)
    have intoF {u : V} (h : u ∈ F) : u ∈ K :=
      Finset.mem_union_left _ (Finset.mem_union_right _ h)
    have intoR {u : V} (h : u ∈ R) : u ∈ K := Finset.mem_union_right _ h
    have intoForced {u v : V} (hc : u ∈ cut \ B) (hv : v ∉ cut) (hh : H.Adj u v) : v ∈ F := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩, u, hc, hh⟩
    have viaMatch {u v : V} (hm : (u,v) ∈ matching) (hh : H.Adj u v) : u ∈ K ∨ v ∈ K := by
      by_cases hu : u ∈ F
      · exact Or.inl (intoF hu)
      by_cases hv : v ∈ F
      · exact Or.inr (intoF hv)
      have stays : (u,v) ∈ remaining H B := Finset.mem_filter.mpr ⟨hm, hh, hu, hv⟩
      exact Or.inl (intoR (Finset.mem_image_of_mem Prod.fst stays))
    refine ⟨K, ?_, ?_⟩
    · intro u v adj
      show u ∈ K ∨ v ∈ K
      by_cases huB : u ∈ B
      · exact Or.inl (intoB huB)
      by_cases hvB : v ∈ B
      · exact Or.inr (intoB hvB)
      by_cases hu : u ∈ cut
      · have uc := Finset.mem_sdiff.mpr ⟨hu, huB⟩
        by_cases hv : v ∈ cut
        · exact (outsideIndependent u uc v (Finset.mem_sdiff.mpr ⟨hv, hvB⟩) adj).elim
        · exact Or.inr (intoF (intoForced uc hv adj))
      by_cases hv : v ∈ cut
      · exact Or.inl (intoF (intoForced (Finset.mem_sdiff.mpr ⟨hv, hvB⟩) hu adj.symm))
      rcases shape u v adj with ht | ht | h | h
      · exact (hu ht).elim
      · exact (hv ht).elim
      · exact viaMatch h adj
      · exact (viaMatch h adj.symm).symm
    · have lhs := Finset.card_union_le B F
      have rhs := Finset.card_union_le (B ∪ F) R
      have rcount : R.card ≤ (remaining H B).card := Finset.card_image_le
      change ((B ∪ F) ∪ R).card ≤ B.card + F.card + (remaining H B).card
      omega
  intro G inst C same least top small nested
  dsimp only
  intro B _ independent
  let U := Ustar G C
  let P := 2 * (centreless G C).card + (orN G C \ lam G C).card
  let H := G.deleteEdges (U : Set (Sym2 (Fin 11)))
  have fixed : G = G₀ := same
  have shape (u v : Fin 11) (uv : H.Adj u v) :
      u ∈ cut ∨ v ∈ cut ∨ (u,v) ∈ matching ∨ (v,u) ∈ matching := by
    have adj : G.Adj u v := (SimpleGraph.deleteEdges_adj.mp uv).1
    exact graphShape u v (fixed ▸ adj)
  obtain ⟨K, covers, coverCost⟩ := cut_witness H B shape independent
  have coverFixed : (G₀.deleteEdges (U : Set (Sym2 (Fin 11)))).IsVertexCover (K : Set (Fin 11)) := by
    rw [← fixed]
    exact covers
  have base := graph_deletion_cover U K coverFixed
  have normalized : G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
      fun e => (e / 11, e % 11)) := same.trans (by rfl)
  have enough : 5 + U.card ≤ K.card + P := by
    by_contra! short
    have needs : P + 2 < 2 * U.card := by omega
    have uPos : U.Nonempty := Finset.card_pos.mp (by omega)
    have pPos : 0 < P := positive G C normalized least top uPos
    by_cases hTwo : U.card = 2
    · have pOne : P = 1 := by omega
      have kFive : K.card = 5 := by omega
      change 2 * (centreless G C).card + (orN G C \ lam G C).card = 1 at pOne
      have empty : centreless G C = ∅ := Finset.card_eq_zero.mp (by omega)
      have only : (orN G C \ lam G C).card = 1 := by omega
      exact two G C normalized least top small nested hTwo empty only K covers kFive
    · have hLarger : 3 ≤ U.card := by omega
      exact (not_le_of_gt short) (larger G C normalized least top small nested
        hLarger pPos needs K covers base)
  change 5 + U.card ≤ B.card + (forced H B).card + (remaining H B).card +
    2 * (centreless G C).card + (orN G C \ lam G C).card
  change K.card ≤ B.card + (forced H B).card + (remaining H B).card at coverCost
  dsimp only [P] at enough
  omega
