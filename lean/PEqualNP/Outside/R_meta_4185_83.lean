import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.CoverPromise

-- Split off heads matched to independent leaves. Only the remaining vertices
-- need an odd-cycle deletion. On the resulting bipartite graph a matching pays
-- for a minimum cover. The Hall argument below follows R_meta_2685_41.
theorem PEqualNP.Outside.R_meta_4185_83
    (crown : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ A B W : Finset (Fin n), Disjoint A B ∧ Disjoint A W ∧ Disjoint B W ∧
      A ∪ B ∪ W = Finset.univ ∧ (∀ a ∈ A, ∀ v, G.Adj a v → v ∈ B) ∧
      (∃ m : B → A, Function.Injective m ∧ ∀ b : B, G.Adj b.val (m b).val) ∧
      (∃ σ : W ≃ W, ∀ w : W, G.Adj w.val (σ w).val))
    (sparse : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      (∀ j ∈ junk G C ∪ mixing G C, (gammaE G C j ∩ Ustar G C).card ≤ 1) →
      (∀ h ∈ centreless G C, (gammaE G C h ∩ Ustar G C).card ≤ 2) →
      ∃ K : Finset (Fin n), IsVertexCover G K ∧
        K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card + 2*(centreless G C).card +
          (junk G C).card + (orN G C \ lam G C).card)
    (matching : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((∃ j ∈ junk G C ∪ mixing G C, 1 < (gammaE G C j ∩ Ustar G C).card) ∨
        ∃ h ∈ centreless G C, 2 < (gammaE G C h ∩ Ustar G C).card) →
      ∀ (k : ℕ) (x y : Fin k → Fin n), Function.Injective (Sum.elim x y) →
      (∀ i, G.Adj (x i) (y i)) →
      (Ustar G C).card+k ≤ (tops G C \ centreless G C).card + 2*(centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card)
    (odd : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((∃ j ∈ junk G C ∪ mixing G C, 1 < (gammaE G C j ∩ Ustar G C).card) ∨
        ∃ h ∈ centreless G C, 2 < (gammaE G C h ∩ Ustar G C).card) →
      ∀ W : Finset (Fin n), (∃ σ : W ≃ W, ∀ w : W, G.Adj w.val (σ w).val) →
      let colors (V L : Finset (Fin n)) := ∀ u ∈ V, ∀ v ∈ V, G.Adj u v → (u ∈ L ↔ v ∉ L)
      (¬ ∃ L, colors W L) → ∃ Z L : Finset (Fin n), Z ⊆ W ∧ colors (W \ Z) L ∧
        (∀ z ∈ Z, ∃ u ∈ W \ Z, ∃ v ∈ W \ Z, u ∈ L ∧ v ∉ L ∧ G.Adj z u ∧ G.Adj z v) ∧
        ∀ (k : ℕ) (x y : Fin k → Fin n), Function.Injective (Sum.elim x y) →
        (∀ i, G.Adj (x i) (y i) ∧ x i ∉ Z ∧ y i ∉ Z) →
        (Ustar G C).card+k+Z.card ≤ (tops G C \ centreless G C).card + 2*(centreless G C).card +
          (junk G C).card + (orN G C \ lam G C).card) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∃ (x9 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x9 ∧ x9.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  classical
  have saturate {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (r : α → β → Prop) (A : Finset α) (B : Finset β)
      (cov : ∀ a b, r a b → a ∈ A ∨ b ∈ B)
      (minimal : ∀ (X : Finset α) (Y : Finset β),
        (∀ a b, r a b → a ∈ X ∨ b ∈ Y) → A.card+B.card ≤ X.card+Y.card) :
      ∃ f : A → β, Function.Injective f ∧ ∀ a : A, r a (f a) ∧ f a ∉ B := by
    classical
    let adj (a : A) := Finset.univ.filter fun b => r a b ∧ b ∉ B
    have hall (s : Finset A) : s.card ≤ (s.biUnion adj).card := by
      let X : Finset α := s.map (Function.Embedding.subtype _)
      let Y := s.biUnion adj
      have Xsub : X ⊆ A := by
        intro a ha
        obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
        exact i.property
      have replacement : ∀ a b, r a b → a ∈ A \ X ∨ b ∈ B ∪ Y := by
        intro a b h
        by_cases hb : b ∈ B
        · exact Or.inr (Finset.mem_union_left _ hb)
        have ha := (cov a b h).resolve_right hb
        by_cases hx : a ∈ X
        · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
          exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,hb⟩⟩))
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨ha,hx⟩)
      have bound := minimal _ _ replacement
      have card := Finset.card_sdiff_add_card_eq_card Xsub
      have union := Finset.card_union_le B Y
      have sizeX : X.card = s.card := Finset.card_map _
      change s.card ≤ Y.card
      omega
    obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
    exact ⟨f,inj,fun a => (Finset.mem_filter.mp (mem a)).2⟩

  have matchingCover (n m : ℕ) (E : Finset (Fin n × Fin m)) :
      ∃ (M : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)),
        M ⊆ E ∧ Set.InjOn Prod.fst (M : Set (Fin n × Fin m)) ∧
        Set.InjOn Prod.snd (M : Set (Fin n × Fin m)) ∧
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ A.card+B.card ≤ M.card := by
    classical
    let cover (A : Finset (Fin n)) (B : Finset (Fin m)) :=
      ∀ a b, (a,b) ∈ E → a ∈ A ∨ b ∈ B
    have has : ∃ k, ∃ A B, cover A B ∧ A.card+B.card = k :=
      ⟨_,Finset.univ,∅,fun a _ _ => Or.inl (Finset.mem_univ a),rfl⟩
    obtain ⟨A,B,cov,least⟩ := Nat.find_spec has
    have minAB (X Y) (h : cover X Y) : A.card+B.card ≤ X.card+Y.card := by
      rw [least]
      exact Nat.find_min' has ⟨X,Y,h,rfl⟩
    obtain ⟨f,fi,hf⟩ := saturate (fun (a : Fin n) (b : Fin m) => (a,b) ∈ E) A B cov minAB
    obtain ⟨g,gi,hg⟩ := saturate (fun (b : Fin m) (a : Fin n) => (a,b) ∈ E) B A
      (fun b a h => (cov a b h).symm) (fun Y X h => by
        simpa only [Nat.add_comm] using minAB X Y (fun a b he => (h b a he).symm))
    let pair : A ⊕ B → Fin n × Fin m := Sum.elim (fun a => (a.val,f a)) (fun b => (g b,b.val))
    have first : Function.Injective (Prod.fst ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (Subtype.ext eq)
        | inr b => exact False.elim ((hg b).2 ((show a.val = g b from eq) ▸ a.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hg b).2 ((show a.val = g b from eq.symm) ▸ a.property))
        | inr b' => exact congrArg Sum.inr (gi eq)
    have second : Function.Injective (Prod.snd ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (fi eq)
        | inr b => exact False.elim ((hf a).2 ((show b.val = f a from eq.symm) ▸ b.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hf a).2 ((show b.val = f a from eq) ▸ b.property))
        | inr b' => exact congrArg Sum.inr (Subtype.ext eq)
    let M := Finset.univ.image pair
    refine ⟨M,A,B,?_,?_,?_,fun e he => cov _ _ he,?_⟩
    · intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      cases i with
      | inl a => exact (hf a).1
      | inr b => exact (hg b).1
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (first eq)
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (second eq)
    · simp [M,Finset.card_image_of_injective _ (Function.Injective.of_comp first)]

  have join {n : ℕ} (G : SimpleGraph (Fin n)) (A B W Z L R : Finset (Fin n))
      (M : Finset (Fin n × Fin n)) (ab : Disjoint A B) (aw : Disjoint A W)
      (bw : Disjoint B W) (zw : Z ⊆ W) (ls : L ⊆ W \ Z) (rs : R ⊆ W \ Z)
      (lr : Disjoint L R) (m : B → A) (mi : Function.Injective m)
      (ma : ∀ b : B, G.Adj b.val (m b).val)
      (edges : ∀ e ∈ M, e.1 ∈ L ∧ e.2 ∈ R ∧ G.Adj e.1 e.2)
      (fi : Set.InjOn Prod.fst (↑M : Set (Fin n × Fin n))) (si : Set.InjOn Prod.snd (↑M : Set (Fin n × Fin n))) :
      ∃ x y : Fin (B.card + M.card) → Fin n, Function.Injective (Sum.elim x y) ∧
        ∀ i, G.Adj (x i) (y i) ∧ x i ∉ Z ∧ y i ∉ Z := by
    classical
    let idx : Fin (B.card + M.card) ≃ (B ⊕ M) := Fintype.equivOfCardEq (by simp)
    let f : B ⊕ M → Fin n := Sum.elim Subtype.val (fun e => e.val.1)
    let g : B ⊕ M → Fin n := Sum.elim (fun b => (m b).val) (fun e => e.val.2)
    have sumInj {α β γ : Type} (p : α → γ) (q : β → γ)
        (hp : Function.Injective p) (hq : Function.Injective q) (sep : ∀ a b, p a ≠ q b) :
        Function.Injective (Sum.elim p q) := by
      intro u v eq
      cases u with
      | inl u =>
        cases v with
        | inl v => exact congrArg Sum.inl (hp eq)
        | inr v => exact False.elim (sep u v eq)
      | inr u =>
        cases v with
        | inl v => exact False.elim (sep v u eq.symm)
        | inr v => exact congrArg Sum.inr (hq eq)
    have ewL (e : M) := Finset.mem_sdiff.mp (ls (edges e.val e.property).1)
    have ewR (e : M) := Finset.mem_sdiff.mp (rs (edges e.val e.property).2.1)
    have diff {S T : Finset (Fin n)} (st : Disjoint S T) {s t : Fin n} (hs : s ∈ S) (ht : t ∈ T) :
        s ≠ t := fun eq => Finset.disjoint_left.mp st hs (eq ▸ ht)
    have hf : Function.Injective f := sumInj _ _ Subtype.val_injective
      (fun e d h => Subtype.ext (fi e.property d.property h))
      (fun b e => diff bw b.property (ewL e).1)
    have hg : Function.Injective g := sumInj _ _ (Subtype.val_injective.comp mi)
      (fun e d h => Subtype.ext (si e.property d.property h))
      (fun b e => diff aw (m b).property (ewR e).1)
    have separate (i j : B ⊕ M) : f i ≠ g j := by
      cases i with
      | inl b =>
        cases j with
        | inl d => exact diff ab.symm b.property (m d).property
        | inr e => exact diff bw b.property (ewR e).1
      | inr e =>
        cases j with
        | inl b => exact diff aw.symm (ewL e).1 (m b).property
        | inr d => exact diff lr (edges e.val e.property).1 (edges d.val d.property).2.1
    refine ⟨f ∘ idx, g ∘ idx, sumInj _ _ (hf.comp idx.injective) (hg.comp idx.injective)
      (fun i j => separate (idx i) (idx j)), ?_⟩
    intro i
    simp only [Function.comp_apply]
    cases idx i with
    | inl b => exact ⟨ma b,fun hz => Finset.disjoint_left.mp bw b.property (zw hz),
        fun hz => Finset.disjoint_left.mp aw (m b).property (zw hz)⟩
    | inr e => exact ⟨(edges e.val e.property).2.2,(ewL e).2,(ewR e).2⟩

  intro n G _ C h4 he least top
  by_cases overload : (∃ j ∈ junk G C ∪ mixing G C, 1 < (gammaE G C j ∩ Ustar G C).card) ∨
      ∃ h ∈ centreless G C, 2 < (gammaE G C h ∩ Ustar G C).card
  case neg =>
    exact sparse n G C h4 he least top
      (fun j hj => Nat.le_of_not_gt (fun big => overload (Or.inl ⟨j,hj,big⟩)))
      (fun j hj => Nat.le_of_not_gt (fun big => overload (Or.inr ⟨j,hj,big⟩)))
  obtain ⟨A,B,W,ab,aw,bw,whole,heads,⟨m,mi,ma⟩,perm⟩ := crown n G
  let colors (V L : Finset (Fin n)) := ∀ u ∈ V, ∀ v ∈ V, G.Adj u v → (u ∈ L ↔ v ∉ L)
  let cap := (tops G C \ centreless G C).card + 2*(centreless G C).card +
      (junk G C).card + (orN G C \ lam G C).card
  have packing : ∃ Z L : Finset (Fin n), Z ⊆ W ∧ colors (W \ Z) L ∧
      ∀ (k : ℕ) (x y : Fin k → Fin n), Function.Injective (Sum.elim x y) →
      (∀ i, G.Adj (x i) (y i) ∧ x i ∉ Z ∧ y i ∉ Z) → (Ustar G C).card+k+Z.card ≤ cap := by
    by_cases bip : ∃ L, colors W L
    · obtain ⟨L,hl⟩ := bip
      refine ⟨∅,L,Finset.empty_subset _,by simpa using hl,?_⟩
      intro k x y hinj hxy
      change (Ustar G C).card+k+0 ≤ cap
      rw [Nat.add_zero]
      exact matching n G C h4 he least top overload k x y hinj (fun i => (hxy i).1)
    · obtain ⟨Z,L,zw,col,_,bound⟩ := odd n G C h4 he least top overload W perm bip
      exact ⟨Z,L,zw,col,bound⟩
  obtain ⟨Z,P,zw,col,bound⟩ := packing
  let L := (W \ Z) ∩ P
  let R := (W \ Z) \ P
  have ls : L ⊆ W \ Z := Finset.inter_subset_left
  have rs : R ⊆ W \ Z := Finset.sdiff_subset
  have lr : Disjoint L R := Finset.disjoint_left.mpr (fun _ hl hr =>
    (Finset.mem_sdiff.mp hr).2 (Finset.mem_inter.mp hl).2)
  let E : Finset (Fin n × Fin n) := Finset.univ.filter fun e =>
    e.1 ∈ L ∧ e.2 ∈ R ∧ G.Adj e.1 e.2
  obtain ⟨M,X,Y,sub,fi,si,hits,dual⟩ := matchingCover n n E
  have members (e) (he : e ∈ M) : e.1 ∈ L ∧ e.2 ∈ R ∧ G.Adj e.1 e.2 :=
    (Finset.mem_filter.mp (sub he)).2
  obtain ⟨x,y,ij,avoid⟩ := join G A B W Z L R M ab aw bw zw ls rs lr m mi ma members fi si
  have budget := bound (B.card+M.card) x y ij avoid
  let K := ((B ∪ Z) ∪ X) ∪ Y
  refine ⟨K,?_,?_⟩
  · intro u v uv
    by_contra neither
    have outsideB (q : Fin n) (h : q ∉ K) : q ∉ B := by
      intro hB
      exact h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hB)))
    have inW (q r : Fin n) (hq : q ∉ K) (hr : r ∉ K) (adj : G.Adj q r) : q ∈ W \ Z := by
      have un : q ∈ A ∪ B ∪ W := whole ▸ Finset.mem_univ q
      have qw : q ∈ W := (Finset.mem_union.mp un).resolve_left (fun h =>
        (Finset.mem_union.mp h).elim (fun ha => outsideB r hr (heads q ha r adj)) (outsideB q hq))
      exact Finset.mem_sdiff.mpr ⟨qw,fun hz => hq (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hz)))⟩
    have nu : u ∉ K := fun h => neither (Or.inl h)
    have nv : v ∉ K := fun h => neither (Or.inr h)
    have hu := inW u v nu nv uv
    have hv := inW v u nv nu uv.symm
    have cross (q r : Fin n) (hq : q ∈ L) (hr : r ∈ R) (a : G.Adj q r) (nq : q ∉ K) (nr : r ∉ K) : False := by
      have edge : (q,r) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq,hr,a⟩
      exact (hits (q,r) edge).elim
        (fun hx => nq (Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
        (fun hy => nr (Finset.mem_union_right _ hy))
    by_cases h : u ∈ P
    · exact cross u v (Finset.mem_inter.mpr ⟨hu,h⟩)
        (Finset.mem_sdiff.mpr ⟨hv,(col u hu v hv uv).mp h⟩) uv nu nv
    · exact cross v u (Finset.mem_inter.mpr ⟨hv,(col v hv u hu uv.symm).mpr h⟩)
        (Finset.mem_sdiff.mpr ⟨hu,h⟩) uv.symm nv nu
  · have e1 := Finset.card_union_le B Z
    have e2 := Finset.card_union_le (B ∪ Z) X
    have e3 := Finset.card_union_le ((B ∪ Z) ∪ X) Y
    change (((B ∪ Z) ∪ X) ∪ Y).card + (Ustar G C).card ≤ cap
    omega
