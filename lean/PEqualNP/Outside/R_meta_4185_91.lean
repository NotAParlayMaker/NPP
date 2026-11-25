import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverPromise

-- The finite bipartite matching-cover argument is adapted from the checked reduction R_meta_2685_41.
theorem PEqualNP.Outside.R_meta_4185_91
    (matchingCharge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ (K : Finset (Fin n)) (M : Finset (Fin n × Fin n)),
      (∀ e ∈ M, e.1 ∈ K ∧ e.2 ∉ K ∧ G.Adj e.1 e.2) →
      (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) →
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      M.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card + 2*(centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card)
    (exchange : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K X : Finset (Fin n)),
      NestedCover.IsMinCover G K → X ⊆ K → (∀ u ∈ X, ∀ v ∈ X, ¬ G.Adj u v) →
      X.card ≤ (X.biUnion fun u => G.neighborFinset u \ K).card)
    (defectCharge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ (K X : Finset (Fin n)) (M : Finset (Fin n × Fin n)),
      NestedCover.IsMinCover G K → X ⊆ K → (¬ ∃ s : Fin n → Bool, ∀ u ∈ X, ∀ v, G.Adj u v → (v ∈ X ∨ v ∉ K) → s u ≠ s v) →
      (∀ e ∈ M, e.1 ∈ K ∧ e.2 ∉ K ∧ G.Adj e.1 e.2) →
      (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) →
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      let N := X.biUnion fun u => G.neighborFinset u \ K
      N.card < X.card → M.card + (Ustar G C).card + X.card ≤
        (tops G C \ centreless G C).card + 2*(centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card + N.card) : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∃ (x9 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x9 ∧ x9.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
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

  intro n G inst C square nonempty least top
  classical
  let attainable (k : Nat) := ∃ K : Finset (Fin n), IsVertexCover G K ∧ K.card = k
  have ex : ∃ k, attainable k := ⟨_,Finset.univ,fun u _ _ => Or.inl (Finset.mem_univ u),rfl⟩
  obtain ⟨K,cover,eqK⟩ := Nat.find_spec ex
  have optimal : NestedCover.IsMinCover G K := by
    refine ⟨fun {u v} h => cover u v h,?_⟩
    intro T ht
    rw [eqK]
    exact Nat.find_min' ex ⟨T,fun _ _ h => ht h,rfl⟩
  let E := (Finset.univ : Finset (Fin n × Fin n)).filter fun e => e.1 ∈ K ∧ e.2 ∉ K ∧ G.Adj e.1 e.2
  obtain ⟨M,A,B,sub,fi,si,hits,dual⟩ := matchingCover n n E
  have edges e (he : e ∈ M) : e.1 ∈ K ∧ e.2 ∉ K ∧ G.Adj e.1 e.2 := (Finset.mem_filter.mp (sub he)).2
  have budget := matchingCharge n G C square nonempty least top K M edges (fun _ he _ hf eq => fi he hf eq) (fun _ he _ hf eq => si he hf eq)
  let X := K \ A
  let N := Finset.univ.filter fun v => v ∉ K ∧ ∃ u ∈ X, G.Adj u v
  have Ksplit : K.card ≤ A.card + X.card := by
    apply (Finset.card_le_card ?_).trans (Finset.card_union_le A X)
    intro u hu
    by_cases ha : u ∈ A
    · exact Finset.mem_union_left _ ha
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hu,ha⟩)
  have nbr (Z : Finset (Fin n)) : (Z.biUnion fun u => G.neighborFinset u \ K) =
      Finset.univ.filter (fun v => v ∉ K ∧ ∃ u ∈ Z, G.Adj u v) := by
    ext v
    simp only [Finset.mem_biUnion,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,Finset.mem_filter,
      Finset.mem_univ,true_and]
    constructor
    · rintro ⟨u,uz,uv,vk⟩; exact ⟨vk,u,uz,uv⟩
    · rintro ⟨vk,u,uz,uv⟩; exact ⟨u,uz,uv,vk⟩
  have near : N ⊆ B := by
    intro v hv
    obtain ⟨_,vn,u,ux,uv⟩ := Finset.mem_filter.mp hv
    obtain ⟨uk,ua⟩ := Finset.mem_sdiff.mp ux
    exact (hits (u,v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,uk,vn,uv⟩)).resolve_left ua
  have small := Finset.card_le_card near
  refine ⟨K,cover,?_⟩
  by_cases enough : X.card ≤ N.card
  · omega
  have odd : ¬ ∃ s : Fin n → Bool, ∀ u ∈ X, ∀ v, G.Adj u v →
      (v ∈ X ∨ v ∉ K) → s u ≠ s v := by
    rintro ⟨s,proper⟩
    let S (b : Bool) := X.filter fun u => s u = b
    let V (b : Bool) := Finset.univ.filter fun v => v ∉ K ∧ ∃ u ∈ S b, G.Adj u v
    have part (b : Bool) : (S b).card ≤ (V b).card := by
      change (S b).card ≤ (Finset.univ.filter fun v => v ∉ K ∧ ∃ u ∈ S b, G.Adj u v).card
      rw [← nbr]
      apply exchange n G K _ optimal ((Finset.filter_subset _ _).trans (Finset.sdiff_subset ..))
      intro u hu v hv adj
      obtain ⟨ux,colu⟩ := Finset.mem_filter.mp hu
      obtain ⟨vx,colv⟩ := Finset.mem_filter.mp hv
      exact proper u ux v adj (Or.inl vx) (colu.trans colv.symm)
    have sx : S false ∪ S true = X := by
      ext v
      simp [S]
      cases s v <;> simp
    have disjS : Disjoint (S false) (S true) := by
      apply Finset.disjoint_left.mpr
      intro v a b
      exact Bool.noConfusion ((Finset.mem_filter.mp a).2.symm.trans (Finset.mem_filter.mp b).2)
    have disjV : Disjoint (V false) (V true) := by
      apply Finset.disjoint_left.mpr
      intro v a b
      obtain ⟨_,vk,u,hu,uv⟩ := Finset.mem_filter.mp a
      obtain ⟨_,_,w,hw,wv⟩ := Finset.mem_filter.mp b
      obtain ⟨ux,colu⟩ := Finset.mem_filter.mp hu
      obtain ⟨wx,colw⟩ := Finset.mem_filter.mp hw
      have uv' := proper u ux v uv (Or.inr vk)
      have wv' := proper w wx v wv (Or.inr vk)
      cases hv : s v with
      | false => exact uv' (colu.trans hv.symm)
      | true => exact wv' (colw.trans hv.symm)
    have Vsub (b : Bool) : V b ⊆ N := by
      intro v hv
      obtain ⟨_,vk,u,hu,uv⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,vk,u,(Finset.mem_filter.mp hu).1,uv⟩
    have rest := Finset.card_le_card (Finset.union_subset (Vsub false) (Vsub true))
    rw [Finset.card_union_of_disjoint disjV] at rest
    have splitCard := Finset.card_union_of_disjoint disjS
    rw [sx] at splitCard
    have left := part false
    have right := part true
    omega
  have paid := defectCharge n G C square nonempty least top K X M optimal (Finset.sdiff_subset ..)
    odd edges (fun _ he _ hf eq => fi he hf eq) (fun _ he _ hf eq => si he hf eq) (by rw [nbr]; exact Nat.lt_of_not_ge enough)
  rw [nbr] at paid
  change M.card + (Ustar G C).card + X.card ≤ _ + N.card at paid
  omega
