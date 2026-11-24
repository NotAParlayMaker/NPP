import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.EdgeOwnership
open scoped BigOperators

theorem PEqualNP.Outside.R_meta_3241_683
    (clean : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      let f : (Fin (n+m) → Bool) → Bool := fun z => decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) C → circuitFun (n+m) C = f →
      ∃ D : Circuit, IsAO2 (n+m) D ∧ D.size ≤ C.size ∧
        (∀ u v, circuitFun (n+m) D (pairInput u v) = f (pairInput u v)) ∧
        (∀ j < D.size, (NestedCover.gateAt D j).op = GateOp.and → ∀ u v,
          gateVal (n+m) D j (pairInput u v) = true → f (pairInput u v) = true))
    (shape : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit),
      let safe (D : Circuit) (w : ℕ) :=
        ∀ u v : Fin n, (D.wires (List.ofFn (pairInput u v))).getD w false = true →
          f (pairInput u v) = true
      IsAO2 n C → (∀ u v, circuitFun n C (pairInput u v) = f (pairInput u v)) →
      (∀ j < C.size, (NestedCover.gateAt C j).op = GateOp.and → safe C (n+j)) →
      ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
        (∀ u v, circuitFun n D (pairInput u v) = f (pairInput u v)) ∧
        (∀ j < D.size,
          ((NestedCover.gateAt D j).op = GateOp.and →
            safe D (n+j) ∧ ¬safe D (opnd D j 0) ∧ ¬safe D (opnd D j 1)) ∧
          ((NestedCover.gateAt D j).op = GateOp.or → ¬safe D (n+j) →
            ¬safe D (opnd D j 0) ∧ ¬safe D (opnd D j 1))))
    (charge : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (D : Circuit),
      let f : (Fin (n+m) → Bool) → Bool := fun z => decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)
      let safe (w : ℕ) :=
        ∀ u v : Fin (n+m), (D.wires (List.ofFn (pairInput u v))).getD w false = true →
          f (pairInput u v) = true
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) D → (∀ u v, circuitFun (n+m) D (pairInput u v) = f (pairInput u v)) →
      (∀ j < D.size,
        ((NestedCover.gateAt D j).op = GateOp.and →
          safe (n+m+j) ∧ ¬safe (opnd D j 0) ∧ ¬safe (opnd D j 1)) ∧
        ((NestedCover.gateAt D j).op = GateOp.or → ¬safe (n+m+j) →
          ¬safe (opnd D j 0) ∧ ¬safe (opnd D j 1))) →
      M ⊆ E → (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) →
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) → E.card + M.card ≤ D.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   let x6 : ℕ := x1 + x2;   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬(x3 x7 x9 ∧ x3 x7 x10 ∧ x3 x8 x9 ∧ x3 x8 x10)) → PEqualNP.TopForm.IsAO2 x6 x5 → (∀ (x9 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → ∃ (x10 : List (ℕ × List ℕ)), (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < x6) ∨ x1 ≤ x11.1 ∧ x11.1 < x6 ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧ (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧ (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - (1 : ℕ) ≤ x5.size := by
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
  intro n m I _ C
  dsimp only
  intro square ao correct
  let E : Finset (Fin n × Fin m) := Finset.univ.filter fun e => I e.1 e.2
  have mem (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by simp [E]
  have sq (p q : Fin n) (l s : Fin m) (hp : p ≠ q) (hl : l ≠ s) :
      ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E) := by
    simpa only [mem] using square p q l s hp hl
  have eqF : circuitFun (n+m) C = fun z => decide (∃ p l, (p,l) ∈ E ∧
      z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) := by
    funext z
    simpa only [mem] using correct z
  obtain ⟨W, hW, hsizeW, hpairW, hcleanW⟩ := clean n m E C sq ao eqF
  obtain ⟨D, hD, hsize, hpair, hclean⟩ := shape (n+m) (fun z => decide (∃ p l, (p,l) ∈ E ∧
      z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) W hW hpairW hcleanW
  obtain ⟨M, A, B, hM, hm₁, hm₂, cover, hab⟩ := matchingCover n m E
  have budget := charge n m E M D sq hD hpair hclean hM
    (fun _ he _ hf => hm₁ he hf) (fun _ he _ hf => hm₂ he hf)
  let owner (e : Fin n × Fin m) : Fin n ⊕ Fin m :=
    if e.1 ∈ A then Sum.inl e.1 else Sum.inr e.2
  let fiber (s : Fin n ⊕ Fin m) := E.filter fun e => owner e = s
  let centers := (A.disjSum B).filter fun s => (fiber s).Nonempty
  have owner_mem (e) (he : e ∈ E) : owner e ∈ centers := by
    refine Finset.mem_filter.mpr ⟨?_, ⟨e, Finset.mem_filter.mpr ⟨he,rfl⟩⟩⟩
    have hc := cover e he
    by_cases h : e.1 ∈ A
    · simp [owner, h]
    · simp [owner, h, hc.resolve_left h]
  let star : Fin n ⊕ Fin m → ℕ × List ℕ := Sum.elim
    (fun p => (p.val, (fiber (.inl p)).toList.map fun e => n + e.2.val))
    (fun l => (n + l.val, (fiber (.inr l)).toList.map fun e => e.1.val))
  have starlen (s) : (star s).2.length = (fiber s).card := by
    cases s <;> simp [star]
  have sizestar : (centers.toList.map (fun s => (star s).2.length)).sum = E.card := by
    simp_rw [starlen]
    rw [Finset.sum_map_toList, ← Finset.card_eq_sum_card_fiberwise owner_mem]
  have centerCount : centers.card ≤ A.card + B.card := by
    simpa using (Finset.card_filter_le (s := A.disjSum B)
      (p := fun s => (fiber s).Nonempty))
  refine ⟨centers.toList.map star, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    have hs' := (Finset.mem_filter.mp (Finset.mem_toList.mp hs)).2
    refine ⟨?_, ?_⟩
    · intro hnil
      have hp := hs'.card_pos
      have he := starlen s
      rw [hnil] at he
      simp at he
      omega
    cases s with
    | inl p =>
      refine Or.inl ⟨p.isLt, ?_⟩
      intro z hz
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hz
      have := e.2.isLt
      omega
    | inr l =>
      refine Or.inr ⟨by change n ≤ n + l.val; omega,
        by change n + l.val < n + m; have := l.isLt; omega, ?_⟩
      intro z hz
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hz
      exact e.1.isLt
  · intro p l
    rw [← mem p l]
    constructor
    · intro he
      have hs := Finset.mem_toList.mpr (owner_mem (p,l) he)
      refine ⟨star (owner (p,l)), List.mem_map.mpr ⟨_,hs,rfl⟩, ?_⟩
      by_cases h : p ∈ A
      · left
        simp only [owner, h, ite_true]
        change p.val = p.val ∧ n + l.val ∈ (fiber (.inl p)).toList.map (fun e => n + e.2.val)
        exact ⟨rfl, List.mem_map.mpr ⟨(p,l), Finset.mem_toList.mpr
          (Finset.mem_filter.mpr ⟨he, by simp [owner,h]⟩),rfl⟩⟩
      · right
        simp only [owner, h, ite_false]
        change n + l.val = n + l.val ∧ p.val ∈ (fiber (.inr l)).toList.map (fun e => e.1.val)
        exact ⟨rfl, List.mem_map.mpr ⟨(p,l), Finset.mem_toList.mpr
          (Finset.mem_filter.mpr ⟨he, by simp [owner,h]⟩),rfl⟩⟩
    · rintro ⟨t, ht, hleft | hright⟩
      all_goals obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
      · cases s with
        | inl q =>
          obtain ⟨e, he, hm⟩ := List.mem_map.mp hleft.2
          have hef := Finset.mem_filter.mp (Finset.mem_toList.mp he)
          have hq : q = p := Fin.ext hleft.1
          have hcol : e.2 = l := Fin.ext (by omega)
          have hrow : e.1 = q := by
            by_cases h : e.1 ∈ A <;> simpa [owner,h] using hef.2
          have heq : e = (p,l) := Prod.ext (hrow.trans hq) hcol
          simpa [heq] using hef.1
        | inr s =>
          have hl := p.isLt
          have he : n + s.val = p.val := hleft.1
          omega
      · cases s with
        | inl q =>
          have hq := q.isLt
          have he : q.val = n + l.val := hright.1
          omega
        | inr s =>
          obtain ⟨e, he, hm⟩ := List.mem_map.mp hright.2
          have hef := Finset.mem_filter.mp (Finset.mem_toList.mp he)
          have hs : s = l := Fin.ext (by have := hright.1; change n + s.val = n + l.val at this; omega)
          have hrow : e.1 = p := Fin.ext hm
          have hcol : e.2 = s := by
            by_cases h : e.1 ∈ A <;> simpa [owner,h] using hef.2
          have heq : e = (p,l) := Prod.ext hrow (hcol.trans hs)
          simpa [heq] using hef.1
  · rw [List.map_map]
    change (centers.toList.map fun s => (star s).2.length).sum + _ - 1 ≤ _
    rw [sizestar, List.length_map, Finset.length_toList]
    omega
