import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

private lemma card_ge_of_adj (k : ℕ) (B : Finset (Fin (2 * k)))
    (hadj : ∀ j j' : Fin (2 * k), j'.val = j.val + 1 → j ∈ B ∨ j' ∈ B) :
    k ≤ B.card := by
  let h : Fin k → Fin (2 * k) := fun r =>
    if (⟨2 * r.val, by omega⟩ : Fin (2 * k)) ∈ B
    then ⟨2 * r.val, by omega⟩
    else ⟨2 * r.val + 1, by omega⟩
  have hmem : ∀ r : Fin k, h r ∈ B := by
    intro r
    dsimp only [h]
    split_ifs with h1
    · exact h1
    · exact (hadj ⟨2 * r.val, by omega⟩ ⟨2 * r.val + 1, by omega⟩ rfl).resolve_left h1
  have hinj : Function.Injective h := by
    intro r1 r2 heq
    have hdiv : ∀ r : Fin k, (h r).val / 2 = r.val := by
      intro r
      dsimp only [h]
      split_ifs <;> dsimp only <;> omega
    have hv : (h r1).val = (h r2).val := congrArg Fin.val heq
    exact Fin.ext (by have := hdiv r1; have := hdiv r2; omega)
  calc
    k = (Finset.univ : Finset (Fin k)).card := by simp
    _ = (Finset.univ.image h).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ B.card := Finset.card_le_card (by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨r, _, rfl⟩
      exact hmem r)

private lemma card_ge_succ_of_endpoints (k : ℕ) (hk : 0 < k) (B : Finset (Fin (2 * k)))
    (h0 : (⟨0, by omega⟩ : Fin (2 * k)) ∈ B)
    (hlast : (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) ∈ B)
    (hadj : ∀ j j' : Fin (2 * k), j'.val = j.val + 1 → j ∈ B ∨ j' ∈ B) :
    k + 1 ≤ B.card := by
  let g : Fin (k + 1) → Fin (2 * k) := fun r =>
    if hr0 : r.val = 0 then ⟨0, by omega⟩
    else if hrk : r.val = k then ⟨2 * k - 1, by omega⟩
    else if (⟨2 * r.val - 1, by omega⟩ : Fin (2 * k)) ∈ B
         then ⟨2 * r.val - 1, by omega⟩
         else ⟨2 * r.val, by omega⟩
  have hmem : ∀ r : Fin (k + 1), g r ∈ B := by
    intro r
    dsimp only [g]
    split_ifs with hr0 hrk h1
    · exact h0
    · exact hlast
    · exact h1
    · exact (hadj ⟨2 * r.val - 1, by omega⟩ ⟨2 * r.val, by omega⟩ (by dsimp only; omega)).resolve_left h1
  have hinj : Function.Injective g := by
    intro r1 r2 heq
    have hdiv : ∀ r : Fin (k + 1), ((g r).val + 1) / 2 = r.val := by
      intro r
      dsimp only [g]
      split_ifs <;> dsimp only <;> omega
    have hv : (g r1).val = (g r2).val := congrArg Fin.val heq
    exact Fin.ext (by have := hdiv r1; have := hdiv r2; omega)
  calc
    k + 1 = (Finset.univ : Finset (Fin (k + 1))).card := by simp
    _ = (Finset.univ.image g).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ B.card := Finset.card_le_card (by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨r, _, rfl⟩
      exact hmem r)

theorem PEqualNP.Outside.L_meta_279 :
    ∀ (n k t : ℕ) (E : List (Fin n × Fin n)), 0 < k → (∀ e ∈ E, e.1 ≠ e.2) → E.Nodup → (∀ e ∈ E, (e.2, e.1) ∉ E) → ((∃ S : Finset (Fin n), (∀ i : Fin E.length, (E.get i).1 ∈ S ∨ (E.get i).2 ∈ S) ∧ S.card = t) ∧ ∀ S : Finset (Fin n), (∀ i : Fin E.length, (E.get i).1 ∈ S ∨ (E.get i).2 ∈ S) → t ≤ S.card) → ((∃ S : Finset (Fin n ⊕ (Fin E.length × Fin (2 * k))), (∀ (i : Fin E.length) (j : Fin (2 * k)), (j.val = 0 → Sum.inl (E.get i).1 ∈ S ∨ Sum.inr (i, j) ∈ S) ∧ (j.val + 1 = 2 * k → Sum.inr (i, j) ∈ S ∨ Sum.inl (E.get i).2 ∈ S) ∧ (∀ j' : Fin (2 * k), j'.val = j.val + 1 → Sum.inr (i, j) ∈ S ∨ Sum.inr (i, j') ∈ S)) ∧ S.card = t + k * E.length) ∧ ∀ S : Finset (Fin n ⊕ (Fin E.length × Fin (2 * k))), (∀ (i : Fin E.length) (j : Fin (2 * k)), (j.val = 0 → Sum.inl (E.get i).1 ∈ S ∨ Sum.inr (i, j) ∈ S) ∧ (j.val + 1 = 2 * k → Sum.inr (i, j) ∈ S ∨ Sum.inl (E.get i).2 ∈ S) ∧ (∀ j' : Fin (2 * k), j'.val = j.val + 1 → Sum.inr (i, j) ∈ S ∨ Sum.inr (i, j') ∈ S)) → t + k * E.length ≤ S.card) := by
  classical
  intro n k t E hk _ _ _ ⟨⟨S0, hS0_cov, hS0_card⟩, ht_min⟩
  constructor
  · let f : Fin E.length × Fin k → Fin n ⊕ (Fin E.length × Fin (2 * k)) := fun p =>
      Sum.inr (p.1,
        if (E.get p.1).1 ∈ S0
        then ⟨2 * p.2.val + 1, by omega⟩
        else ⟨2 * p.2.val, by omega⟩)
    let S : Finset (Fin n ⊕ (Fin E.length × Fin (2 * k))) :=
      S0.image Sum.inl ∪ Finset.univ.image f
    refine ⟨S, ?_, ?_⟩
    · have h_in_odd : ∀ (i : Fin E.length) (j : Fin (2 * k)),
          (E.get i).1 ∈ S0 → j.val % 2 = 1 → Sum.inr (i, j) ∈ S := by
        intro i j h1 hodd
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨(i, ⟨j.val / 2, by omega⟩), Finset.mem_univ _, ?_⟩
        simp only [f, h1, ↓reduceIte]
        congr 2
        apply Fin.ext
        dsimp only
        omega
      have h_in_even : ∀ (i : Fin E.length) (j : Fin (2 * k)),
          (E.get i).1 ∉ S0 → j.val % 2 = 0 → Sum.inr (i, j) ∈ S := by
        intro i j h1 heven
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨(i, ⟨j.val / 2, by omega⟩), Finset.mem_univ _, ?_⟩
        simp only [f, h1, ↓reduceIte]
        congr 2
        apply Fin.ext
        dsimp only
        omega
      intro i j
      refine ⟨?_, ?_, ?_⟩
      · intro hj0
        by_cases h1 : (E.get i).1 ∈ S0
        · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h1))
        · exact Or.inr (h_in_even i j h1 (by omega))
      · intro hjlast
        by_cases h1 : (E.get i).1 ∈ S0
        · exact Or.inl (h_in_odd i j h1 (by omega))
        · have h2 : (E.get i).2 ∈ S0 := (hS0_cov i).resolve_left h1
          exact Or.inr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h2))
      · intro j' hj'
        by_cases h1 : (E.get i).1 ∈ S0
        · by_cases hp : j.val % 2 = 1
          · exact Or.inl (h_in_odd i j h1 hp)
          · exact Or.inr (h_in_odd i j' h1 (by omega))
        · by_cases hp : j.val % 2 = 0
          · exact Or.inl (h_in_even i j h1 hp)
          · exact Or.inr (h_in_even i j' h1 (by omega))
    · have hdisj : Disjoint (S0.image Sum.inl) (Finset.univ.image f) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rcases Finset.mem_image.mp hx1 with ⟨v, _, rfl⟩
        rcases Finset.mem_image.mp hx2 with ⟨p, _, hp⟩
        simp only [f] at hp
        cases hp
      have hfinj : Function.Injective f := by
        intro p1 p2 heq
        rcases p1 with ⟨i1, m1⟩
        rcases p2 with ⟨i2, m2⟩
        simp only [f, Sum.inr.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨hi, hm⟩
        change i1 = i2 at hi
        subst hi
        change (if (E.get i1).1 ∈ S0 then (⟨2 * m1.val + 1, by omega⟩ : Fin (2 * k)) else ⟨2 * m1.val, by omega⟩) =
            (if (E.get i1).1 ∈ S0 then ⟨2 * m2.val + 1, by omega⟩ else ⟨2 * m2.val, by omega⟩) at hm
        congr 1
        apply Fin.ext
        split_ifs at hm <;> simp only [Fin.mk.injEq] at hm <;> omega
      rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ Sum.inl_injective,
          Finset.card_image_of_injective _ hfinj,
          hS0_card]
      simp [Nat.mul_comm]
  · intro S hS
    let A : Finset (Fin n) := Finset.univ.filter (fun v => Sum.inl v ∈ S)
    let B : Fin E.length → Finset (Fin (2 * k)) :=
      fun i => Finset.univ.filter (fun j => Sum.inr (i, j) ∈ S)
    let U : Finset (Fin E.length) :=
      Finset.univ.filter (fun i => (E.get i).1 ∉ A ∧ (E.get i).2 ∉ A)
    have hS_eq : S = A.image Sum.inl ∪
        Finset.univ.biUnion (fun i => (B i).image (fun j => Sum.inr (i, j))) := by
      ext x
      cases x with
      | inl v => simp [A]
      | inr p =>
        rcases p with ⟨i, j⟩
        simp [B]
    have hdisj_AB : Disjoint (A.image Sum.inl)
        (Finset.univ.biUnion (fun i => (B i).image (fun j => Sum.inr (i, j)))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_image.mp hx1 with ⟨v, _, rfl⟩
      simp at hx2
    have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin E.length)))
        (fun i => (B i).image (fun j => (Sum.inr (i, j) : Fin n ⊕ (Fin E.length × Fin (2 * k))))) := by
      intro i1 _ i2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_image.mp hx1 with ⟨j1, _, rfl⟩
      rcases Finset.mem_image.mp hx2 with ⟨j2, _, h2⟩
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h2
      exact hne h2.1.symm
    have hS_card : S.card = A.card + ∑ i : Fin E.length, (B i).card := by
      rw [hS_eq, Finset.card_union_of_disjoint hdisj_AB,
          Finset.card_image_of_injective _ Sum.inl_injective,
          Finset.card_biUnion hpair]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.card_image_of_injective
      intro j1 j2 heq
      simp only [Sum.inr.injEq, Prod.mk.injEq] at heq
      exact heq.2
    have hB_lb : ∀ i : Fin E.length, k + (if i ∈ U then 1 else 0) ≤ (B i).card := by
      intro i
      have hadj : ∀ j j' : Fin (2 * k), j'.val = j.val + 1 → j ∈ B i ∨ j' ∈ B i := by
        intro j j' hj'
        have h := (hS i j).2.2 j' hj'
        simpa [B] using h
      by_cases hi : i ∈ U
      · simp only [hi, ↓reduceIte]
        have hnot1 : Sum.inl (E.get i).1 ∉ S := by
          have := (Finset.mem_filter.mp hi).2.1
          simpa [A] using this
        have hnot2 : Sum.inl (E.get i).2 ∉ S := by
          have := (Finset.mem_filter.mp hi).2.2
          simpa [A] using this
        have h0 : (⟨0, by omega⟩ : Fin (2 * k)) ∈ B i := by
          have h := ((hS i ⟨0, by omega⟩).1 rfl).resolve_left hnot1
          simpa [B] using h
        have hlast : (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) ∈ B i := by
          have h := ((hS i ⟨2 * k - 1, by omega⟩).2.1 (by dsimp only; omega)).resolve_right hnot2
          simpa [B] using h
        exact card_ge_succ_of_endpoints k hk (B i) h0 hlast hadj
      · simp only [hi, ↓reduceIte, Nat.add_zero]
        exact card_ge_of_adj k (B i) hadj
    have hsum : E.length * k + U.card ≤ ∑ i : Fin E.length, (B i).card := by
      have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin E.length))) (fun i _ => hB_lb i)
      rw [Finset.sum_add_distrib] at h1
      simpa using h1
    let A' : Finset (Fin n) := A ∪ U.image (fun i => (E.get i).1)
    have hA'_cov : ∀ i : Fin E.length, (E.get i).1 ∈ A' ∨ (E.get i).2 ∈ A' := by
      intro i
      by_cases hi : i ∈ U
      · exact Or.inl (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi))
      · have hnot : ¬ ((E.get i).1 ∉ A ∧ (E.get i).2 ∉ A) := by
          simpa [U] using hi
        by_cases h1 : (E.get i).1 ∈ A
        · exact Or.inl (Finset.mem_union_left _ h1)
        · have h2 : (E.get i).2 ∈ A := by
            by_contra h2
            exact hnot ⟨h1, h2⟩
          exact Or.inr (Finset.mem_union_left _ h2)
    have ht_le : t ≤ A.card + U.card := by
      calc
        t ≤ A'.card := ht_min A' hA'_cov
        _ ≤ A.card + (U.image (fun i => (E.get i).1)).card := Finset.card_union_le _ _
        _ ≤ A.card + U.card := Nat.add_le_add_left Finset.card_image_le _
    have hmul : E.length * k = k * E.length := Nat.mul_comm _ _
    omega
