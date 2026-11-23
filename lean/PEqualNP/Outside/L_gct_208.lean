import Mathlib
import PEqualNP.Defs

private def phiFun (c : Fin 7 → ℂ) : Fin 4 × Fin 6 → ℂ
  | (0, 0) => -(c 4 + c 5 + c 6)
  | (0, 1) => c 0
  | (0, 2) => c 1
  | (0, 3) => c 2
  | (0, 4) => c 3
  | (0, 5) => -(c 0 + c 1 + c 2 + c 3)
  | (1, 0) => c 4
  | (2, 0) => c 5
  | (3, 0) => c 6
  | _ => 0

private def phi : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := phiFun
  map_add' x y := by
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [phiFun] <;> ring
  map_smul' r x := by
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [phiFun] <;> ring

private lemma phi_injective : Function.Injective phi := by
  intro x y h
  funext k
  fin_cases k
  · simpa [phi, phiFun] using congrFun h (0, 1)
  · simpa [phi, phiFun] using congrFun h (0, 2)
  · simpa [phi, phiFun] using congrFun h (0, 3)
  · simpa [phi, phiFun] using congrFun h (0, 4)
  · simpa [phi, phiFun] using congrFun h (1, 0)
  · simpa [phi, phiFun] using congrFun h (2, 0)
  · simpa [phi, phiFun] using congrFun h (3, 0)

private lemma phi_off_zero (c : Fin 7 → ℂ) (i : Fin 4) (j : Fin 6)
    (hi : i ≠ 0) (hj : j ≠ 0) : phi c (i, j) = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [phi, phiFun]

private def tag (f : Fin 4 ↪ Fin 6) : Fin 6 × Fin 4 :=
  (f 0, if f 1 = 0 then 1 else if f 2 = 0 then 2 else if f 3 = 0 then 3 else 0)

private def val (t : Fin 4 × Fin 6 → ℂ) (p : Fin 6 × Fin 4) : ℂ :=
  if p.1 = 0 then 1 + t (0, 0)
  else if p.2 = 0 then 1 + t (0, p.1)
  else (1 + t (0, p.1)) * (1 + t (p.2, 0))

private lemma prod_eq_val_tag (t : Fin 4 × Fin 6 → ℂ)
    (hoff : ∀ i j, i ≠ 0 → j ≠ 0 → t (i, j) = 0) (f : Fin 4 ↪ Fin 6) :
    (∏ i : Fin 4, (1 + t (i, f i))) = val t (tag f) := by
  rw [Fin.prod_univ_four]
  by_cases h0 : f 0 = 0
  · have h1 : f 1 ≠ 0 := fun h => by have := f.injective (h.trans h0.symm); exact absurd this (by decide)
    have h2 : f 2 ≠ 0 := fun h => by have := f.injective (h.trans h0.symm); exact absurd this (by decide)
    have h3 : f 3 ≠ 0 := fun h => by have := f.injective (h.trans h0.symm); exact absurd this (by decide)
    rw [hoff 1 (f 1) (by decide) h1, hoff 2 (f 2) (by decide) h2, hoff 3 (f 3) (by decide) h3]
    simp [val, tag, h0]
  · by_cases h1 : f 1 = 0
    · have h2 : f 2 ≠ 0 := fun h => by have := f.injective (h.trans h1.symm); exact absurd this (by decide)
      have h3 : f 3 ≠ 0 := fun h => by have := f.injective (h.trans h1.symm); exact absurd this (by decide)
      rw [hoff 2 (f 2) (by decide) h2, hoff 3 (f 3) (by decide) h3]
      simp [val, tag, h0, h1]
    · by_cases h2 : f 2 = 0
      · have h3 : f 3 ≠ 0 := fun h => by have := f.injective (h.trans h2.symm); exact absurd this (by decide)
        rw [hoff 1 (f 1) (by decide) h1, hoff 3 (f 3) (by decide) h3]
        simp [val, tag, h0, h1, h2]
      · by_cases h3 : f 3 = 0
        · rw [hoff 1 (f 1) (by decide) h1, hoff 2 (f 2) (by decide) h2]
          simp [val, tag, h0, h1, h2, h3]
        · rw [hoff 1 (f 1) (by decide) h1, hoff 2 (f 2) (by decide) h2, hoff 3 (f 3) (by decide) h3]
          simp [val, tag, h0, h1, h2, h3]

private lemma card_fin4_ne0 : Fintype.card {i : Fin 4 // i ≠ 0} = 3 := by decide

private lemma card_fin6_ne0 : Fintype.card {x : Fin 6 // x ≠ 0} = 5 := by decide

private lemma card_fin6_ne0_ne (j : Fin 6) (hj : j ≠ 0) :
    Fintype.card {x : Fin 6 // x ≠ 0 ∧ x ≠ j} = 4 := by
  fin_cases j
  · exact absurd rfl hj
  · decide
  · decide
  · decide
  · decide
  · decide

private lemma card_fin4_ne0_ne (k : Fin 4) (hk : k ≠ 0) :
    Fintype.card {i : Fin 4 // i ≠ 0 ∧ i ≠ k} = 2 := by
  fin_cases k
  · exact absurd rfl hk
  · decide
  · decide
  · decide

private lemma tag_eq_zero_zero_iff (f : Fin 4 ↪ Fin 6) :
    tag f = (0, 0) ↔ f 0 = 0 := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h0
    have h1 : f 1 ≠ 0 := fun h => by have := f.injective (h.trans h0.symm); exact absurd this (by decide)
    have h2 : f 2 ≠ 0 := fun h => by have := f.injective (h.trans h0.symm); exact absurd this (by decide)
    have h3 : f 3 ≠ 0 := fun h => by have := f.injective (h.trans h0.symm); exact absurd this (by decide)
    simp [tag, h0, h1, h2, h3]

private lemma tag_eq_nz_zero_iff (f : Fin 4 ↪ Fin 6) (j : Fin 6) (hj : j ≠ 0) :
    tag f = (j, 0) ↔ f 0 = j ∧ ∀ i : Fin 4, i ≠ 0 → f i ≠ 0 := by
  constructor
  · intro h
    have h0 : f 0 = j := congrArg Prod.fst h
    have h2 : (if f 1 = 0 then (1 : Fin 4) else if f 2 = 0 then 2 else if f 3 = 0 then 3 else 0) = 0 :=
      congrArg Prod.snd h
    refine ⟨h0, fun i hi => ?_⟩
    fin_cases i <;> dsimp at *
    · exact absurd rfl hi
    · intro hf1; simp [hf1] at h2
    · intro hf2
      by_cases hf1 : f 1 = 0
      · simp [hf1] at h2
      · simp [hf1, hf2] at h2
    · intro hf3
      by_cases hf1 : f 1 = 0
      · simp [hf1] at h2
      · by_cases hf2 : f 2 = 0
        · simp [hf1, hf2] at h2
        · simp [hf1, hf2, hf3] at h2
  · rintro ⟨h0, hall⟩
    have h1 := hall 1 (by decide)
    have h2 := hall 2 (by decide)
    have h3 := hall 3 (by decide)
    simp [tag, h0, h1, h2, h3]

private lemma tag_eq_nz_nz_iff (f : Fin 4 ↪ Fin 6) (j : Fin 6) (k : Fin 4)
    (hj : j ≠ 0) (hk : k ≠ 0) :
    tag f = (j, k) ↔ f 0 = j ∧ f k = 0 := by
  constructor
  · intro h
    have h0 : f 0 = j := congrArg Prod.fst h
    have hs : (if f 1 = 0 then (1 : Fin 4) else if f 2 = 0 then 2 else if f 3 = 0 then 3 else 0) = k :=
      congrArg Prod.snd h
    refine ⟨h0, ?_⟩
    by_cases h1 : f 1 = 0
    · simp only [h1, ↓reduceIte] at hs; rw [← hs]; exact h1
    · by_cases h2 : f 2 = 0
      · simp only [h1, h2, ↓reduceIte] at hs; rw [← hs]; exact h2
      · by_cases h3 : f 3 = 0
        · simp only [h1, h2, h3, ↓reduceIte] at hs; rw [← hs]; exact h3
        · simp only [h1, h2, h3, ↓reduceIte] at hs; exact absurd hs.symm hk
  · rintro ⟨h0, hfk⟩
    fin_cases k <;> dsimp at *
    · exact absurd rfl hk
    · simp [tag, h0, hfk]
    · have h1 : f 1 ≠ 0 := fun h => by have := f.injective (h.trans hfk.symm); exact absurd this (by decide)
      simp [tag, h0, h1, hfk]
    · have h1 : f 1 ≠ 0 := fun h => by have := f.injective (h.trans hfk.symm); exact absurd this (by decide)
      have h2 : f 2 ≠ 0 := fun h => by have := f.injective (h.trans hfk.symm); exact absurd this (by decide)
      simp [tag, h0, h1, h2, hfk]

private lemma fiber_card (p : Fin 6 × Fin 4) :
    (Finset.univ.filter (fun f : Fin 4 ↪ Fin 6 => tag f = p)).card =
      if p.1 = 0 then (if p.2 = 0 then 60 else 0)
      else (if p.2 = 0 then 24 else 12) := by
  rcases p with ⟨j, k⟩
  dsimp only
  by_cases hj : j = 0
  · subst hj
    by_cases hk : k = 0
    · subst hk
      simp only [↓reduceIte]
      rw [← Fintype.card_subtype]
      let e : {f : Fin 4 ↪ Fin 6 // tag f = (0, 0)} ≃ ({i : Fin 4 // i ≠ 0} ↪ {x : Fin 6 // x ≠ 0}) :=
        { toFun := fun ⟨f, hf⟩ =>
            { toFun := fun i => ⟨f i.1, fun hx => i.2 (f.injective (hx.trans ((tag_eq_zero_zero_iff f).1 hf).symm))⟩
              inj' := fun a b h => Subtype.ext (f.injective (congrArg Subtype.val h)) }
          invFun := fun g =>
            ⟨{ toFun := fun i => if h : i = 0 then 0 else (g ⟨i, h⟩).1
               inj' := fun a b h => by
                 by_cases ha : a = 0 <;> by_cases hb : b = 0
                 · exact ha.trans hb.symm
                 · simp only [ha, hb, ↓reduceDIte] at h
                   exact absurd h.symm (g ⟨b, hb⟩).2
                 · simp only [ha, hb, ↓reduceDIte] at h
                   exact absurd h (g ⟨a, ha⟩).2
                 · simp only [ha, hb, ↓reduceDIte] at h
                   exact congrArg Subtype.val (g.injective (Subtype.ext h)) },
              (tag_eq_zero_zero_iff _).2 (by simp)⟩
          left_inv := fun ⟨f, hf⟩ => by
            apply Subtype.ext
            apply DFunLike.ext
            intro i
            by_cases hi : i = 0
            · subst hi; simp [((tag_eq_zero_zero_iff f).1 hf)]
            · simp [hi]; rfl
          right_inv := fun g => by
            apply DFunLike.ext
            intro i
            apply Subtype.ext
            simp [i.2] }
      rw [Fintype.card_congr e, Fintype.card_embedding_eq, card_fin6_ne0, card_fin4_ne0]
      rfl
    · simp only [↓reduceIte, hk]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro f _ h
      have h0 : f 0 = 0 := congrArg Prod.fst h
      have h00 : tag f = (0, 0) := (tag_eq_zero_zero_iff f).2 h0
      exact hk (congrArg Prod.snd (h.symm.trans h00))
  · by_cases hk : k = 0
    · subst hk
      simp only [hj, ↓reduceIte]
      rw [← Fintype.card_subtype]
      let e : {f : Fin 4 ↪ Fin 6 // tag f = (j, 0)} ≃
          ({i : Fin 4 // i ≠ 0} ↪ {x : Fin 6 // x ≠ 0 ∧ x ≠ j}) :=
        { toFun := fun ⟨f, hf⟩ =>
            have hspec := (tag_eq_nz_zero_iff f j hj).1 hf
            { toFun := fun i =>
                ⟨f i.1, hspec.2 i.1 i.2, fun hx => i.2 (f.injective (hx.trans hspec.1.symm))⟩
              inj' := fun a b h => Subtype.ext (f.injective (congrArg Subtype.val h)) }
          invFun := fun g =>
            ⟨{ toFun := fun i => if h : i = 0 then j else (g ⟨i, h⟩).1
               inj' := fun a b h => by
                 by_cases ha : a = 0 <;> by_cases hb : b = 0
                 · exact ha.trans hb.symm
                 · simp only [ha, hb, ↓reduceDIte] at h
                   exact absurd h.symm (g ⟨b, hb⟩).2.2
                 · simp only [ha, hb, ↓reduceDIte] at h
                   exact absurd h (g ⟨a, ha⟩).2.2
                 · simp only [ha, hb, ↓reduceDIte] at h
                   exact congrArg Subtype.val (g.injective (Subtype.ext h)) },
              (tag_eq_nz_zero_iff _ j hj).2 ⟨by simp, fun i hi => by
                change (if h : i = 0 then j else (g ⟨i, h⟩).1) ≠ 0
                rw [dif_neg hi]
                exact (g ⟨i, hi⟩).2.1⟩⟩
          left_inv := fun ⟨f, hf⟩ => by
            have hspec := (tag_eq_nz_zero_iff f j hj).1 hf
            apply Subtype.ext
            apply DFunLike.ext
            intro i
            by_cases hi : i = 0
            · subst hi; simp [hspec.1]
            · simp [hi]; rfl
          right_inv := fun g => by
            apply DFunLike.ext
            intro i
            apply Subtype.ext
            simp [i.2] }
      rw [Fintype.card_congr e, Fintype.card_embedding_eq, card_fin6_ne0_ne j hj, card_fin4_ne0]
      rfl
    · simp only [hj, hk, ↓reduceIte]
      rw [← Fintype.card_subtype]
      let e : {f : Fin 4 ↪ Fin 6 // tag f = (j, k)} ≃
          ({i : Fin 4 // i ≠ 0 ∧ i ≠ k} ↪ {x : Fin 6 // x ≠ 0 ∧ x ≠ j}) :=
        { toFun := fun ⟨f, hf⟩ =>
            have hspec := (tag_eq_nz_nz_iff f j k hj hk).1 hf
            { toFun := fun i =>
                ⟨f i.1,
                  fun hx => i.2.2 (f.injective (hx.trans hspec.2.symm)),
                  fun hx => i.2.1 (f.injective (hx.trans hspec.1.symm))⟩
              inj' := fun a b h => Subtype.ext (f.injective (congrArg Subtype.val h)) }
          invFun := fun g =>
            ⟨{ toFun := fun i =>
                 if h0 : i = 0 then j
                 else if hk' : i = k then 0
                 else (g ⟨i, h0, hk'⟩).1
               inj' := fun a b h => by
                 by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0
                 · exact ha0.trans hb0.symm
                 · by_cases hbk : b = k
                   · simp only [ha0, hb0, hbk, hk, ↓reduceDIte] at h; exact absurd h hj
                   · simp only [ha0, hb0, hbk, ↓reduceDIte] at h; exact absurd h.symm (g ⟨b, hb0, hbk⟩).2.2
                 · by_cases hak : a = k
                   · simp only [ha0, hb0, hak, hk, ↓reduceDIte] at h; exact absurd h.symm hj
                   · simp only [ha0, hb0, hak, ↓reduceDIte] at h; exact absurd h (g ⟨a, ha0, hak⟩).2.2
                 · by_cases hak : a = k <;> by_cases hbk : b = k
                   · exact hak.trans hbk.symm
                   · simp only [ha0, hb0, hak, hbk, hk, ↓reduceDIte] at h
                     exact absurd h.symm (g ⟨b, hb0, hbk⟩).2.1
                   · simp only [ha0, hb0, hak, hbk, hk, ↓reduceDIte] at h
                     exact absurd h (g ⟨a, ha0, hak⟩).2.1
                   · simp only [ha0, hb0, hak, hbk, ↓reduceDIte] at h
                     exact congrArg Subtype.val (g.injective (Subtype.ext h)) },
              (tag_eq_nz_nz_iff _ j k hj hk).2 ⟨by simp, by simp [hk]⟩⟩
          left_inv := fun ⟨f, hf⟩ => by
            have hspec := (tag_eq_nz_nz_iff f j k hj hk).1 hf
            apply Subtype.ext
            apply DFunLike.ext
            intro i
            by_cases hi0 : i = 0
            · subst hi0; simp [hspec.1]
            · by_cases hik : i = k
              · subst hik; simp [hi0, hspec.2]
              · simp [hi0, hik]; rfl
          right_inv := fun g => by
            apply DFunLike.ext
            intro i
            apply Subtype.ext
            simp [i.2.1, i.2.2] }
      rw [Fintype.card_congr e, Fintype.card_embedding_eq, card_fin6_ne0_ne j hj, card_fin4_ne0_ne k hk]
      rfl

theorem PEqualNP.Outside.L_gct_208 :
    ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧
      Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range phi, ?_, ?_⟩
  · rintro t ⟨c, rfl⟩
    have hsum : (∑ f : Fin 4 ↪ Fin 6, ∏ i : Fin 4, (1 + phi c (i, f i))) =
        ∑ p : Fin 6 × Fin 4,
          ((Finset.univ.filter (fun f : Fin 4 ↪ Fin 6 => tag f = p)).card : ℂ) * val (phi c) p := by
      calc (∑ f : Fin 4 ↪ Fin 6, ∏ i : Fin 4, (1 + phi c (i, f i)))
          = ∑ f : Fin 4 ↪ Fin 6, val (phi c) (tag f) := by
              refine Finset.sum_congr rfl fun f _ => ?_
              exact prod_eq_val_tag (phi c) (phi_off_zero c) f
        _ = ∑ p : Fin 6 × Fin 4, ∑ f ∈ Finset.univ.filter (fun f : Fin 4 ↪ Fin 6 => tag f = p),
              val (phi c) (tag f) := by
              symm
              exact Finset.sum_fiberwise Finset.univ tag (fun f => val (phi c) (tag f))
        _ = ∑ p : Fin 6 × Fin 4,
              ((Finset.univ.filter (fun f : Fin 4 ↪ Fin 6 => tag f = p)).card : ℂ) * val (phi c) p := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_congr rfl (fun f hf => by rw [(Finset.mem_filter.1 hf).2])]
              rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    simp_rw [fiber_card]
    rw [Fintype.sum_prod_type, Fin.sum_univ_six]
    simp only [Fin.sum_univ_four, val, phi, LinearMap.coe_mk, AddHom.coe_mk, phiFun]
    norm_num
    ring
  · rw [LinearMap.finrank_range_of_inj phi_injective, Module.finrank_fin_fun]
