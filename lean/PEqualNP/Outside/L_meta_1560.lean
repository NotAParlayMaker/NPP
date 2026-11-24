import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1560_aux

theorem main (L : Fin 21 → Finset (Fin 21)) (hL : ∀ t : Fin 21, L t = {t, t + 1, t + 4, t + 14, t + 16})
    (T : Finset (Fin 21)) (hT : T.card = 3) (hTL : ∀ t : Fin 21, ¬ T ⊆ L t) :
    (∀ f : (Fin 21 → Bool) → Bool,
      (∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) → f x = true → f y = true) →
      ∀ t : Fin 21,
        ((∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) → f x = decide (∃ v ∈ L t, x v = true)) ↔
          ((∀ a ∈ T ∩ L t, f (fun v : Fin 21 => decide (v = a)) = true) ∧
           (∀ a ∈ T \ L t, ∀ s ∈ L t \ T, f (fun v : Fin 21 => decide (v = a ∨ v = s)) = true) ∧
           f (fun v : Fin 21 => decide (v ∉ L t)) = false))) ∧
    (∀ t : Fin 21, ∃ v ∈ T, v ∉ L t) ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a)))).card = 3 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ L t, ∃ s ∈ L t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s)))).card = 54 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 21 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, (∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a))) ∨
      (∃ a ∈ T \ L t, ∃ s ∈ L t \ T, x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ∨
      x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 78 := by
  classical
  have hB : ∀ t : Fin 21, ∃ v ∈ T, v ∉ L t := by
    intro t
    by_contra h
    push_neg at h
    exact hTL t (fun v hv => h v hv)
  have hF2 : ∀ a : Fin 21, a ∈ L a := by
    intro a
    rw [hL]
    simp
  have hF1 : ∀ a s : Fin 21, a ≠ s → ∃ t : Fin 21, s ∈ L t ∧ a ∉ L t := by
    have key : ∀ a s : Fin 21, a ≠ s → ∃ t : Fin 21,
        s ∈ ({t, t + 1, t + 4, t + 14, t + 16} : Finset (Fin 21)) ∧
        a ∉ ({t, t + 1, t + 4, t + 14, t + 16} : Finset (Fin 21)) := by decide
    intro a s has
    obtain ⟨t, h1, h2⟩ := key a s has
    exact ⟨t, by rw [hL]; exact h1, by rw [hL]; exact h2⟩
  have hF3 : ∀ t t' : Fin 21, L t = L t' → t = t' := by
    have key : ∀ t t' : Fin 21, ({t, t + 1, t + 4, t + 14, t + 16} : Finset (Fin 21)) =
        {t', t' + 1, t' + 4, t' + 14, t' + 16} → t = t' := by decide
    intro t t' h
    rw [hL, hL] at h
    exact key t t' h
  have hF4 : ∀ t : Fin 21, (L t).card ≤ 5 := by
    intro t
    rw [hL]
    exact Finset.card_le_five
  have hco : ∀ t : Fin 21, 16 ≤ ((L t)ᶜ).card := by
    intro t
    rw [Finset.card_compl, Fintype.card_fin]
    have := hF4 t
    omega
  -- the three families of tests as images
  have m1 : ∀ x : Fin 21 → Bool, (∃ t : Fin 21, ∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a))) ↔
      x ∈ T.image (fun a : Fin 21 => (fun v : Fin 21 => decide (v = a))) := by
    intro x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨t, a, ha, rfl⟩
      exact ⟨a, (Finset.mem_inter.mp ha).1, rfl⟩
    · rintro ⟨a, haT, rfl⟩
      exact ⟨a, a, Finset.mem_inter.mpr ⟨haT, hF2 a⟩, rfl⟩
  have m2 : ∀ x : Fin 21 → Bool, (∃ t : Fin 21, ∃ a ∈ T \ L t, ∃ s ∈ L t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ↔
      x ∈ (T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => (fun v : Fin 21 => decide (v = p.1 ∨ v = p.2))) := by
    intro x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨t, a, ha, s, hs, rfl⟩
      refine ⟨(a, s), ?_, rfl⟩
      rw [Finset.mem_product, Finset.mem_compl]
      exact ⟨(Finset.mem_sdiff.mp ha).1, (Finset.mem_sdiff.mp hs).2⟩
    · rintro ⟨⟨a, s⟩, hp, rfl⟩
      rw [Finset.mem_product, Finset.mem_compl] at hp
      obtain ⟨t, h1, h2⟩ := hF1 a s (by rintro rfl; exact hp.2 hp.1)
      exact ⟨t, a, Finset.mem_sdiff.mpr ⟨hp.1, h2⟩, s, Finset.mem_sdiff.mpr ⟨h1, hp.2⟩, rfl⟩
  have m3 : ∀ x : Fin 21 → Bool, (∃ t : Fin 21, x = (fun v : Fin 21 => decide (v ∉ L t))) ↔
      x ∈ (Finset.univ : Finset (Fin 21)).image (fun t : Fin 21 => (fun v : Fin 21 => decide (v ∉ L t))) := by
    intro x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, Finset.mem_univ t, rfl⟩
    · rintro ⟨t, _, rfl⟩
      exact ⟨t, rfl⟩
  have c1 : (T.image (fun a : Fin 21 => (fun v : Fin 21 => decide (v = a)))).card = 3 := by
    rw [Finset.card_image_of_injective, hT]
    intro a b h
    have := congrFun h a
    simpa using this
  have c2 : ((T ×ˢ Tᶜ).image
      (fun p : Fin 21 × Fin 21 => (fun v : Fin 21 => decide (v = p.1 ∨ v = p.2)))).card = 54 := by
    rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_compl, Fintype.card_fin, hT]
    rintro ⟨a, s⟩ hp ⟨a', s'⟩ hq h
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_compl] at hp hq
    have h1 := congrFun h a
    have h2 := congrFun h s
    simp at h1 h2
    have e1 : a = a' := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hp.1) hq.2
    have e2 : s = s' := by
      rcases h2 with h2 | h2
      · exact absurd (h2 ▸ hq.1) hp.2
      · exact h2
    rw [e1, e2]
  have c3 : ((Finset.univ : Finset (Fin 21)).image
      (fun t : Fin 21 => (fun v : Fin 21 => decide (v ∉ L t)))).card = 21 := by
    rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro t t' h
    apply hF3
    ext v
    have := congrFun h v
    simp at this
    exact this
  have d12 : Disjoint (T.image (fun a : Fin 21 => (fun v : Fin 21 => decide (v = a))))
      ((T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => (fun v : Fin 21 => decide (v = p.1 ∨ v = p.2)))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx1 hx2
    obtain ⟨a, _, rfl⟩ := hx1
    obtain ⟨⟨a', s'⟩, hp, h⟩ := hx2
    rw [Finset.mem_product, Finset.mem_compl] at hp
    have h1 := congrFun h a'
    have h2 := congrFun h s'
    simp at h1 h2
    exact hp.2 (h2.trans h1.symm ▸ hp.1)
  have d13 : Disjoint (T.image (fun a : Fin 21 => (fun v : Fin 21 => decide (v = a))))
      ((Finset.univ : Finset (Fin 21)).image (fun t : Fin 21 => (fun v : Fin 21 => decide (v ∉ L t)))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx1 hx2
    obtain ⟨a, _, rfl⟩ := hx1
    obtain ⟨t, _, h⟩ := hx2
    have hsub : (L t)ᶜ ⊆ {a} := by
      intro v hv
      rw [Finset.mem_compl] at hv
      have := congrFun h v
      simp [hv] at this
      rw [Finset.mem_singleton]
      exact this
    have := Finset.card_le_card hsub
    have := hco t
    rw [Finset.card_singleton] at *
    omega
  have d23 : Disjoint ((T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => (fun v : Fin 21 => decide (v = p.1 ∨ v = p.2))))
      ((Finset.univ : Finset (Fin 21)).image (fun t : Fin 21 => (fun v : Fin 21 => decide (v ∉ L t)))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx1 hx2
    obtain ⟨⟨a, s⟩, _, rfl⟩ := hx1
    obtain ⟨t, _, h⟩ := hx2
    have hsub : (L t)ᶜ ⊆ {a, s} := by
      intro v hv
      rw [Finset.mem_compl] at hv
      have := congrFun h v
      simp [hv] at this
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have h1 := Finset.card_le_card hsub
    have h2 := hco t
    have h3 : ({a, s} : Finset (Fin 21)).card ≤ 2 := Finset.card_le_two
    omega
  refine ⟨?_, hB, ?_, ?_, ?_, ?_⟩
  · intro f hmono t
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        rw [h _ ⟨a, (Finset.mem_inter.mp ha).1, by simp⟩, decide_eq_true_eq]
        exact ⟨a, (Finset.mem_inter.mp ha).2, by simp⟩
      · intro a ha s hs
        rw [h _ ⟨a, (Finset.mem_sdiff.mp ha).1, by simp⟩, decide_eq_true_eq]
        exact ⟨s, (Finset.mem_sdiff.mp hs).1, by simp⟩
      · obtain ⟨v, hvT, hvL⟩ := hB t
        rw [h _ ⟨v, hvT, by simp [hvL]⟩, decide_eq_false_iff_not]
        rintro ⟨w, hw, hw2⟩
        simp at hw2
        exact hw2 hw
    · rintro ⟨h1, h2, h3⟩ x ⟨a, haT, hxa⟩
      by_cases hor : ∃ v ∈ L t, x v = true
      · rw [decide_eq_true hor]
        obtain ⟨s, hsL, hxs⟩ := hor
        by_cases haL : a ∈ L t
        · refine hmono _ x ?_ (h1 a (Finset.mem_inter.mpr ⟨haT, haL⟩))
          intro v hv
          simp at hv
          rw [hv]
          exact hxa
        · by_cases hsT : s ∈ T
          · refine hmono _ x ?_ (h1 s (Finset.mem_inter.mpr ⟨hsT, hsL⟩))
            intro v hv
            simp at hv
            rw [hv]
            exact hxs
          · refine hmono _ x ?_ (h2 a (Finset.mem_sdiff.mpr ⟨haT, haL⟩) s (Finset.mem_sdiff.mpr ⟨hsL, hsT⟩))
            intro v hv
            simp at hv
            rcases hv with hv | hv
            · rw [hv]
              exact hxa
            · rw [hv]
              exact hxs
      · rw [decide_eq_false hor]
        by_contra hfx
        have hfx' : f x = true := by simpa using hfx
        have hco' := hmono x (fun v : Fin 21 => decide (v ∉ L t)) (fun v hv => by
          show decide (v ∉ L t) = true
          rw [decide_eq_true_eq]
          intro hvL
          exact hor ⟨v, hvL, hv⟩) hfx'
        rw [h3] at hco'
        exact absurd hco' (by simp)
  · refine (congrArg Finset.card (Finset.ext fun x => ?_)).trans c1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact m1 x
  · refine (congrArg Finset.card (Finset.ext fun x => ?_)).trans c2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact m2 x
  · refine (congrArg Finset.card (Finset.ext fun x => ?_)).trans c3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact m3 x
  · have hcard : ((T.image (fun a : Fin 21 => (fun v : Fin 21 => decide (v = a)))) ∪
        ((T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => (fun v : Fin 21 => decide (v = p.1 ∨ v = p.2)))) ∪
        ((Finset.univ : Finset (Fin 21)).image (fun t : Fin 21 => (fun v : Fin 21 => decide (v ∉ L t))))).card = 78 := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d13, d23⟩),
        Finset.card_union_of_disjoint d12, c1, c2, c3]
    refine (congrArg Finset.card (Finset.ext fun x => ?_)).trans hcard
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [← m1 x, ← m2 x, ← m3 x]
    constructor
    · rintro ⟨t, h | h | h⟩
      · exact Or.inl (Or.inl ⟨t, h⟩)
      · exact Or.inl (Or.inr ⟨t, h⟩)
      · exact Or.inr ⟨t, h⟩
    · rintro ((⟨t, h⟩ | ⟨t, h⟩) | ⟨t, h⟩)
      · exact ⟨t, Or.inl h⟩
      · exact ⟨t, Or.inr (Or.inl h)⟩
      · exact ⟨t, Or.inr (Or.inr h)⟩

end PEqualNP.Outside.L_meta_1560_aux

theorem PEqualNP.Outside.L_meta_1560 : ∀ L : Fin 21 → Finset (Fin 21), (∀ t : Fin 21, L t = {t, t + 1, t + 4, t + 14, t + 16}) →
    ∀ T : Finset (Fin 21), T.card = 3 → (∀ t : Fin 21, ¬ T ⊆ L t) →
    (∀ f : (Fin 21 → Bool) → Bool,
      (∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) → f x = true → f y = true) →
      ∀ t : Fin 21,
        ((∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) → f x = decide (∃ v ∈ L t, x v = true)) ↔
          ((∀ a ∈ T ∩ L t, f (fun v : Fin 21 => decide (v = a)) = true) ∧
           (∀ a ∈ T \ L t, ∀ s ∈ L t \ T, f (fun v : Fin 21 => decide (v = a ∨ v = s)) = true) ∧
           f (fun v : Fin 21 => decide (v ∉ L t)) = false))) ∧
    (∀ t : Fin 21, ∃ v ∈ T, v ∉ L t) ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a)))).card = 3 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ L t, ∃ s ∈ L t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s)))).card = 54 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 21 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, (∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a))) ∨
      (∃ a ∈ T \ L t, ∃ s ∈ L t \ T, x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ∨
      x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 78 := by
  intro L hL T hT hTL
  exact PEqualNP.Outside.L_meta_1560_aux.main L hL T hT hTL
