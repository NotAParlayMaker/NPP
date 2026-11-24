import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1560

def line (t : Fin 21) : Finset (Fin 21) := {t, t + 1, t + 4, t + 14, t + 16}

lemma through : ∀ s a : Fin 21, s ≠ a → ∃ t : Fin 21, s ∈ line t ∧ a ∉ line t := by
  unfold line
  decide

lemma line_inj : ∀ t t' : Fin 21, line t = line t' → t = t' := by
  unfold line
  decide

lemma outside3 : ∀ t : Fin 21, t + 2 ∉ line t ∧ t + 3 ∉ line t ∧ t + 5 ∉ line t ∧
    t + 2 ≠ t + 3 ∧ t + 3 ≠ t + 5 ∧ t + 2 ≠ t + 5 := by
  unfold line
  decide

lemma self_mem (t : Fin 21) : t ∈ line t := by
  simp [line]

def e1 (a : Fin 21) : Fin 21 → Bool := fun v => decide (v = a)

def e2 (a s : Fin 21) : Fin 21 → Bool := fun v => decide (v = a ∨ v = s)

def ec (t : Fin 21) : Fin 21 → Bool := fun v => decide (v ∉ line t)

lemma iff_part (T : Finset (Fin 21)) (hTn : ∀ t : Fin 21, ¬ T ⊆ line t)
    (f : (Fin 21 → Bool) → Bool)
    (hmono : ∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) →
      f x = true → f y = true) (t : Fin 21) :
    ((∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) → f x = decide (∃ v ∈ line t, x v = true)) ↔
      ((∀ a ∈ T ∩ line t, f (fun v : Fin 21 => decide (v = a)) = true) ∧
       (∀ a ∈ T \ line t, ∀ s ∈ line t \ T, f (fun v : Fin 21 => decide (v = a ∨ v = s)) = true) ∧
       f (fun v : Fin 21 => decide (v ∉ line t)) = false)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rw [h _ ⟨a, (Finset.mem_inter.mp ha).1, by simp⟩]
      simp only [decide_eq_true_eq]
      exact ⟨a, (Finset.mem_inter.mp ha).2, by simp⟩
    · intro a ha s hs
      rw [h _ ⟨a, (Finset.mem_sdiff.mp ha).1, by simp⟩]
      simp only [decide_eq_true_eq]
      exact ⟨s, (Finset.mem_sdiff.mp hs).1, by simp⟩
    · obtain ⟨v, hvT, hvL⟩ := Finset.not_subset.mp (hTn t)
      rw [h _ ⟨v, hvT, by simp [hvL]⟩]
      simp
  · rintro ⟨h1, h2, h3⟩ x ⟨a, haT, hxa⟩
    by_cases hx : ∃ v ∈ line t, x v = true
    · rw [decide_eq_true hx]
      obtain ⟨s, hsL, hxs⟩ := hx
      by_cases haL : a ∈ line t
      · exact hmono _ x (fun v hv => by simp at hv; subst hv; exact hxa)
          (h1 a (Finset.mem_inter.mpr ⟨haT, haL⟩))
      by_cases hsT : s ∈ T
      · exact hmono _ x (fun v hv => by simp at hv; subst hv; exact hxs)
          (h1 s (Finset.mem_inter.mpr ⟨hsT, hsL⟩))
      · exact hmono _ x (fun v hv => by
            simp only [decide_eq_true_eq] at hv
            rcases hv with rfl | rfl
            · exact hxa
            · exact hxs)
          (h2 a (Finset.mem_sdiff.mpr ⟨haT, haL⟩) s (Finset.mem_sdiff.mpr ⟨hsL, hsT⟩))
    · rw [decide_eq_false hx]
      cases hfx : f x
      · rfl
      · have := hmono x (fun v : Fin 21 => decide (v ∉ line t))
          (fun v hv => decide_eq_true (fun hvL => hx ⟨v, hvL, hv⟩)) hfx
        rw [h3] at this
        exact absurd this (by decide)

lemma e1_inj : Function.Injective e1 := by
  intro a b h
  have := congrFun h a
  simp [e1] at this
  exact this

lemma e2_injOn (T : Finset (Fin 21)) :
    Set.InjOn (fun p : Fin 21 × Fin 21 => e2 p.1 p.2) ↑(T ×ˢ Tᶜ) := by
  rintro ⟨a, s⟩ hp ⟨a', s'⟩ hp' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_compl] at hp hp'
  simp only at h
  have ha := congrFun h a
  have hs := congrFun h s
  simp only [e2, true_or, decide_true, or_true] at ha hs
  have ha' : a = a' ∨ a = s' := by simpa using ha.symm
  have hs' : s = a' ∨ s = s' := by simpa using hs.symm
  have h1 : a = a' := by
    rcases ha' with h | h
    · exact h
    · exact absurd (h ▸ hp.1) hp'.2
  have h2 : s = s' := by
    rcases hs' with h | h
    · exact absurd (h ▸ hp'.1) hp.2
    · exact h
  rw [h1, h2]

lemma ec_inj : Function.Injective ec := by
  intro t t' h
  apply line_inj
  ext v
  have := congrFun h v
  simp only [ec, decide_eq_decide] at this
  tauto

lemma set1 (T : Finset (Fin 21)) :
    Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ line t,
      x = (fun v : Fin 21 => decide (v = a))) = T.image e1 := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨t, a, ⟨haT, _⟩, rfl⟩
    exact ⟨a, haT, rfl⟩
  · rintro ⟨a, haT, rfl⟩
    exact ⟨a, a, ⟨haT, self_mem a⟩, rfl⟩

lemma set2 (T : Finset (Fin 21)) :
    Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ line t, ∃ s ∈ line t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s))) =
      (T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => e2 p.1 p.2) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_sdiff,
    Finset.mem_product, Finset.mem_compl, Prod.exists]
  constructor
  · rintro ⟨t, a, ⟨haT, _⟩, s, ⟨_, hsT⟩, rfl⟩
    exact ⟨a, s, ⟨haT, hsT⟩, rfl⟩
  · rintro ⟨a, s, ⟨haT, hsT⟩, rfl⟩
    have hsa : s ≠ a := fun h => hsT (h ▸ haT)
    obtain ⟨t, hst, hat⟩ := through s a hsa
    exact ⟨t, a, ⟨haT, hat⟩, s, ⟨hst, hsT⟩, rfl⟩

lemma set3 :
    Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21,
      x = (fun v : Fin 21 => decide (v ∉ line t))) = Finset.univ.image ec := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

lemma main : ∀ L : Fin 21 → Finset (Fin 21), (∀ t : Fin 21, L t = {t, t + 1, t + 4, t + 14, t + 16}) →
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
  intro L hL T hT3 hTn
  obtain rfl : L = line := funext hL
  have c1 : (T.image e1).card = 3 := by rw [Finset.card_image_of_injective _ e1_inj, hT3]
  have c2 : ((T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => e2 p.1 p.2)).card = 54 := by
    rw [Finset.card_image_of_injOn (e2_injOn T), Finset.card_product, Finset.card_compl, hT3]
    simp
  have c3 : (Finset.univ.image ec).card = 21 := by
    rw [Finset.card_image_of_injective _ ec_inj]
    simp
  refine ⟨fun f hmono t => iff_part T hTn f hmono t,
    fun t => Finset.not_subset.mp (hTn t), by rw [set1, c1], by rw [set2, c2],
    by rw [set3, c3], ?_⟩
  have hsplit : Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21,
      (∃ a ∈ T ∩ line t, x = (fun v : Fin 21 => decide (v = a))) ∨
      (∃ a ∈ T \ line t, ∃ s ∈ line t \ T, x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ∨
      x = (fun v : Fin 21 => decide (v ∉ line t))) =
      (T.image e1 ∪ (T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => e2 p.1 p.2)) ∪
        Finset.univ.image ec := by
    rw [← set1, ← set2, ← set3, ← Finset.filter_or, ← Finset.filter_or]
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨t, h | h | h⟩
      · exact Or.inl (Or.inl ⟨t, h⟩)
      · exact Or.inl (Or.inr ⟨t, h⟩)
      · exact Or.inr ⟨t, h⟩
    · rintro ((⟨t, h⟩ | ⟨t, h⟩) | ⟨t, h⟩)
      · exact ⟨t, Or.inl h⟩
      · exact ⟨t, Or.inr (Or.inl h)⟩
      · exact ⟨t, Or.inr (Or.inr h)⟩
  have d12 : Disjoint (T.image e1) ((T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => e2 p.1 p.2)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨a, haT, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨⟨a', s⟩, hp, hx⟩ := Finset.mem_image.mp hx2
    simp only [Finset.mem_product, Finset.mem_compl] at hp
    have := congrFun hx s
    simp only [e1, e2, or_true, decide_true] at this
    have hsa : s = a := by simpa using this.symm
    exact hp.2 (hsa ▸ haT)
  have d3 : Disjoint (T.image e1 ∪ (T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => e2 p.1 p.2))
      (Finset.univ.image ec) := by
    rw [Finset.disjoint_left]
    intro x hx hx3
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx3
    obtain ⟨hu, hv, hw, huv, hvw, huw⟩ := outside3 t
    have tu : ec t (t + 2) = true := by simp [ec, hu]
    have tv : ec t (t + 3) = true := by simp [ec, hv]
    have tw : ec t (t + 5) = true := by simp [ec, hw]
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
      rw [← ha] at tu tv
      simp only [e1, decide_eq_true_eq] at tu tv
      exact huv (tu.trans tv.symm)
    · obtain ⟨⟨a, s⟩, _, ha⟩ := Finset.mem_image.mp hx
      rw [← ha] at tu tv tw
      simp only [e2, decide_eq_true_eq] at tu tv tw
      rcases tu with tu | tu <;> rcases tv with tv | tv
      · exact huv (tu.trans tv.symm)
      · rcases tw with tw | tw
        · exact huw (tu.trans tw.symm)
        · exact hvw (tv.trans tw.symm)
      · rcases tw with tw | tw
        · exact hvw (tv.trans tw.symm)
        · exact huw (tu.trans tw.symm)
      · exact huv (tu.trans tv.symm)
  rw [hsplit, Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d12, c1, c2, c3]

end PEqualNP.Outside.L_meta_1560

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
      x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 78 :=
  PEqualNP.Outside.L_meta_1560.main
