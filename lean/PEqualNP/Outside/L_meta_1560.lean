import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1560

abbrev onLine (t v : Fin 21) : Prop :=
  v = t ∨ v = t + 1 ∨ v = t + 4 ∨ v = t + 14 ∨ v = t + 16

theorem mem_iff_onLine (t v : Fin 21) :
    v ∈ ({t, t + 1, t + 4, t + 14, t + 16} : Finset (Fin 21)) ↔ onLine t v := by
  simp [onLine]

theorem off_line : ∀ a s : Fin 21, a ≠ s → ¬ onLine s a ∨ ¬ onLine (s + 20) a := by
  decide

theorem on_line_shift : ∀ s : Fin 21, onLine (s + 20) s := by
  decide

theorem three_off : ∀ t : Fin 21,
    ¬ onLine t (t + 2) ∧ ¬ onLine t (t + 3) ∧ ¬ onLine t (t + 5) ∧
      t + 2 ≠ t + 3 ∧ t + 2 ≠ t + 5 ∧ t + 3 ≠ t + 5 := by
  decide

theorem line_inj : ∀ t t' : Fin 21, onLine t' t → onLine t' (t + 1) → t = t' := by
  decide

def pt (a : Fin 21) : Fin 21 → Bool := fun v => decide (v = a)
def pr (a s : Fin 21) : Fin 21 → Bool := fun v => decide (v = a ∨ v = s)
def co (L : Fin 21 → Finset (Fin 21)) (t : Fin 21) : Fin 21 → Bool := fun v => decide (v ∉ L t)

theorem main_iff (L : Fin 21 → Finset (Fin 21)) (T : Finset (Fin 21)) (t : Fin 21)
    (hT : ∃ v ∈ T, v ∉ L t) (f : (Fin 21 → Bool) → Bool)
    (hf : ∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) →
      f x = true → f y = true) :
    ((∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) → f x = decide (∃ v ∈ L t, x v = true)) ↔
      ((∀ a ∈ T ∩ L t, f (fun v : Fin 21 => decide (v = a)) = true) ∧
       (∀ a ∈ T \ L t, ∀ s ∈ L t \ T, f (fun v : Fin 21 => decide (v = a ∨ v = s)) = true) ∧
       f (fun v : Fin 21 => decide (v ∉ L t)) = false)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_inter] at ha
      rw [h _ ⟨a, ha.1, by simp⟩]
      simp only [decide_eq_true_eq]
      exact ⟨a, ha.2, by simp⟩
    · intro a ha s hs
      rw [Finset.mem_sdiff] at ha hs
      rw [h _ ⟨a, ha.1, by simp⟩]
      simp only [decide_eq_true_eq]
      exact ⟨s, hs.1, by simp⟩
    · obtain ⟨v, hvT, hvL⟩ := hT
      rw [h _ ⟨v, hvT, by simp [hvL]⟩]
      simp
  · rintro ⟨h1, h2, h3⟩ x ⟨a, haT, hax⟩
    by_cases hx : ∃ v ∈ L t, x v = true
    · rw [decide_eq_true hx]
      obtain ⟨s, hsL, hsx⟩ := hx
      by_cases haL : a ∈ L t
      · refine hf _ _ ?_ (h1 a (Finset.mem_inter.2 ⟨haT, haL⟩))
        intro v hv
        simp only [decide_eq_true_eq] at hv
        subst hv
        exact hax
      · by_cases hsT : s ∈ T
        · refine hf _ _ ?_ (h1 s (Finset.mem_inter.2 ⟨hsT, hsL⟩))
          intro v hv
          simp only [decide_eq_true_eq] at hv
          subst hv
          exact hsx
        · refine hf _ _ ?_
            (h2 a (Finset.mem_sdiff.2 ⟨haT, haL⟩) s (Finset.mem_sdiff.2 ⟨hsL, hsT⟩))
          intro v hv
          simp only [decide_eq_true_eq] at hv
          rcases hv with rfl | rfl
          · exact hax
          · exact hsx
    · rw [decide_eq_false hx]
      by_contra hfx
      have hle : ∀ v : Fin 21, x v = true → (fun v : Fin 21 => decide (v ∉ L t)) v = true := by
        intro v hv
        simp only [decide_eq_true_eq]
        intro hvL
        exact hx ⟨v, hvL, hv⟩
      have := hf _ _ hle (by simpa using hfx)
      rw [h3] at this
      exact absurd this (by simp)

theorem pt_inj : Function.Injective pt := by
  intro a b h
  have := congrFun h a
  simp [pt] at this
  exact this

theorem pr_injOn (T : Finset (Fin 21)) :
    Set.InjOn (fun p : Fin 21 × Fin 21 => pr p.1 p.2) ↑(T ×ˢ Tᶜ) := by
  rintro ⟨a, s⟩ hp ⟨a', s'⟩ hp' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_compl] at hp hp'
  have ha := congrFun h a
  have hs := congrFun h s
  simp only [pr, true_or, decide_true] at ha hs
  simp only [or_true, decide_true] at hs
  have ha' : a = a' ∨ a = s' := by simpa using ha.symm
  have hs' : s = a' ∨ s = s' := by simpa using hs.symm
  have e1 : a = a' := by
    rcases ha' with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hp.1) hp'.2
  have e2 : s = s' := by
    rcases hs' with h2 | h2
    · exact absurd (h2 ▸ hp'.1) hp.2
    · exact h2
  rw [e1, e2]

theorem co_inj (L : Fin 21 → Finset (Fin 21))
    (hLm : ∀ t v, v ∈ L t ↔ onLine t v) : Function.Injective (co L) := by
  intro t t' h
  have h1 := congrFun h t
  have h2 := congrFun h (t + 1)
  simp only [co, decide_eq_decide, not_iff_not] at h1 h2
  have m1 : t ∈ L t' := h1.1 ((hLm t t).2 (Or.inl rfl))
  have m2 : t + 1 ∈ L t' := h2.1 ((hLm t (t + 1)).2 (Or.inr (Or.inl rfl)))
  exact line_inj t t' ((hLm t' t).1 m1) ((hLm t' (t + 1)).1 m2)

theorem pt_ne_pr (T : Finset (Fin 21)) (a a' s : Fin 21) (ha' : a' ∈ T) (hs : s ∉ T) :
    pt a ≠ pr a' s := by
  intro h
  have h1 := congrFun h a'
  have h2 := congrFun h s
  simp only [pt, pr, true_or, or_true, decide_true, decide_eq_true_eq] at h1 h2
  exact hs (h2 ▸ h1 ▸ ha')

theorem pt_ne_co (L : Fin 21 → Finset (Fin 21)) (hLm : ∀ t v, v ∈ L t ↔ onLine t v)
    (a t : Fin 21) : pt a ≠ co L t := by
  intro h
  obtain ⟨o2, o3, -, d23, -, -⟩ := three_off t
  have h2 := congrFun h (t + 2)
  have h3 := congrFun h (t + 3)
  simp only [pt, co, decide_eq_decide] at h2 h3
  have x2 : t + 2 = a := h2.2 (fun m => o2 ((hLm t _).1 m))
  have x3 : t + 3 = a := h3.2 (fun m => o3 ((hLm t _).1 m))
  exact d23 (x2.trans x3.symm)

theorem pr_ne_co (L : Fin 21 → Finset (Fin 21)) (hLm : ∀ t v, v ∈ L t ↔ onLine t v)
    (a s t : Fin 21) : pr a s ≠ co L t := by
  intro h
  obtain ⟨o2, o3, o5, d23, d25, d35⟩ := three_off t
  have h2 := congrFun h (t + 2)
  have h3 := congrFun h (t + 3)
  have h5 := congrFun h (t + 5)
  simp only [pr, co, decide_eq_decide] at h2 h3 h5
  have x2 := h2.2 (fun m => o2 ((hLm t _).1 m))
  have x3 := h3.2 (fun m => o3 ((hLm t _).1 m))
  have x5 := h5.2 (fun m => o5 ((hLm t _).1 m))
  rcases x2 with x2 | x2 <;> rcases x3 with x3 | x3 <;> rcases x5 with x5 | x5
  · exact d23 (x2.trans x3.symm)
  · exact d23 (x2.trans x3.symm)
  · exact d25 (x2.trans x5.symm)
  · exact d35 (x3.trans x5.symm)
  · exact d35 (x3.trans x5.symm)
  · exact d25 (x2.trans x5.symm)
  · exact d23 (x2.trans x3.symm)
  · exact d23 (x2.trans x3.symm)

end PEqualNP.Outside.L_meta_1560

open PEqualNP.Outside.L_meta_1560 in
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
  intro L hL T hT3 hTn
  have hLm : ∀ t v, v ∈ L t ↔ onLine t v := fun t v => by rw [hL]; exact mem_iff_onLine t v
  have hoff : ∀ t, ∃ v ∈ T, v ∉ L t := fun t => Finset.not_subset.1 (hTn t)
  have e1 : Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ L t,
      x = (fun v : Fin 21 => decide (v = a))) = T.image pt := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_inter]
    constructor
    · rintro ⟨t, a, ⟨haT, -⟩, rfl⟩
      exact ⟨a, haT, rfl⟩
    · rintro ⟨a, haT, rfl⟩
      exact ⟨a, a, ⟨haT, (hLm a a).2 (Or.inl rfl)⟩, rfl⟩
  have e2 : Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ L t,
      ∃ s ∈ L t \ T, x = (fun v : Fin 21 => decide (v = a ∨ v = s))) =
      (T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => pr p.1 p.2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_product, Finset.mem_compl, Finset.mem_sdiff, Prod.exists]
    constructor
    · rintro ⟨t, a, ⟨haT, -⟩, s, ⟨-, hsT⟩, rfl⟩
      exact ⟨a, s, ⟨haT, hsT⟩, rfl⟩
    · rintro ⟨a, s, ⟨haT, hsT⟩, rfl⟩
      have hne : a ≠ s := fun h => hsT (h ▸ haT)
      rcases off_line a s hne with h | h
      · exact ⟨s, a, ⟨haT, fun m => h ((hLm s a).1 m)⟩, s,
          ⟨(hLm s s).2 (Or.inl rfl), hsT⟩, rfl⟩
      · exact ⟨s + 20, a, ⟨haT, fun m => h ((hLm _ a).1 m)⟩, s,
          ⟨(hLm _ s).2 (on_line_shift s), hsT⟩, rfl⟩
  have e3 : Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21,
      x = (fun v : Fin 21 => decide (v ∉ L t))) = Finset.univ.image (co L) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
  have c1 : (T.image pt).card = 3 := by
    rw [Finset.card_image_of_injective _ pt_inj, hT3]
  have c2 : ((T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => pr p.1 p.2)).card = 54 := by
    rw [Finset.card_image_of_injOn (pr_injOn T), Finset.card_product, Finset.card_compl, hT3]
    simp
  have c3 : (Finset.univ.image (co L)).card = 21 := by
    rw [Finset.card_image_of_injective _ (co_inj L hLm)]
    simp
  have e4 : Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21,
      (∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a))) ∨
      (∃ a ∈ T \ L t, ∃ s ∈ L t \ T, x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ∨
      x = (fun v : Fin 21 => decide (v ∉ L t))) =
      (T.image pt ∪ (T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => pr p.1 p.2)) ∪
        Finset.univ.image (co L) := by
    rw [← e1, ← e2, ← e3]
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨t, h | h | h⟩
      · exact Or.inl (Or.inl ⟨t, h⟩)
      · exact Or.inl (Or.inr ⟨t, h⟩)
      · exact Or.inr ⟨t, h⟩
    · rintro ((⟨t, h⟩ | ⟨t, h⟩) | ⟨t, h⟩)
      · exact ⟨t, Or.inl h⟩
      · exact ⟨t, Or.inr (Or.inl h)⟩
      · exact ⟨t, Or.inr (Or.inr h)⟩
  have d12 : Disjoint (T.image pt) ((T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => pr p.1 p.2)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx1
    obtain ⟨⟨a', s⟩, hp, he⟩ := Finset.mem_image.1 hx2
    simp only [Finset.mem_product, Finset.mem_compl] at hp
    exact pt_ne_pr T a a' s hp.1 hp.2 he.symm
  have d3 : Disjoint (T.image pt ∪ (T ×ˢ Tᶜ).image (fun p : Fin 21 × Fin 21 => pr p.1 p.2))
      (Finset.univ.image (co L)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hx2
    rcases Finset.mem_union.1 hx1 with h | h
    · obtain ⟨a, -, he⟩ := Finset.mem_image.1 h
      exact pt_ne_co L hLm a t he
    · obtain ⟨⟨a, s⟩, -, he⟩ := Finset.mem_image.1 h
      exact pr_ne_co L hLm a s t he
  refine ⟨fun f hf t => main_iff L T t (hoff t) f hf, hoff, ?_, ?_, ?_, ?_⟩
  · rw [e1, c1]
  · rw [e2, c2]
  · rw [e3, c3]
  · rw [e4, Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d12, c1, c2, c3]
