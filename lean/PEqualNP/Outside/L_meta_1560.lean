import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1560

/-- The line through `t` in the plane of order 4 on `Fin 21`. -/
def lineSet (t : Fin 21) : Finset (Fin 21) := {t, t + 1, t + 4, t + 14, t + 16}

lemma lineSet_card : ∀ t : Fin 21, (lineSet t).card = 5 := by decide

lemma lineSet_inj : Function.Injective lineSet := by decide

lemma pair_unique : ∀ p q : Fin 21, p ≠ q →
    ∃ t : Fin 21, p ∈ lineSet t ∧ q ∈ lineSet t ∧
      ∀ t' : Fin 21, p ∈ lineSet t' → q ∈ lineSet t' → t' = t := by decide

lemma lines_through : ∀ p : Fin 21,
    (Finset.univ.filter (fun t : Fin 21 => p ∈ lineSet t)).card = 5 := by decide

/-- The indicator of a single point. -/
def one (a : Fin 21) : Fin 21 → Bool := fun v => decide (v = a)

/-- The indicator of a two-element set. -/
def two (a s : Fin 21) : Fin 21 → Bool := fun v => decide (v = a ∨ v = s)

/-- The indicator of the complement of a line. -/
def zero (t : Fin 21) : Fin 21 → Bool := fun v => decide (v ∉ lineSet t)

lemma one_eq_true {a v : Fin 21} : one a v = true ↔ v = a := by simp [one]
lemma two_eq_true {a s v : Fin 21} : two a s v = true ↔ v = a ∨ v = s := by simp [two]
lemma zero_eq_true {t v : Fin 21} : zero t v = true ↔ v ∉ lineSet t := by simp [zero]

lemma decide_of {p : Prop} [Decidable p] (h : p) : decide p = true := by simp [h]
lemma decide_of_not {p : Prop} [Decidable p] (h : ¬p) : decide p = false := by simp [h]

/-- A point of `T` outside a line, from `T` not being contained in it. -/
lemma sub_not_subset (T : Finset (Fin 21)) (t : Fin 21) (h : ¬ T ⊆ lineSet t) :
    ∃ v ∈ T, v ∉ lineSet t := by
  simpa [Finset.subset_iff] using h

/-- Through a point there is a line that avoids another point. -/
lemma line_avoiding : ∀ a s : Fin 21, a ≠ s → ∃ t : Fin 21, a ∉ lineSet t ∧ s ∈ lineSet t := by
  decide

/-- The three test families are forced by the monotone function. -/
lemma mspec_forward {f : (Fin 21 → Bool) → Bool} {t : Fin 21} {T : Finset (Fin 21)}
    (hne : ∃ v ∈ T, v ∉ lineSet t)
    (h : ∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) →
      f x = decide (∃ v ∈ lineSet t, x v = true)) :
    (∀ a ∈ T ∩ lineSet t, f (one a) = true) ∧
    (∀ a ∈ T \ lineSet t, ∀ s ∈ lineSet t \ T, f (two a s) = true) ∧
    f (zero t) = false := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    have haT : a ∈ T := (Finset.mem_inter.1 ha).1
    have haL : a ∈ lineSet t := (Finset.mem_inter.1 ha).2
    have hP : ∃ v ∈ lineSet t, (one a) v = true := ⟨a, haL, one_eq_true.2 rfl⟩
    have hh := h (one a) ⟨a, haT, one_eq_true.2 rfl⟩
    rw [decide_of hP] at hh
    exact hh
  · intro a ha s hs
    have haT : a ∈ T := (Finset.mem_sdiff.1 ha).1
    have hsL : s ∈ lineSet t := (Finset.mem_sdiff.1 hs).1
    have hP : ∃ v ∈ lineSet t, (two a s) v = true := ⟨s, hsL, two_eq_true.2 (Or.inr rfl)⟩
    have hh := h (two a s) ⟨a, haT, two_eq_true.2 (Or.inl rfl)⟩
    rw [decide_of hP] at hh
    exact hh
  · obtain ⟨v, hvT, hvL⟩ := hne
    have hP : ¬ ∃ w ∈ lineSet t, (zero t) w = true := by
      rintro ⟨w, hwL, hw⟩
      exact (zero_eq_true.1 hw) hwL
    have hh := h (zero t) ⟨v, hvT, zero_eq_true.2 hvL⟩
    rw [decide_of_not hP] at hh
    exact hh

/-- The three test families imply the monotone function on the anchored domain. -/
lemma mspec_backward {f : (Fin 21 → Bool) → Bool}
    (hm : ∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) →
      f x = true → f y = true)
    {t : Fin 21} {T : Finset (Fin 21)}
    (h1 : ∀ a ∈ T ∩ lineSet t, f (one a) = true)
    (h2 : ∀ a ∈ T \ lineSet t, ∀ s ∈ lineSet t \ T, f (two a s) = true)
    (h3 : f (zero t) = false) :
    ∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) →
      f x = decide (∃ v ∈ lineSet t, x v = true) := by
  intro x hx
  by_cases hP : ∃ v ∈ lineSet t, x v = true
  · have hfx : f x = true := by
      by_cases hc : ∃ a, a ∈ T ∩ lineSet t ∧ x a = true
      · obtain ⟨a, ha, hax⟩ := hc
        refine hm (one a) x ?_ (h1 a ha)
        intro v hv
        rw [one_eq_true.1 hv]
        exact hax
      · obtain ⟨a, haT, hax⟩ := hx
        have haL : a ∉ lineSet t := by
          intro hL
          exact hc ⟨a, Finset.mem_inter.2 ⟨haT, hL⟩, hax⟩
        obtain ⟨s, hsL, hsx⟩ := hP
        have hsT : s ∉ T := by
          intro hT
          exact hc ⟨s, Finset.mem_inter.2 ⟨hT, hsL⟩, hsx⟩
        refine hm (two a s) x ?_
          (h2 a (Finset.mem_sdiff.2 ⟨haT, haL⟩) s (Finset.mem_sdiff.2 ⟨hsL, hsT⟩))
        intro v hv
        rcases two_eq_true.1 hv with h | h
        · rw [h]; exact hax
        · rw [h]; exact hsx
    rw [hfx, decide_of hP]
  · have hfx : f x = false := by
      have hne : f x ≠ true := by
        intro htrue
        have hle : ∀ v : Fin 21, x v = true → (zero t) v = true := by
          intro v hv
          exact zero_eq_true.2 (fun hvL => hP ⟨v, hvL, hv⟩)
        have hcontra := hm x (zero t) hle htrue
        rw [h3] at hcontra
        exact Bool.false_ne_true hcontra
      cases hb : f x with
      | false => rfl
      | true => exact absurd hb hne
    rw [hfx, decide_of_not hP]

/-- The indicators of points of `T` on a line. -/
def anchorSet (T : Finset (Fin 21)) : Finset (Fin 21 → Bool) :=
  Finset.univ.filter (fun x => ∃ t : Fin 21, ∃ a ∈ T ∩ lineSet t, x = one a)

/-- The indicators of a point of `T` off a line and a point of the line off `T`. -/
def pairSet (T : Finset (Fin 21)) : Finset (Fin 21 → Bool) :=
  Finset.univ.filter (fun x => ∃ t : Fin 21, ∃ a ∈ T \ lineSet t,
    ∃ s ∈ lineSet t \ T, x = two a s)

/-- The indicators of the complements of the lines. -/
def zeroSet : Finset (Fin 21 → Bool) :=
  Finset.univ.filter (fun x => ∃ t : Fin 21, x = zero t)

/-- The union of the three test families. -/
def allSet (T : Finset (Fin 21)) : Finset (Fin 21 → Bool) :=
  Finset.univ.filter (fun x => ∃ t : Fin 21,
    (∃ a ∈ T ∩ lineSet t, x = one a) ∨
    (∃ a ∈ T \ lineSet t, ∃ s ∈ lineSet t \ T, x = two a s) ∨
    x = zero t)

/-- The support of a Boolean function. -/
def supp (x : Fin 21 → Bool) : Finset (Fin 21) :=
  Finset.univ.filter (fun v => x v = true)

lemma supp_one (a : Fin 21) : supp (one a) = {a} := by
  ext v; simp [supp, one]

lemma supp_two (a s : Fin 21) : supp (two a s) = {a, s} := by
  ext v; simp [supp, two]

lemma supp_zero (t : Fin 21) : supp (zero t) = Finset.univ \ lineSet t := by
  ext v; simp [supp, zero]

lemma supp_zero_card (t : Fin 21) : (supp (zero t)).card = 16 := by
  rw [supp_zero, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have := lineSet_card t
  omega

lemma one_inj : Function.Injective one := by
  intro a a' h
  have h2 : one a a = one a' a := congrFun h a
  have hl : one a a = true := one_eq_true.2 rfl
  rw [hl] at h2
  exact one_eq_true.1 h2.symm

lemma zero_inj : Function.Injective zero := by
  intro t t' h
  apply lineSet_inj
  ext v
  have hv := congrFun h v
  simp only [zero] at hv
  constructor
  · intro hv1
    by_contra hv2
    rw [decide_of_not (by simpa using hv1), decide_of (by simpa using hv2)] at hv
    exact Bool.false_ne_true hv
  · intro hv2
    by_contra hv1
    rw [decide_of (by simpa using hv1), decide_of_not (by simpa using hv2)] at hv
    exact Bool.false_ne_true hv.symm

lemma anchorSet_eq (T : Finset (Fin 21)) : anchorSet T = T.image one := by
  ext x
  constructor
  · intro hx
    simp only [anchorSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨t, a, ha, hxa⟩ := hx
    exact Finset.mem_image.2 ⟨a, (Finset.mem_inter.1 ha).1, hxa.symm⟩
  · intro hx
    obtain ⟨a, haT, hxa⟩ := Finset.mem_image.1 hx
    simp only [anchorSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, a, Finset.mem_inter.2 ⟨haT, by simp [lineSet]⟩, hxa.symm⟩

lemma card_anchor (T : Finset (Fin 21)) (hT : T.card = 3) : (anchorSet T).card = 3 := by
  rw [anchorSet_eq, Finset.card_image_of_injective T one_inj, hT]

lemma pairSet_eq (T : Finset (Fin 21)) :
    pairSet T = (T ×ˢ (Finset.univ \ T)).image (fun p : Fin 21 × Fin 21 => two p.1 p.2) := by
  ext x
  constructor
  · intro hx
    simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨t, a, ha, s, hs, hxa⟩ := hx
    refine Finset.mem_image.2 ⟨(a, s), ?_, hxa.symm⟩
    exact Finset.mem_product.2 ⟨(Finset.mem_sdiff.1 ha).1,
      Finset.mem_sdiff.2 ⟨Finset.mem_univ s, (Finset.mem_sdiff.1 hs).2⟩⟩
  · intro hx
    obtain ⟨p, hp, hxp⟩ := Finset.mem_image.1 hx
    obtain ⟨haT, hsT⟩ := Finset.mem_product.1 hp
    have hsT' : p.2 ∉ T := (Finset.mem_sdiff.1 hsT).2
    have hne : p.1 ≠ p.2 := by
      intro h
      exact hsT' (h ▸ haT)
    obtain ⟨t, ht1, ht2⟩ := line_avoiding p.1 p.2 hne
    simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t, p.1, Finset.mem_sdiff.2 ⟨haT, ht1⟩, p.2, Finset.mem_sdiff.2 ⟨ht2, hsT'⟩, hxp.symm⟩

lemma card_pair (T : Finset (Fin 21)) (hT : T.card = 3) : (pairSet T).card = 54 := by
  rw [pairSet_eq]
  have hinj : Set.InjOn (fun p : Fin 21 × Fin 21 => two p.1 p.2)
      ↑(T ×ˢ (Finset.univ \ T)) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe] at hp hq
    obtain ⟨a, s⟩ := p
    obtain ⟨a', s'⟩ := q
    obtain ⟨haT, hsT⟩ := Finset.mem_product.1 hp
    obtain ⟨ha'T, hs'T⟩ := Finset.mem_product.1 hq
    have hsT' : s ∉ T := (Finset.mem_sdiff.1 hsT).2
    have hs'T' : s' ∉ T := (Finset.mem_sdiff.1 hs'T).2
    have ha : a = a' := by
      have h1 : two a s a = two a' s' a := congrFun hpq a
      have hl : two a s a = true := two_eq_true.2 (Or.inl rfl)
      rw [hl] at h1
      rcases two_eq_true.1 h1.symm with h | h
      · exact h
      · exact absurd (h ▸ haT) hs'T'
    subst ha
    have hs : s = s' := by
      have h2 : two a s s = two a s' s := congrFun hpq s
      have hl : two a s s = true := two_eq_true.2 (Or.inr rfl)
      rw [hl] at h2
      rcases two_eq_true.1 h2.symm with h | h
      · exact absurd (h ▸ haT) hsT'
      · exact h
    subst hs
    rfl
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, hT]
  have hcomp : (Finset.univ \ T).card = 18 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hT]
  rw [hcomp]

lemma zeroSet_eq : zeroSet = Finset.univ.image zero := by
  ext x
  constructor
  · intro hx
    simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨t, hxt⟩ := hx
    exact Finset.mem_image.2 ⟨t, Finset.mem_univ t, hxt.symm⟩
  · intro hx
    obtain ⟨t, -, hxt⟩ := Finset.mem_image.1 hx
    simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t, hxt.symm⟩

lemma card_zero : zeroSet.card = 21 := by
  rw [zeroSet_eq, Finset.card_image_of_injective _ zero_inj, Finset.card_univ,
    Fintype.card_fin]

lemma card_union_disjoint {s t : Finset (Fin 21 → Bool)} (h : Disjoint s t) :
    (s ∪ t).card = s.card + t.card := by
  have hc := Finset.card_union_add_card_inter s t
  rw [Finset.disjoint_iff_inter_eq_empty.1 h] at hc
  simp at hc
  omega

lemma disjoint_anchor_pair (T : Finset (Fin 21)) : Disjoint (anchorSet T) (pairSet T) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have h1 : (supp x).card = 1 := by
    simp only [anchorSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨t, a, ha, hxa⟩ := hx
    subst hxa
    rw [supp_one, Finset.card_singleton]
  have h2 : (supp x).card = 2 := by
    simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨t, a, ha, s, hs, hxa⟩ := hy
    have hne : a ≠ s := by
      intro h
      exact (Finset.mem_sdiff.1 ha).2 (h ▸ (Finset.mem_sdiff.1 hs).1)
    subst hxa
    rw [supp_two, Finset.card_pair hne]
  omega

lemma disjoint_anchor_zero (T : Finset (Fin 21)) : Disjoint (anchorSet T) zeroSet := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have h1 : (supp x).card = 1 := by
    simp only [anchorSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨t, a, ha, hxa⟩ := hx
    subst hxa
    rw [supp_one, Finset.card_singleton]
  have h2 : (supp x).card = 16 := by
    simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨t, hxt⟩ := hy
    subst hxt
    exact supp_zero_card t
  omega

lemma disjoint_pair_zero (T : Finset (Fin 21)) : Disjoint (pairSet T) zeroSet := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have h1 : (supp x).card = 2 := by
    simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨t, a, ha, s, hs, hxa⟩ := hx
    have hne : a ≠ s := by
      intro h
      exact (Finset.mem_sdiff.1 ha).2 (h ▸ (Finset.mem_sdiff.1 hs).1)
    subst hxa
    rw [supp_two, Finset.card_pair hne]
  have h2 : (supp x).card = 16 := by
    simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨t, hxt⟩ := hy
    subst hxt
    exact supp_zero_card t
  omega

lemma allSet_eq (T : Finset (Fin 21)) : allSet T = anchorSet T ∪ pairSet T ∪ zeroSet := by
  ext x
  simp only [allSet, anchorSet, pairSet, zeroSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · intro hx
    obtain ⟨t, hx⟩ := hx
    rcases hx with hx | hx | hx
    · exact Or.inl (Or.inl ⟨t, hx⟩)
    · exact Or.inl (Or.inr ⟨t, hx⟩)
    · exact Or.inr ⟨t, hx⟩
  · intro hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨t, hx⟩ := hx
      exact ⟨t, Or.inl hx⟩
    · obtain ⟨t, hx⟩ := hx
      exact ⟨t, Or.inr (Or.inl hx)⟩
    · obtain ⟨t, hx⟩ := hx
      exact ⟨t, Or.inr (Or.inr hx)⟩

lemma card_all (T : Finset (Fin 21)) (hT : T.card = 3) : (allSet T).card = 78 := by
  rw [allSet_eq]
  have hz : Disjoint (anchorSet T ∪ pairSet T) zeroSet := by
    rw [Finset.disjoint_union_left]
    exact ⟨disjoint_anchor_zero T, disjoint_pair_zero T⟩
  have h3 : (anchorSet T).card + (pairSet T).card + zeroSet.card = 78 := by
    rw [card_anchor T hT, card_pair T hT, card_zero]
  rw [card_union_disjoint hz, card_union_disjoint (disjoint_anchor_pair T)]
  exact h3

end PEqualNP.Outside.L_meta_1560

open PEqualNP.Outside.L_meta_1560

theorem PEqualNP.Outside.L_meta_1560 :
  ∀ L : Fin 21 → Finset (Fin 21), (∀ t : Fin 21, L t = {t, t + 1, t + 4, t + 14, t + 16}) →
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
      x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 78
  := by
  intro L hL T hT hnot
  have hLfun : L = lineSet := funext hL
  subst hLfun
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hm t
    have hne : ∃ v ∈ T, v ∉ lineSet t := sub_not_subset T t (hnot t)
    exact ⟨fun h => mspec_forward hne h, fun h => mspec_backward hm h.1 h.2.1 h.2.2⟩
  · exact fun t => sub_not_subset T t (hnot t)
  · exact card_anchor T hT
  · exact card_pair T hT
  · exact card_zero
  · exact card_all T hT
