import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1560

def Ln (t : Fin 21) : Finset (Fin 21) := {t, t + 1, t + 4, t + 14, t + 16}

lemma onLine : ∀ a : Fin 21, ∃ t : Fin 21, a ∈ Ln t := by decide +kernel

lemma sep : ∀ a s : Fin 21, a ≠ s → ∃ t : Fin 21, s ∈ Ln t ∧ a ∉ Ln t := by decide +kernel

lemma lineInj : ∀ t t' : Fin 21, Ln t = Ln t' → t = t' := by decide +kernel

lemma away : ∀ t a s : Fin 21, ∃ v : Fin 21, v ≠ a ∧ v ≠ s ∧ v ∉ Ln t := by decide +kernel

def S1 (T : Finset (Fin 21)) : Finset (Fin 21 → Bool) :=
  T.image (fun a v => decide (v = a))

def S2 (T : Finset (Fin 21)) : Finset (Fin 21 → Bool) :=
  (T ×ˢ Tᶜ).image (fun p v => decide (v = p.1 ∨ v = p.2))

def S3 : Finset (Fin 21 → Bool) :=
  Finset.univ.image (fun (t : Fin 21) (v : Fin 21) => decide (v ∉ Ln t))

lemma part2 (T : Finset (Fin 21)) (hnl : ∀ t : Fin 21, ¬ T ⊆ Ln t) :
    ∀ t : Fin 21, ∃ v ∈ T, v ∉ Ln t := by
  intro t
  have h := hnl t
  rw [Finset.not_subset] at h
  exact h

lemma part1 (T : Finset (Fin 21)) (hnl : ∀ t : Fin 21, ¬ T ⊆ Ln t)
    (f : (Fin 21 → Bool) → Bool)
    (hmono : ∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) →
      f x = true → f y = true) (t : Fin 21) :
    ((∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) → f x = decide (∃ v ∈ Ln t, x v = true)) ↔
      ((∀ a ∈ T ∩ Ln t, f (fun v : Fin 21 => decide (v = a)) = true) ∧
       (∀ a ∈ T \ Ln t, ∀ s ∈ Ln t \ T, f (fun v : Fin 21 => decide (v = a ∨ v = s)) = true) ∧
       f (fun v : Fin 21 => decide (v ∉ Ln t)) = false)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨haT, haL⟩ := Finset.mem_inter.mp ha
      have h0 := h (fun v : Fin 21 => decide (v = a)) ⟨a, haT, decide_eq_true rfl⟩
      exact h0.trans (decide_eq_true ⟨a, haL, decide_eq_true rfl⟩)
    · intro a ha s hs
      obtain ⟨haT, _⟩ := Finset.mem_sdiff.mp ha
      obtain ⟨hsL, _⟩ := Finset.mem_sdiff.mp hs
      have h0 := h (fun v : Fin 21 => decide (v = a ∨ v = s))
        ⟨a, haT, decide_eq_true (Or.inl rfl)⟩
      exact h0.trans (decide_eq_true ⟨s, hsL, decide_eq_true (Or.inr rfl)⟩)
    · obtain ⟨v, hvT, hvL⟩ := part2 T hnl t
      have h0 := h (fun v : Fin 21 => decide (v ∉ Ln t)) ⟨v, hvT, decide_eq_true hvL⟩
      refine h0.trans (decide_eq_false ?_)
      rintro ⟨u, huL, hu⟩
      exact (of_decide_eq_true hu) huL
  · rintro ⟨h1, h2, h3⟩ x ⟨v, hvT, hxv⟩
    by_cases hex : ∃ u ∈ Ln t, x u = true
    · refine (?_ : f x = true).trans (decide_eq_true hex).symm
      obtain ⟨u, huL, hxu⟩ := hex
      by_cases hvL : v ∈ Ln t
      · refine hmono _ x ?_ (h1 v (Finset.mem_inter.mpr ⟨hvT, hvL⟩))
        intro w hw
        have e : w = v := of_decide_eq_true hw
        rw [e]
        exact hxv
      · by_cases huT : u ∈ T
        · refine hmono _ x ?_ (h1 u (Finset.mem_inter.mpr ⟨huT, huL⟩))
          intro w hw
          have e : w = u := of_decide_eq_true hw
          rw [e]
          exact hxu
        · refine hmono _ x ?_
            (h2 v (Finset.mem_sdiff.mpr ⟨hvT, hvL⟩) u (Finset.mem_sdiff.mpr ⟨huL, huT⟩))
          intro w hw
          have e : w = v ∨ w = u := of_decide_eq_true hw
          rcases e with e | e
          · rw [e]
            exact hxv
          · rw [e]
            exact hxu
    · refine (?_ : f x = false).trans (decide_eq_false hex).symm
      cases hfx : f x with
      | false => rfl
      | true =>
        have key : ∀ w : Fin 21, x w = true →
            (fun v : Fin 21 => decide (v ∉ Ln t)) w = true :=
          fun w hw => decide_eq_true (fun hwL => hex ⟨w, hwL, hw⟩)
        have h4 := hmono x _ key hfx
        rw [h3] at h4
        exact h4.symm

lemma single_inj :
    Function.Injective (fun (a : Fin 21) (v : Fin 21) => decide (v = a)) := by
  intro a b h
  have h1 : decide (a = a) = decide (a = b) := congrFun h a
  exact of_decide_eq_true (h1.symm.trans (decide_eq_true rfl))

lemma co_inj :
    Function.Injective (fun (t : Fin 21) (v : Fin 21) => decide (v ∉ Ln t)) := by
  intro t t' h
  apply lineInj
  ext v
  have h1 : decide (v ∉ Ln t) = decide (v ∉ Ln t') := congrFun h v
  exact not_iff_not.mp (decide_eq_decide.mp h1)

lemma pair_injOn (T : Finset (Fin 21)) :
    Set.InjOn (fun (p : Fin 21 × Fin 21) (v : Fin 21) => decide (v = p.1 ∨ v = p.2))
      (T ×ˢ Tᶜ : Finset (Fin 21 × Fin 21)) := by
  rintro ⟨a, s⟩ hp ⟨a', s'⟩ hp' h
  obtain ⟨haT, hsT⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp)
  obtain ⟨ha'T, hs'T⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp')
  have hsT' : s ∉ T := Finset.mem_compl.mp hsT
  have hs'T' : s' ∉ T := Finset.mem_compl.mp hs'T
  have h1 : decide (a = a ∨ a = s) = decide (a = a' ∨ a = s') := congrFun h a
  have h2 : decide (s = a ∨ s = s) = decide (s = a' ∨ s = s') := congrFun h s
  have ha : a = a' ∨ a = s' := of_decide_eq_true (h1.symm.trans (decide_eq_true (Or.inl rfl)))
  have hs : s = a' ∨ s = s' := of_decide_eq_true (h2.symm.trans (decide_eq_true (Or.inr rfl)))
  have e1 : a = a' := ha.resolve_right (fun e => hs'T' (by rw [← e]; exact haT))
  have e2 : s = s' := hs.resolve_left (fun e => hsT' (by rw [e]; exact ha'T))
  exact Prod.ext e1 e2

lemma card1 (T : Finset (Fin 21)) (hT : T.card = 3) : (S1 T).card = 3 := by
  unfold S1
  rw [Finset.card_image_of_injective _ single_inj, hT]

lemma card2 (T : Finset (Fin 21)) (hT : T.card = 3) : (S2 T).card = 54 := by
  unfold S2
  rw [Finset.card_image_of_injOn (pair_injOn T), Finset.card_product, Finset.card_compl, hT,
    Fintype.card_fin]

lemma card3 : S3.card = 21 := by
  unfold S3
  rw [Finset.card_image_of_injective _ co_inj, Finset.card_univ, Fintype.card_fin]

lemma mem1 (T : Finset (Fin 21)) (x : Fin 21 → Bool) :
    (∃ t : Fin 21, ∃ a ∈ T ∩ Ln t, x = (fun v : Fin 21 => decide (v = a))) ↔ x ∈ S1 T := by
  constructor
  · rintro ⟨t, a, ha, rfl⟩
    exact Finset.mem_image.mpr ⟨a, (Finset.mem_inter.mp ha).1, rfl⟩
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨t, ht⟩ := onLine a
    exact ⟨t, a, Finset.mem_inter.mpr ⟨ha, ht⟩, rfl⟩

lemma mem2 (T : Finset (Fin 21)) (x : Fin 21 → Bool) :
    (∃ t : Fin 21, ∃ a ∈ T \ Ln t, ∃ s ∈ Ln t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ↔ x ∈ S2 T := by
  constructor
  · rintro ⟨t, a, ha, s, hs, rfl⟩
    exact Finset.mem_image.mpr ⟨(a, s), Finset.mem_product.mpr
      ⟨(Finset.mem_sdiff.mp ha).1, Finset.mem_compl.mpr (Finset.mem_sdiff.mp hs).2⟩, rfl⟩
  · intro h
    obtain ⟨⟨a, s⟩, hp, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ha, hs⟩ := Finset.mem_product.mp hp
    have hs' : s ∉ T := Finset.mem_compl.mp hs
    have hne : a ≠ s := fun e => hs' (by rw [← e]; exact ha)
    obtain ⟨t, hst, hat⟩ := sep a s hne
    exact ⟨t, a, Finset.mem_sdiff.mpr ⟨ha, hat⟩, s, Finset.mem_sdiff.mpr ⟨hst, hs'⟩, rfl⟩

lemma mem3 (x : Fin 21 → Bool) :
    (∃ t : Fin 21, x = (fun v : Fin 21 => decide (v ∉ Ln t))) ↔ x ∈ S3 := by
  constructor
  · rintro ⟨t, rfl⟩
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  · intro h
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨t, rfl⟩

lemma mem4 (T : Finset (Fin 21)) (x : Fin 21 → Bool) :
    (∃ t : Fin 21, (∃ a ∈ T ∩ Ln t, x = (fun v : Fin 21 => decide (v = a))) ∨
      (∃ a ∈ T \ Ln t, ∃ s ∈ Ln t \ T, x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ∨
      x = (fun v : Fin 21 => decide (v ∉ Ln t))) ↔ x ∈ S1 T ∪ (S2 T ∪ S3) := by
  rw [Finset.mem_union, Finset.mem_union, ← mem1 T x, ← mem2 T x, ← mem3 x]
  constructor
  · rintro ⟨t, h | h | h⟩
    · exact Or.inl ⟨t, h⟩
    · exact Or.inr (Or.inl ⟨t, h⟩)
    · exact Or.inr (Or.inr ⟨t, h⟩)
  · rintro (⟨t, h⟩ | ⟨t, h⟩ | ⟨t, h⟩)
    · exact ⟨t, Or.inl h⟩
    · exact ⟨t, Or.inr (Or.inl h)⟩
    · exact ⟨t, Or.inr (Or.inr h)⟩

lemma disj12 (T : Finset (Fin 21)) : Disjoint (S1 T) (S2 T) := by
  rw [Finset.disjoint_left]
  intro x h1 h2
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨⟨a', s'⟩, hp, h⟩ := Finset.mem_image.mp h2
  obtain ⟨_, hs'⟩ := Finset.mem_product.mp hp
  have e : decide (s' = a' ∨ s' = s') = decide (s' = a) := congrFun h s'
  have e2 : s' = a := of_decide_eq_true (e.symm.trans (decide_eq_true (Or.inr rfl)))
  exact (Finset.mem_compl.mp hs') (by rw [e2]; exact ha)

lemma disj13 (T : Finset (Fin 21)) : Disjoint (S1 T) S3 := by
  rw [Finset.disjoint_left]
  intro x h1 h3
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨t, _, h⟩ := Finset.mem_image.mp h3
  obtain ⟨v, hva, _, hvt⟩ := away t a a
  have e : decide (v ∉ Ln t) = decide (v = a) := congrFun h v
  exact hva (of_decide_eq_true (e.symm.trans (decide_eq_true hvt)))

lemma disj23 (T : Finset (Fin 21)) : Disjoint (S2 T) S3 := by
  rw [Finset.disjoint_left]
  intro x h2 h3
  obtain ⟨⟨a, s⟩, _, rfl⟩ := Finset.mem_image.mp h2
  obtain ⟨t, _, h⟩ := Finset.mem_image.mp h3
  obtain ⟨v, hva, hvs, hvt⟩ := away t a s
  have e : decide (v ∉ Ln t) = decide (v = a ∨ v = s) := congrFun h v
  have e2 : v = a ∨ v = s := of_decide_eq_true (e.symm.trans (decide_eq_true hvt))
  exact e2.elim hva hvs

lemma card4 (T : Finset (Fin 21)) (hT : T.card = 3) : (S1 T ∪ (S2 T ∪ S3)).card = 78 := by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨disj12 T, disj13 T⟩),
    Finset.card_union_of_disjoint (disj23 T), card1 T hT, card2 T hT, card3]

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
  intro L hL T hT hnl
  have hLn : L = Ln := funext hL
  subst hLn
  refine ⟨?_, part2 T hnl, ?_, ?_, ?_, ?_⟩
  · intro f hmono t
    exact part1 T hnl f hmono t
  · refine Eq.trans (congrArg Finset.card ?_) (card1 T hT)
    ext x
    rw [Finset.mem_filter]
    exact ⟨fun h => (mem1 T x).mp h.2, fun h => ⟨Finset.mem_univ _, (mem1 T x).mpr h⟩⟩
  · refine Eq.trans (congrArg Finset.card ?_) (card2 T hT)
    ext x
    rw [Finset.mem_filter]
    exact ⟨fun h => (mem2 T x).mp h.2, fun h => ⟨Finset.mem_univ _, (mem2 T x).mpr h⟩⟩
  · refine Eq.trans (congrArg Finset.card ?_) card3
    ext x
    rw [Finset.mem_filter]
    exact ⟨fun h => (mem3 x).mp h.2, fun h => ⟨Finset.mem_univ _, (mem3 x).mpr h⟩⟩
  · refine Eq.trans (congrArg Finset.card ?_) (card4 T hT)
    ext x
    rw [Finset.mem_filter]
    exact ⟨fun h => (mem4 T x).mp h.2, fun h => ⟨Finset.mem_univ _, (mem4 T x).mpr h⟩⟩
