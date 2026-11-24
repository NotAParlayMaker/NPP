import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1560

def Lz (t : Fin 21) : Finset (Fin 21) := {t, t + 1, t + 4, t + 14, t + 16}

theorem self_mem (a : Fin 21) : a ∈ Lz a := by simp [Lz]

set_option maxRecDepth 100000 in
theorem ex_line : ∀ a s : Fin 21, a ≠ s → ∃ t : Fin 21, a ∉ Lz t ∧ s ∈ Lz t := by
  decide

set_option maxRecDepth 100000 in
theorem coline_inj : ∀ t t' : Fin 21,
    (fun v : Fin 21 => decide (v ∉ Lz t)) = (fun v : Fin 21 => decide (v ∉ Lz t')) → t = t' := by
  decide

set_option maxRecDepth 100000 in
theorem coline_card : ∀ t : Fin 21, (Finset.univ.filter (fun v : Fin 21 => decide (v ∉ Lz t) = true)).card = 16 := by
  decide

theorem single_card (a : Fin 21) : (Finset.univ.filter (fun v : Fin 21 => decide (v = a) = true)).card = 1 := by
  have : (Finset.univ.filter (fun v : Fin 21 => decide (v = a) = true)) = {a} := by
    ext v; simp
  rw [this, Finset.card_singleton]

theorem pair_card (a s : Fin 21) (h : a ≠ s) :
    (Finset.univ.filter (fun v : Fin 21 => decide (v = a ∨ v = s) = true)).card = 2 := by
  have : (Finset.univ.filter (fun v : Fin 21 => decide (v = a ∨ v = s) = true)) = {a, s} := by
    ext v; simp
  rw [this, Finset.card_pair h]

theorem iffPart (L : Fin 21 → Finset (Fin 21)) (T : Finset (Fin 21)) (hT : ∀ t : Fin 21, ¬ T ⊆ L t)
    (f : (Fin 21 → Bool) → Bool)
    (hf : ∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) → f x = true → f y = true)
    (t : Fin 21) :
    ((∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) → f x = decide (∃ v ∈ L t, x v = true)) ↔
      ((∀ a ∈ T ∩ L t, f (fun v : Fin 21 => decide (v = a)) = true) ∧
       (∀ a ∈ T \ L t, ∀ s ∈ L t \ T, f (fun v : Fin 21 => decide (v = a ∨ v = s)) = true) ∧
       f (fun v : Fin 21 => decide (v ∉ L t)) = false)) := by
  constructor
  · intro H
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_inter] at ha
      rw [H _ ⟨a, ha.1, by simp⟩]
      simp only [decide_eq_true_eq]
      exact ⟨a, ha.2, by simp⟩
    · intro a ha s hs
      rw [Finset.mem_sdiff] at ha hs
      rw [H _ ⟨a, ha.1, by simp⟩]
      simp only [decide_eq_true_eq]
      exact ⟨s, hs.1, by simp⟩
    · obtain ⟨v, hvT, hvL⟩ := Finset.not_subset.mp (hT t)
      rw [H _ ⟨v, hvT, by simp [hvL]⟩]
      simp
  · rintro ⟨h1, h2, h3⟩ x ⟨b, hbT, hxb⟩
    by_cases hx : ∃ v ∈ L t, x v = true
    · rw [decide_eq_true hx]
      obtain ⟨s, hsL, hxs⟩ := hx
      by_cases hsT : s ∈ T
      · apply hf _ _ _ (h1 s (Finset.mem_inter.mpr ⟨hsT, hsL⟩))
        intro v hv
        simp only [decide_eq_true_eq] at hv
        rw [hv]; exact hxs
      · by_cases hbL : b ∈ L t
        · apply hf _ _ _ (h1 b (Finset.mem_inter.mpr ⟨hbT, hbL⟩))
          intro v hv
          simp only [decide_eq_true_eq] at hv
          rw [hv]; exact hxb
        · apply hf _ _ _ (h2 b (Finset.mem_sdiff.mpr ⟨hbT, hbL⟩) s (Finset.mem_sdiff.mpr ⟨hsL, hsT⟩))
          intro v hv
          simp only [decide_eq_true_eq] at hv
          rcases hv with rfl | rfl
          · exact hxb
          · exact hxs
    · rw [decide_eq_false hx]
      by_contra hfx
      have hfx' : f x = true := by
        cases h : f x
        · exact absurd h hfx
        · rfl
      have := hf x (fun v : Fin 21 => decide (v ∉ L t)) (by
        intro v hv
        simp only [decide_eq_true_eq]
        exact fun hvL => hx ⟨v, hvL, hv⟩) hfx'
      rw [h3] at this
      exact Bool.false_ne_true this

theorem single_inj : Function.Injective (fun a : Fin 21 => fun v : Fin 21 => decide (v = a)) := by
  intro a b h
  simpa using congrFun h a

theorem c1 (T : Finset (Fin 21)) (hTc : T.card = 3) :
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ Lz t, x = (fun v : Fin 21 => decide (v = a)))).card = 3 := by
  have h : (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ Lz t, x = (fun v : Fin 21 => decide (v = a)))) =
      T.image (fun a : Fin 21 => fun v : Fin 21 => decide (v = a)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_inter]
    constructor
    · rintro ⟨t, a, ⟨ha, -⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, a, ⟨ha, self_mem a⟩, rfl⟩
  rw [h, Finset.card_image_of_injective _ single_inj, hTc]

theorem c2 (T : Finset (Fin 21)) (hTc : T.card = 3) :
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ Lz t, ∃ s ∈ Lz t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s)))).card = 54 := by
  have h : (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ Lz t, ∃ s ∈ Lz t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s)))) =
      (T ×ˢ (Finset.univ \ T)).image (fun p : Fin 21 × Fin 21 => fun v : Fin 21 => decide (v = p.1 ∨ v = p.2)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_sdiff,
      Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨t, a, ⟨ha, -⟩, s, ⟨-, hs⟩, rfl⟩
      exact ⟨a, s, ⟨ha, hs⟩, rfl⟩
    · rintro ⟨a, s, ⟨ha, hs⟩, rfl⟩
      have hne : a ≠ s := fun h => hs (h ▸ ha)
      obtain ⟨t, hat, hst⟩ := ex_line a s hne
      exact ⟨t, a, ⟨ha, hat⟩, s, ⟨hst, hs⟩, rfl⟩
  rw [h, Finset.card_image_of_injOn]
  · rw [Finset.card_product, Finset.card_univ_diff, hTc]
    simp
  · intro p hp q hq hpq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at hp hq
    have e1 := congrFun hpq p.1
    have e2 := congrFun hpq p.2
    simp only [true_or, decide_true, or_true] at e1 e2
    have e1' : p.1 = q.1 ∨ p.1 = q.2 := by simpa using e1.symm
    have e2' : p.2 = q.1 ∨ p.2 = q.2 := by simpa using e2.symm
    have h1 : p.1 = q.1 := by
      rcases e1' with h | h
      · exact h
      · exact absurd (h ▸ hp.1) hq.2
    have h2 : p.2 = q.2 := by
      rcases e2' with h | h
      · exact absurd (h ▸ hq.1) hp.2
      · exact h
    exact Prod.ext h1 h2

theorem c3 :
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, x = (fun v : Fin 21 => decide (v ∉ Lz t)))).card = 21 := by
  have h : (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, x = (fun v : Fin 21 => decide (v ∉ Lz t)))) =
      (Finset.univ : Finset (Fin 21)).image (fun t : Fin 21 => fun v : Fin 21 => decide (v ∉ Lz t)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
  rw [h, Finset.card_image_of_injective _ (fun t t' h => coline_inj t t' h)]
  simp

def wt (x : Fin 21 → Bool) : ℕ := (Finset.univ.filter (fun v : Fin 21 => x v = true)).card

theorem c4 (T : Finset (Fin 21)) (hTc : T.card = 3) :
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, (∃ a ∈ T ∩ Lz t, x = (fun v : Fin 21 => decide (v = a))) ∨
      (∃ a ∈ T \ Lz t, ∃ s ∈ Lz t \ T, x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ∨
      x = (fun v : Fin 21 => decide (v ∉ Lz t)))).card = 78 := by
  set S1 := Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ Lz t, x = (fun v : Fin 21 => decide (v = a))) with hS1
  set S2 := Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ Lz t, ∃ s ∈ Lz t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s))) with hS2
  set S3 := Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, x = (fun v : Fin 21 => decide (v ∉ Lz t))) with hS3
  have hU : (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, (∃ a ∈ T ∩ Lz t, x = (fun v : Fin 21 => decide (v = a))) ∨
      (∃ a ∈ T \ Lz t, ∃ s ∈ Lz t \ T, x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ∨
      x = (fun v : Fin 21 => decide (v ∉ Lz t)))) = S1 ∪ S2 ∪ S3 := by
    ext x
    simp only [hS1, hS2, hS3, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, h | h | h⟩
      · exact Or.inl (Or.inl ⟨t, h⟩)
      · exact Or.inl (Or.inr ⟨t, h⟩)
      · exact Or.inr ⟨t, h⟩
    · rintro ((⟨t, h⟩ | ⟨t, h⟩) | ⟨t, h⟩)
      · exact ⟨t, Or.inl h⟩
      · exact ⟨t, Or.inr (Or.inl h)⟩
      · exact ⟨t, Or.inr (Or.inr h)⟩
  have w1 : ∀ x ∈ S1, wt x = 1 := by
    intro x hx
    simp only [hS1, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨t, a, -, rfl⟩ := hx
    exact single_card a
  have w2 : ∀ x ∈ S2, wt x = 2 := by
    intro x hx
    simp only [hS2, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨t, a, ha, s, hs, rfl⟩ := hx
    rw [Finset.mem_sdiff] at ha hs
    exact pair_card a s (fun h => hs.2 (h ▸ ha.1))
  have w3 : ∀ x ∈ S3, wt x = 16 := by
    intro x hx
    simp only [hS3, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨t, rfl⟩ := hx
    exact coline_card t
  have d12 : Disjoint S1 S2 := Finset.disjoint_left.mpr (fun x h1 h2 => by
    have := (w1 x h1).symm.trans (w2 x h2); omega)
  have d3 : Disjoint (S1 ∪ S2) S3 := Finset.disjoint_left.mpr (fun x h h3 => by
    rcases Finset.mem_union.mp h with h | h
    · have := (w1 x h).symm.trans (w3 x h3); omega
    · have := (w2 x h).symm.trans (w3 x h3); omega)
  rw [hU, Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d12, hS1, hS2, hS3,
    c1 T hTc, c2 T hTc, c3]

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
      x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 78 := by
  intro L hL T hTc hT
  obtain rfl : L = PEqualNP.Outside.L_meta_1560.Lz := funext hL
  refine ⟨fun f hf t => PEqualNP.Outside.L_meta_1560.iffPart _ T hT f hf t,
    fun t => Finset.not_subset.mp (hT t),
    PEqualNP.Outside.L_meta_1560.c1 T hTc, PEqualNP.Outside.L_meta_1560.c2 T hTc,
    PEqualNP.Outside.L_meta_1560.c3, PEqualNP.Outside.L_meta_1560.c4 T hTc⟩
