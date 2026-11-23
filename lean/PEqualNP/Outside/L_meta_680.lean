import Mathlib
import PEqualNP.Defs


theorem PEqualNP.Outside.L_meta_680 : ∀ (n : ℕ) [NeZero n] (D : Finset (ZMod n)),
    (∀ d : ZMod n, d ≠ 0 → ((D ×ˢ D).filter (fun q : ZMod n × ZMod n => q.1 - q.2 = d)).card = 1) →
    (∀ s t : ZMod n, s ≠ t →
        (D.image (fun a : ZMod n => a + s) ∩ D.image (fun a : ZMod n => a + t)).card = 1) ∧
    (∀ x : ZMod n,
        (Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a : ZMod n => a + w))).card = D.card) := by
  intro n _ D h
  constructor
  · intro s t hst
    have hd : t - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hst)
    obtain ⟨q0, hq0⟩ := Finset.card_eq_one.mp (h (t - s) hd)
    have e : D.image (fun a : ZMod n => a + s) ∩ D.image (fun a : ZMod n => a + t)
        = {q0.1 + s} := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
        have hmem : (a, b) ∈ (D ×ˢ D).filter
            (fun q : ZMod n × ZMod n => q.1 - q.2 = t - s) := by
          simp only [Finset.mem_filter, Finset.mem_product]
          refine ⟨⟨ha, hb⟩, ?_⟩
          linear_combination -hab
        rw [hq0, Finset.mem_singleton] at hmem
        rw [← hmem]
      · rintro rfl
        have hmem : q0 ∈ (D ×ˢ D).filter
            (fun q : ZMod n × ZMod n => q.1 - q.2 = t - s) := by
          rw [hq0]
          exact Finset.mem_singleton_self q0
        simp only [Finset.mem_filter, Finset.mem_product] at hmem
        refine ⟨⟨q0.1, hmem.1.1, rfl⟩, ⟨q0.2, hmem.1.2, ?_⟩⟩
        linear_combination -hmem.2
    rw [e, Finset.card_singleton]
  · intro x
    have e : Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a : ZMod n => a + w))
        = D.image (fun a : ZMod n => x - a) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, by ring⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, by ring⟩
    rw [e]
    exact Finset.card_image_of_injective D sub_right_injective
