import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_680 : ∀ (n : ℕ) [NeZero n] (D : Finset (ZMod n)),
    (∀ d : ZMod n, d ≠ 0 → ((D ×ˢ D).filter (fun q : ZMod n × ZMod n => q.1 - q.2 = d)).card = 1) →
    (∀ s t : ZMod n, s ≠ t →
        (D.image (fun a : ZMod n => a + s) ∩ D.image (fun a : ZMod n => a + t)).card = 1) ∧
    (∀ x : ZMod n,
        (Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a : ZMod n => a + w))).card = D.card) := by
  intro n _ D h
  refine ⟨?_, ?_⟩
  · intro s t hst
    rw [← h (t - s) (sub_ne_zero.mpr (Ne.symm hst))]
    apply Finset.card_bij (fun x _ => (x - s, x - t))
    · intro x hx
      simp only [Finset.mem_inter, Finset.mem_image] at hx
      obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩ := hx
      simp only [Finset.mem_filter, Finset.mem_product]
      have e : a + s - t = b := by linear_combination (-1 : ZMod n) * hab
      refine ⟨⟨by simpa using ha, ?_⟩, by ring⟩
      rw [e]; exact hb
    · intro x _ y _ hxy
      simpa using congrArg Prod.fst hxy
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨h1, h2⟩, h3⟩ := hq
      refine ⟨q.1 + s, ?_, ?_⟩
      · simp only [Finset.mem_inter, Finset.mem_image]
        exact ⟨⟨q.1, h1, rfl⟩, ⟨q.2, h2, by linear_combination (-1 : ZMod n) * h3⟩⟩
      · refine Prod.ext (by simp) ?_
        show q.1 + s - t = q.2
        linear_combination h3
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
    rw [e, Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)]
