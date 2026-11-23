import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_680 : ∀ (n : ℕ) [NeZero n] (D : Finset (ZMod n)),
    (∀ d : ZMod n, d ≠ 0 → ((D ×ˢ D).filter (fun q : ZMod n × ZMod n => q.1 - q.2 = d)).card = 1) →
    (∀ s t : ZMod n, s ≠ t →
        (D.image (fun a : ZMod n => a + s) ∩ D.image (fun a : ZMod n => a + t)).card = 1) ∧
    (∀ x : ZMod n,
        (Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a : ZMod n => a + w))).card = D.card) := by
  intro n _ D hD
  classical
  constructor
  · intro s t hst
    rw [← hD (t - s) (sub_ne_zero.mpr hst.symm)]
    refine Finset.card_bij' (fun x _ => (x - s, x - t)) (fun q _ => q.1 + s) ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hs, ht⟩ := Finset.mem_inter.mp hx
      obtain ⟨a, ha, ha'⟩ := Finset.mem_image.mp hs
      obtain ⟨b, hb, hb'⟩ := Finset.mem_image.mp ht
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · simpa [← ha'] using ha
      · simpa [← hb'] using hb
      · dsimp
        abel
    · rintro ⟨a, b⟩ h
      obtain ⟨hab, hd⟩ := Finset.mem_filter.mp h
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      apply Finset.mem_inter.mpr
      refine ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, Finset.mem_image.mpr ⟨b, hb, ?_⟩⟩
      change a - b = t - s at hd
      change b + t = a + s
      linear_combination -hd
    · intro x _
      exact sub_add_cancel x s
    · rintro ⟨a, b⟩ h
      have hd : a - b = t - s := (Finset.mem_filter.mp h).2
      apply Prod.ext
      · exact add_sub_cancel_right a s
      · change a + s - t = b
        linear_combination hd
  · intro x
    refine Finset.card_bij' (fun w _ => x - w) (fun a _ => x - a) ?_ ?_ ?_ ?_
    · intro w hw
      obtain ⟨a, ha, h⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hw).2
      simpa [← h] using ha
    · intro a ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨a, ha, ?_⟩⟩
      abel
    · intro w _
      abel
    · intro a _
      abel
