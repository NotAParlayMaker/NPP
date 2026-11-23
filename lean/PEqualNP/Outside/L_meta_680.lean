import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Abel

theorem PEqualNP.Outside.L_meta_680 : ∀ (n : ℕ) [NeZero n] (D : Finset (ZMod n)),
    (∀ d : ZMod n, d ≠ 0 → ((D ×ˢ D).filter (fun q : ZMod n × ZMod n => q.1 - q.2 = d)).card = 1) →
    (∀ s t : ZMod n, s ≠ t →
        (D.image (fun a : ZMod n => a + s) ∩ D.image (fun a : ZMod n => a + t)).card = 1) ∧
    (∀ x : ZMod n,
        (Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a : ZMod n => a + w))).card = D.card) := by
  intro n _ D hD
  constructor
  · intro s t hst
    obtain ⟨⟨a, b⟩, hab, huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp
      (hD (t - s) (sub_ne_zero.mpr hst.symm))
    simp only [Finset.mem_filter, Finset.mem_product] at hab
    have heq : a + s = b + t := by rw [← sub_eq_zero]; calc
      a + s - (b + t) = (a - b) - (t - s) := by abel
      _ = 0 := sub_eq_zero.mpr hab.2
    apply Finset.card_eq_one_iff_existsUnique.mpr
    refine ⟨a + s, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨a, hab.1.1, rfl⟩,
      Finset.mem_image.mpr ⟨b, hab.1.2, heq.symm⟩⟩, ?_⟩
    intro y hy
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_inter.mp hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy₁
    obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hy₂
    have huv : u - v = t - s := by calc
      u - v = (u + s) - (v + s) := by abel
      _ = t - s := by rw [← hvu]; abel
    have hpair := huniq (u, v) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, huv⟩)
    exact congrArg (fun p : ZMod n × ZMod n => p.1 + s) hpair
  · intro x
    have h : (Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a => a + w))) =
        D.image (fun a => x - a) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, by abel⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, by abel⟩
    rw [h]
    exact Finset.card_image_of_injective _ (fun _ _ hab => sub_right_injective hab)
