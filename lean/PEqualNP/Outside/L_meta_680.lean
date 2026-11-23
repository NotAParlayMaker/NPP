import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_680

theorem inter_card {n : ℕ} [NeZero n] (D : Finset (ZMod n)) (s t : ZMod n)
    (h : ((D ×ˢ D).filter (fun q : ZMod n × ZMod n => q.1 - q.2 = t - s)).card = 1) :
    (D.image (fun a : ZMod n => a + s) ∩ D.image (fun a : ZMod n => a + t)).card = 1 := by
  have he : D.image (fun a : ZMod n => a + s) ∩ D.image (fun a : ZMod n => a + t) =
      ((D ×ˢ D).filter (fun q : ZMod n × ZMod n => q.1 - q.2 = t - s)).image
        (fun q : ZMod n × ZMod n => q.1 + s) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      refine ⟨(a, b), ⟨⟨ha, hb⟩, ?_⟩, rfl⟩
      show a - b = t - s
      linear_combination -hab
    · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hd⟩, rfl⟩
      refine ⟨⟨a, ha, rfl⟩, ⟨b, hb, ?_⟩⟩
      have hd' : a - b = t - s := hd
      show b + t = a + s
      linear_combination -hd'
  rw [he, Finset.card_image_of_injOn, h]
  intro q hq q' hq' hqq
  have hq1 : q.1 - q.2 = t - s := (Finset.mem_filter.mp hq).2
  have hq2 : q'.1 - q'.2 = t - s := (Finset.mem_filter.mp hq').2
  have hqq' : q.1 + s = q'.1 + s := hqq
  have h1 : q.1 = q'.1 := add_right_cancel hqq'
  have h2 : q.2 = q'.2 := by
    linear_combination h1 - hq1 + hq2
  exact Prod.ext h1 h2

theorem translate_count {n : ℕ} [NeZero n] (D : Finset (ZMod n)) (x : ZMod n) :
    (Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a : ZMod n => a + w))).card =
      D.card := by
  have he : Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a : ZMod n => a + w)) =
      D.image (fun a : ZMod n => x - a) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, by ring⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, by ring⟩
  rw [he, Finset.card_image_of_injective]
  intro a b hab
  have hab' : x - a = x - b := hab
  linear_combination -hab'

end PEqualNP.Outside.L_meta_680

theorem PEqualNP.Outside.L_meta_680 : ∀ (n : ℕ) [NeZero n] (D : Finset (ZMod n)),
    (∀ d : ZMod n, d ≠ 0 → ((D ×ˢ D).filter (fun q : ZMod n × ZMod n => q.1 - q.2 = d)).card = 1) →
    (∀ s t : ZMod n, s ≠ t →
        (D.image (fun a : ZMod n => a + s) ∩ D.image (fun a : ZMod n => a + t)).card = 1) ∧
    (∀ x : ZMod n,
        (Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a : ZMod n => a + w))).card = D.card) := by
  intro n _ D h
  exact ⟨fun s t hst => PEqualNP.Outside.L_meta_680.inter_card D s t
      (h (t - s) (sub_ne_zero.mpr (Ne.symm hst))),
    fun x => PEqualNP.Outside.L_meta_680.translate_count D x⟩
