import Mathlib.GroupTheory.Index
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- Mythos 6 et Codex Betelgeuse

namespace PEqualNP.Outside.Meta664

lemma filter_card {F : Type*} [Fintype F] (P : F → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = Nat.card {t // P t} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma card_preimage {F : Type*} [Fintype F] (g : F → F)
    (hg : Function.Bijective g) (A : Set F) :
    Nat.card {t // g t ∈ A} = Nat.card A := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun t : {t // g t ∈ A} => (⟨g t, t.property⟩ : A)) ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (hg.1 (congrArg Subtype.val h))
  · intro a
    obtain ⟨t, ht⟩ := hg.2 a
    exact ⟨⟨t, ht ▸ a.property⟩, Subtype.ext ht⟩

lemma translate_card {G : Type*} [AddCommGroup G] (f : G →+ G)
    (A : AddSubgroup G) (e t₀ : G) (ht₀ : e + f t₀ ∈ A) :
    Nat.card {t // e + f t ∈ A} = Nat.card (A.comap f) := by
  apply Nat.card_congr
  refine {
    toFun := fun t => ⟨t - t₀, ?_⟩
    invFun := fun t => ⟨t + t₀, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · change f ((t : G) - t₀) ∈ A
    simpa only [map_sub, add_sub_add_left_eq_sub] using A.sub_mem t.property ht₀
  · simpa only [map_add, add_left_comm e] using A.add_mem t.property ht₀
  · intro t
    exact Subtype.ext (sub_add_cancel _ _)
  · intro t
    exact Subtype.ext (add_sub_cancel_right _ _)

lemma sup_eq_top {G : Type*} [AddCommGroup G] [Finite G]
    (R A : AddSubgroup G) (hR : R.index = 2) (hA : ¬ A ≤ R) :
    R ⊔ A = ⊤ := by
  have hd : (R ⊔ A).index ∣ 2 := hR ▸ AddSubgroup.index_dvd_of_le (show R ≤ R ⊔ A from le_sup_left)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact AddSubgroup.index_eq_one.mp h
  · have he : R = R ⊔ A := AddSubgroup.eq_of_index_dvd_index le_sup_left (by rw [hR, h])
    exact False.elim (hA (he ▸ le_sup_right))

lemma count_additive {G : Type*} [AddCommGroup G] [Finite G]
    (f : G →+ G) (A : AddSubgroup G) (e : G)
    (hk : Nat.card f.ker = 2) (he : e ∉ f.range) :
    Nat.card {t // e + f t ∈ A} = 0 ∨ Nat.card {t // e + f t ∈ A} = Nat.card A := by
  classical
  by_cases h : ∃ t, e + f t ∈ A
  · obtain ⟨t₀, ht₀⟩ := h
    right
    rw [translate_card f A e t₀ ht₀]
    have hA : ¬ A ≤ f.range := by
      intro hle
      have := f.range.sub_mem (hle ht₀) (show f t₀ ∈ f.range from ⟨t₀, rfl⟩)
      exact he (by simpa using this)
    have hsup := sup_eq_top f.range A (AddSubgroup.index_range.trans hk) hA
    have hi : (A.comap f).index = A.index := by
      rw [A.index_comap, ← AddSubgroup.relIndex_sup_left f.range A, sup_comm, hsup,
        A.relIndex_top_right]
    have hc := (A.comap f).card_mul_index
    rw [hi, ← A.card_mul_index] at hc
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero A.index_ne_zero) hc
  · left
    have : IsEmpty {t // e + f t ∈ A} := ⟨fun t => h ⟨t.val, t.property⟩⟩
    simp

def q {F : Type*} [Field F] (b : F) (z : F × F) : F :=
  z.1 ^ 2 + b * z.1 * z.2 + z.2 ^ 2

lemma anisotropic {F : Type*} [Field F] (b : F)
    (hb : ∀ x : F, x ^ 2 + b * x + 1 ≠ 0) (z : F × F)
    (hz : q b z = 0) : z = 0 := by
  rcases z with ⟨x, y⟩
  change x ^ 2 + b * x * y + y ^ 2 = 0 at hz
  by_cases hy : y = 0
  · subst y
    simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hz
    exact Prod.ext (eq_zero_of_pow_eq_zero hz) rfl
  · exfalso
    apply hb (x / y)
    calc
      (x / y) ^ 2 + b * (x / y) + 1 = (x ^ 2 + b * x * y + y ^ 2) / y ^ 2 := by
        field_simp
      _ = 0 := by rw [hz, zero_div]

def lineMap {F : Type*} [Field F] [CharP F 2] (a c : F) : F →+ F where
  toFun t := a * t ^ 2 + c * t
  map_zero' := by simp
  map_add' s t := by
    rw [CharTwo.add_sq]
    ring

lemma expand_line {F : Type*} [Field F] [CharP F 2]
    (b : F) (p d : F × F) (t : F) :
    q b (p + t • d) = q b p + lineMap (q b d) (b * (p.1 * d.2 + p.2 * d.1)) t := by
  change (p.1 + t * d.1) ^ 2 + b * (p.1 + t * d.1) * (p.2 + t * d.2) +
    (p.2 + t * d.2) ^ 2 =
    (p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2) +
    ((d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2) * t ^ 2 +
    (b * (p.1 * d.2 + p.2 * d.1)) * t)
  rw [CharTwo.add_sq, CharTwo.add_sq]
  ring

lemma lineMap_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (a : F) (ha : a ≠ 0) : Function.Bijective (lineMap a 0) := by
  apply (Finite.injective_iff_bijective).mp
  intro s t h
  apply CharTwo.sq_injective
  exact mul_left_cancel₀ ha (by simpa [lineMap] using h)

lemma lineMap_kernel {F : Type*} [Field F] [CharP F 2]
    (a c : F) (ha : a ≠ 0) (hc : c ≠ 0) : Nat.card (lineMap a c).ker = 2 := by
  have hroot : ∀ t : F, lineMap a c t = 0 ↔ t = 0 ∨ t = c / a := by
    intro t
    change a * t ^ 2 + c * t = 0 ↔ _
    rw [show a * t ^ 2 + c * t = t * (a * t + c) by ring, mul_eq_zero,
      CharTwo.add_eq_zero]
    rw [eq_div_iff ha, mul_comm]
  have hw : lineMap a c (c / a) = 0 := (hroot _).2 (Or.inr rfl)
  rw [Nat.card_eq_two_iff' (0 : (lineMap a c).ker)]
  refine ⟨⟨c / a, hw⟩, ?_, ?_⟩
  · intro he
    have he' : c / a = 0 := congrArg Subtype.val he
    exact (div_ne_zero hc ha) he'
  · intro y hy
    apply Subtype.ext
    exact ((hroot y.val).1 y.property).resolve_left (fun he => hy (Subtype.ext he))

lemma constant_outside {F : Type*} [Field F] [CharP F 2]
    (b : F) (hb : ∀ x : F, x ^ 2 + b * x + 1 ≠ 0) (p d : F × F)
    (hc : b * (p.1 * d.2 + p.2 * d.1) ≠ 0) :
    q b p ∉ (lineMap (q b d) (b * (p.1 * d.2 + p.2 * d.1))).range := by
  rintro ⟨t, ht⟩
  have hz : q b (p + t • d) = 0 := by
    rw [expand_line, ht, CharTwo.add_self_eq_zero]
  have hp := anisotropic b hb (p + t • d) hz
  have hx : p.1 = t * d.1 := CharTwo.add_eq_zero.mp (congrArg Prod.fst hp)
  have hy : p.2 = t * d.2 := CharTwo.add_eq_zero.mp (congrArg Prod.snd hp)
  apply hc
  rw [hx, hy]
  calc
    b * (t * d.1 * d.2 + t * d.2 * d.1) = 2 * (b * t * d.1 * d.2) := by ring
    _ = 0 := by rw [CharTwo.two_eq_zero, zero_mul]

end PEqualNP.Outside.Meta664

namespace PEqualNP.Outside

open Meta664

theorem L_meta_664 :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  simp only [filter_card]
  change (Nat.card {t : F // q b (p + t • d) ∈ A} = 0 ∨
    Nat.card {t : F // q b (p + t • d) ∈ A} = Nat.card A) ∧
    (p = 0 → Nat.card {t : F // q b (p + t • d) ∈ A} = Nat.card A)
  have ha : q b d ≠ 0 := fun h => hd (anisotropic b hb d h)
  have hzero (hc : b * (p.1 * d.2 + p.2 * d.1) = 0) :
      Nat.card {t : F // q b (p + t • d) ∈ A} = Nat.card A := by
    apply card_preimage (fun t => q b (p + t • d)) _ (A : Set F)
    apply Finite.injective_iff_bijective.mp
    intro s t hst
    change q b (p + s • d) = q b (p + t • d) at hst
    rw [expand_line, expand_line, hc] at hst
    exact (lineMap_bijective (q b d) ha).1 (add_left_cancel hst)
  constructor
  · by_cases hc : b * (p.1 * d.2 + p.2 * d.1) = 0
    · exact Or.inr (hzero hc)
    · simpa only [expand_line] using count_additive
        (lineMap (q b d) (b * (p.1 * d.2 + p.2 * d.1))) A (q b p)
        (lineMap_kernel _ _ ha hc) (constant_outside b hb p d hc)
  · intro hp
    apply hzero
    simp [hp]

end PEqualNP.Outside
