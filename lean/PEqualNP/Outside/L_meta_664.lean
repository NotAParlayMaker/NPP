import Mathlib
import PEqualNP.Defs

namespace Gap664

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

def quad (b : F) (p : F × F) : F := p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2

def cross (b : F) (p d : F × F) : F := b * (p.1 * d.2 + p.2 * d.1)

def phi (u c : F) : F →+ F where
  toFun t := u * t ^ 2 + c * t
  map_zero' := by simp
  map_add' := by intro x y; rw [CharTwo.add_sq]; ring

theorem quad_zero (b : F) (hb : ∀ x : F, x ^ 2 + b * x + 1 ≠ 0)
    (p : F × F) (h : quad b p = 0) : p = 0 := by
  rcases p with ⟨x, y⟩
  change x ^ 2 + b * x * y + y ^ 2 = 0 at h
  by_cases hy : y = 0
  · subst y
    simp at h
    simp [h]
  · exfalso
    apply hb (x / y)
    field_simp
    linear_combination h

theorem along (b : F) (p d : F × F) (t : F) :
    quad b (p + t • d) = quad b p + phi (quad b d) (cross b p d) t := by
  change (p.1 + t * d.1) ^ 2 + b * (p.1 + t * d.1) * (p.2 + t * d.2) +
      (p.2 + t * d.2) ^ 2 = _ + (quad b d * t ^ 2 + cross b p d * t)
  rw [CharTwo.add_sq, CharTwo.add_sq]
  unfold quad cross
  ring

theorem no_range (b : F) (hb : ∀ x : F, x ^ 2 + b * x + 1 ≠ 0)
    (p d : F × F) (hc : cross b p d ≠ 0) :
    quad b p ∉ (phi (quad b d) (cross b p d)).range := by
  rintro ⟨t, ht⟩
  have h : quad b (p + t • d) = 0 := by rw [along, ht, CharTwo.add_self_eq_zero]
  have hp : p = t • d := CharTwo.add_eq_zero.mp (quad_zero b hb _ h)
  apply hc
  rw [hp]
  change b * ((t * d.1) * d.2 + (t * d.2) * d.1) = 0
  rw [show t * d.2 * d.1 = t * d.1 * d.2 by ring, CharTwo.add_self_eq_zero, mul_zero]

theorem full_range {u : F} (hu : u ≠ 0) : (phi u 0).range = ⊤ := by
  apply AddMonoidHom.range_eq_top.mpr
  apply Finite.surjective_of_injective
  intro x y h
  change u * x ^ 2 + 0 * x = u * y ^ 2 + 0 * y at h
  simp only [zero_mul, add_zero, mul_right_inj' hu, pow_two] at h
  exact CharTwo.mul_self_injective h

theorem ker_iff {u c : F} (hu : u ≠ 0) (x : F) :
    x ∈ (phi u c).ker ↔ x = 0 ∨ x = c / u := by
  change u * x ^ 2 + c * x = 0 ↔ _
  rw [show u * x ^ 2 + c * x = x * (x * u + c) by ring, mul_eq_zero, CharTwo.add_eq_zero,
      eq_div_iff hu]

theorem range_two {u c : F} (hu : u ≠ 0) (hc : c ≠ 0) : (phi u c).range.index = 2 := by
  let f := phi u c
  have hk : Nat.card f.ker = 2 := by
    apply (Nat.card_eq_two_iff' (0 : f.ker)).mpr
    let y : f.ker := ⟨c / u, (ker_iff hu _).mpr (Or.inr rfl)⟩
    refine ⟨y, fun h => div_ne_zero hc hu (congrArg Subtype.val h), ?_⟩
    intro x hx
    apply Subtype.ext
    exact ((ker_iff hu x.val).mp x.property).resolve_left (fun h => hx (Subtype.ext h))
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := f.range))
  exact f.range.index_mul_card.trans (by simpa only [hk] using (AddSubgroup.card_ker_mul_card_range f).symm)

theorem translated (A : AddSubgroup F) (f : F →+ F) (q t₀ : F)
    (h₀ : q + f t₀ ∈ A) :
    Nat.card {t : F // q + f t ∈ A} = Nat.card (A.comap f) := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (Equiv.addRight t₀)
  intro t
  change q + f t ∈ A ↔ f (t + t₀) ∈ A
  rw [map_add, ← A.add_mem_cancel_left h₀]
  congr 1
  rw [show q + f t₀ + (q + f t) = (q + q) + (f t + f t₀) by abel, CharTwo.add_self_eq_zero, zero_add]

theorem card_comap (A : AddSubgroup F) (f : F →+ F) (hs : f.range ⊔ A = ⊤) :
    Nat.card (A.comap f) = Nat.card A := by
  have hi : (A.comap f).index = A.index := by
    rw [A.index_comap, ← AddSubgroup.relIndex_sup_right f.range A, hs, AddSubgroup.relIndex_top_right]
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (AddSubgroup.index_ne_zero_of_finite (H := A)))
  rw [← hi, AddSubgroup.card_mul_index, hi, AddSubgroup.card_mul_index]

theorem count_hit (b : F) (hb : ∀ x : F, x ^ 2 + b * x + 1 ≠ 0)
    (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F) (hd : d ≠ 0)
    (t₀ : F) (h₀ : quad b (p + t₀ • d) ∈ A) :
    (Finset.univ.filter fun t : F => quad b (p + t • d) ∈ A).card = Nat.card A := by
  let f := phi (quad b d) (cross b p d)
  have hw : quad b p + f t₀ ∈ A := by simpa only [along] using h₀
  have hu : quad b d ≠ 0 := fun h => hd (quad_zero b hb d h)
  have hs : f.range ⊔ A = ⊤ := by
    by_cases hc : cross b p d = 0
    · simp [f, hc, full_range hu]
    · have hi : f.range.index = 2 := range_two hu hc
      have hm := AddSubgroup.isCoatom_of_index_prime (hi ▸ Nat.prime_two)
      apply hm.2 _ (lt_of_le_of_ne le_sup_left ?_)
      intro he
      have hA : A ≤ f.range := sup_eq_left.mp he.symm
      have ht : f t₀ ∈ f.range := ⟨_, rfl⟩
      exact no_range b hb p d hc ((f.range.add_mem_cancel_right ht).mp (hA hw))
  classical
  calc
    _ = Nat.card {t : F // quad b (p + t • d) ∈ A} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card {t : F // quad b p + f t ∈ A} := Nat.card_congr
      (Equiv.subtypeEquivRight fun t => by rw [along])
    _ = Nat.card (A.comap f) := translated A f _ _ hw
    _ = Nat.card A := card_comap A f hs

end Gap664

open Gap664

theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  constructor
  · by_cases hh : ∃ t : F, quad b (p + t • d) ∈ A
    · obtain ⟨t, ht⟩ := hh
      exact Or.inr (count_hit b hb A p d hd t ht)
    · exact Or.inl (Finset.card_filter_eq_zero_iff.mpr fun t _ ht => hh ⟨t, ht⟩)
  · rintro rfl
    apply count_hit b hb A 0 d hd 0
    simp [quad]
