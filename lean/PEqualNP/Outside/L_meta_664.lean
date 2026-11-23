import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_664_aux

variable {F : Type} [Field F]

def Q (b : F) (p : F × F) := p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2

theorem anisotropic {b : F} (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0)
    (p : F × F) (hp : Q b p = 0) : p = 0 := by
  classical
  obtain ⟨x,y⟩ := p
  change x ^ 2 + b * x * y + y ^ 2 = 0 at hp
  by_cases hy : y = 0
  · subst y
    simp at hp
    simp [hp]
  · apply False.elim
    apply hb (x / y)
    field_simp
    linear_combination hp

def cross (b : F) (p d : F × F) := b * (p.1 * d.2 + p.2 * d.1)

variable [CharP F 2]

theorem expansion (b t : F) (p d : F × F) :
    Q b (p + t • d) = Q b p + (Q b d * t ^ 2 + cross b p d * t) := by
  change (p.1 + t * d.1) ^ 2 + b * (p.1 + t * d.1) * (p.2 + t * d.2) +
    (p.2 + t * d.2) ^ 2 = _
  rw [CharTwo.add_sq, CharTwo.add_sq]
  unfold Q cross
  ring

def poly (q c : F) : F →+ F where
  toFun t := q * t ^ 2 + c * t
  map_zero' := by simp
  map_add' x y := by rw [CharTwo.add_sq]; ring

theorem ker_two {q c : F} (hq : q ≠ 0) (hc : c ≠ 0) :
    Nat.card (poly q c).ker = 2 := by
  have hset : ((poly q c).ker : Set F) = {0, c / q} := by
    ext x
    change q * x ^ 2 + c * x = 0 ↔ x = 0 ∨ x = c / q
    rw [show q * x ^ 2 + c * x = x * (q * x + c) by ring, mul_eq_zero,
      add_eq_zero_iff_eq_neg, CharTwo.neg_eq, eq_div_iff hq, mul_comm q x]
  change (((poly q c).ker : Set F)).ncard = 2
  rw [hset, Set.ncard_pair (Ne.symm (div_ne_zero hc hq))]

variable [Fintype F] [DecidableEq F]

theorem count (f : F →+ F) (v : F) (A : AddSubgroup F) [DecidablePred (· ∈ A)]
    (hk : Nat.card f.ker = 2) (hv : v ∉ f.range) :
    (Finset.univ.filter (fun t => v + f t ∈ A)).card = 0 ∨
    (Finset.univ.filter (fun t => v + f t ∈ A)).card = Nat.card A := by
  classical
  have hi : f.range.index = 2 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := f.range))
    rw [AddSubgroup.index_mul_card, ← hk, AddSubgroup.card_ker_mul_card_range]
  have hout (t : F) : v + f t ∉ f.range := by
    rw [AddSubgroup.add_mem_iff_of_index_two hi]
    exact fun h => hv (h.mpr ⟨t,rfl⟩)
  by_cases hA : A ≤ f.range
  · left
    apply Finset.card_eq_zero.mpr
    exact Finset.filter_false_of_mem fun t _ h => hout t (hA h)
  right
  let B := Finset.univ.filter (fun a : F => a ∈ A)
  let S := B.filter (fun a => a ∉ f.range)
  have hB : B.card = Nat.card A := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype _).symm
  obtain ⟨a₀,ha₀,hn₀⟩ := IsConcreteLE.not_le_iff_exists.mp hA
  have hr : f.range.relIndex A = 2 := by
    apply AddSubgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
    refine ⟨a₀, ha₀, hn₀, fun a _ => ?_⟩
    rw [AddSubgroup.add_mem_iff_of_index_two hi]
    tauto
  have hI : (B.filter (fun a => a ∈ f.range)).card = Nat.card (f.range ⊓ A : AddSubgroup F) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext a
    simp [B, and_comm]
  have hS : S.card * 2 = Nat.card A := by
    have hsplit := B.card_filter_add_card_filter_not (fun a => a ∈ f.range)
    have hrel := f.range.relIndex_mul_card A
    rw [hr] at hrel
    change _ + S.card = _ at hsplit
    rw [hI, hB] at hsplit
    omega
  let g := fun t => v + f t
  have hcount : (Finset.univ.filter (fun t => v + f t ∈ A)).card =
      (Finset.univ.filter (fun t => g t ∈ S)).card := by
    congr 1
    ext t
    simp only [S, B, g, Finset.mem_filter, Finset.mem_univ, true_and, hout, not_false_eq_true, and_true]
  rw [hcount, ← Finset.sum_card_fiberwise_eq_card_filter, ← hS]
  apply Finset.sum_const_nat
  intro a ha
  have hna : a ∉ f.range := (Finset.mem_filter.mp ha).2
  have hhit : a - v ∈ f.range := by
    rw [sub_eq_add_neg, CharTwo.neg_eq, AddSubgroup.add_mem_iff_of_index_two hi]
    tauto
  have he : (Finset.univ.filter (fun t => g t = a)) =
      Finset.univ.filter (fun t => f t = a - v) := by
    ext t
    simp [g, eq_sub_iff_add_eq, add_comm]
  rw [he, AddMonoidHom.card_fiber_eq_of_mem_range f hhit (show (0 : F) ∈ Set.range f from
    ⟨0, map_zero f⟩), ← hk, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end PEqualNP.Outside.L_meta_664_aux

open PEqualNP.Outside.L_meta_664_aux

theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  let q := Q b d
  let c := cross b p d
  let v := Q b p
  let f := poly q c
  have hq : q ≠ 0 := fun h => hd (anisotropic hb d h)
  let N := (Finset.univ.filter (fun t : F => v + f t ∈ A)).card
  have hN : (Finset.univ.filter (fun t : F => Q b (p + t • d) ∈ A)).card = N := by
    unfold N
    congr 1
    ext t
    simp [expansion, v, f, poly, q, c]
  unfold Q at hN
  rw [hN]
  by_cases hc : c = 0
  · have hinj : Function.Injective (fun t => v + f t) := by
      intro x y h
      have hxy : x ^ 2 = y ^ 2 := by
        simpa [f, poly, hc, hq] using h
      have hsq : (x + y) ^ 2 = 0 := by rw [CharTwo.add_sq, hxy, CharTwo.add_self_eq_zero]
      have hz : x + y = 0 := by simpa using hsq
      simpa [CharTwo.neg_eq] using (add_eq_zero_iff_eq_neg.mp hz)
    let e := Equiv.ofBijective _ ((Finite.injective_iff_bijective).mp hinj)
    have hcard : N = Nat.card A := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      apply Finset.card_bij (fun t _ => e t)
      · intro t ht
        simpa [e] using ht
      · exact fun _ _ _ _ h => e.injective h
      · intro a ha
        refine ⟨e.symm a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply a⟩
        change e (e.symm a) ∈ A
        simpa using (Finset.mem_filter.mp ha).2
    exact ⟨Or.inr hcard, fun _ => hcard⟩
  · have hv : v ∉ f.range := by
      rintro ⟨t, ht⟩
      have hzero : Q b (p + t • d) = 0 := by
        rw [expansion]
        change v + f t = 0
        rw [ht, CharTwo.add_self_eq_zero]
      have he := anisotropic hb _ hzero
      have h1 : p.1 + t * d.1 = 0 := congrArg Prod.fst he
      have h2 : p.2 + t * d.2 = 0 := congrArg Prod.snd he
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h1 h2
      apply hc
      change b * (p.1 * d.2 + p.2 * d.1) = 0
      rw [h1, h2, show t * d.2 * d.1 = t * d.1 * d.2 by ring, CharTwo.add_self_eq_zero, mul_zero]
    refine ⟨count f v A (ker_two hq hc) hv, fun hp => (hc ?_).elim⟩
    simp [c, cross, hp]
