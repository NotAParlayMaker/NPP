import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_685

open Polynomial

def difference (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (m : F) : F →+ F where
  toFun x := x ^ p - m * x
  map_zero' := by simp [(Fact.out : p.Prime).ne_zero]
  map_add' x y := by rw [add_pow_char, mul_add]; ring

lemma kernel_card (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Fintype F]
    [CharP F p] (m : F) :
    Nat.card (difference p m).ker = 1 ∨ Nat.card (difference p m).ker = p := by
  let f := difference p m
  let P : F[X] := X ^ p - C m * X
  have hp : p.Prime := Fact.out
  have hdeg : P.natDegree = p := by
    have hlt : (C m * X : F[X]).natDegree < (X ^ p : F[X]).natDegree := by
      calc
        _ ≤ (X : F[X]).natDegree := natDegree_C_mul_le m X
        _ < _ := by simpa using hp.one_lt
    exact (natDegree_sub_eq_left_of_natDegree_lt hlt).trans (natDegree_X_pow p)
  have hne : P ≠ 0 := by
    intro he
    rw [he, natDegree_zero] at hdeg
    exact hp.ne_zero hdeg.symm
  have hroot : (f.ker : Set F) ⊆ P.rootSet F := by
    intro x hx
    apply (mem_rootSet_of_ne hne).mpr
    change x ^ p - m * x = 0 at hx
    simpa [P] using hx
  have hle : Nat.card f.ker ≤ p := by
    calc
      Nat.card f.ker = (f.ker : Set F).ncard := Nat.card_coe_set_eq _
      _ ≤ (P.rootSet F).ncard := Set.ncard_le_ncard hroot
      _ ≤ P.natDegree := P.ncard_rootSet_le F
      _ = p := hdeg
  have group : IsAddPGroup p F := by
    intro x
    exact ⟨1, by simp [nsmul_eq_mul, CharP.cast_eq_zero F p]⟩
  rcases (group.to_addSubgroup f.ker).card_eq_or_dvd with h | h
  · exact Or.inl h
  · exact Or.inr (le_antisymm hle (Nat.le_of_dvd Nat.card_pos h))

-- For an endomorphism of a finite abelian group, the size of the preimage of
-- a subgroup is its size times the index of its sum with the range.
lemma preimage_card {F : Type} [AddCommGroup F] [Finite F]
    (f : F →+ F) (A : AddSubgroup F) :
    Nat.card (A.comap f) = (f.range ⊔ A).index * Nat.card A := by
  have hidx : (A.comap f).index * (f.range ⊔ A).index = A.index := by
    rw [A.index_comap, ← AddSubgroup.relIndex_sup_right f.range A]
    exact AddSubgroup.relIndex_mul_index le_sup_right
  apply Nat.eq_of_mul_eq_mul_right (AddSubgroup.index_pos (H := A.comap f))
  calc
    Nat.card (A.comap f) * (A.comap f).index = Nat.card F := (A.comap f).card_mul_index
    _ = Nat.card A * A.index := A.card_mul_index.symm
    _ = _ := by rw [← hidx]; ac_rfl

lemma range_index {F : Type} [AddCommGroup F] [Finite F] (f : F →+ F) :
    f.range.index = Nat.card f.ker := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := f.range))
  rw [f.range.index_mul_card, ← AddSubgroup.index_ker f, f.ker.card_mul_index]

def translateFiber {F : Type} [AddCommGroup F] (f : F →+ F) (A : AddSubgroup F)
    (k x₀ : F) (hx₀ : f x₀ + k ∈ A) : {x : F // f x + k ∈ A} ≃ A.comap f where
  toFun x := ⟨x.val - x₀, by
    change f (x.val - x₀) ∈ A
    rw [map_sub]
    simpa only [add_sub_add_right_eq_sub] using A.sub_mem x.property hx₀⟩
  invFun y := ⟨y.val + x₀, by
    rw [map_add, add_assoc]
    exact A.add_mem y.property hx₀⟩
  left_inv x := Subtype.ext (sub_add_cancel _ _)
  right_inv y := Subtype.ext (add_sub_cancel_right _ _)

end PEqualNP.Outside.L_meta_685

open PEqualNP.Outside.L_meta_685


theorem PEqualNP.Outside.L_meta_685 : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (A : AddSubgroup F),
    (∀ a ∈ A, ∀ c : ZMod p, (ZMod.cast c : F) * a ∈ A) →
    ∀ m k : F,
      Nat.card {x : F // x ^ p - m * x + k ∈ A} = 0 ∨
      Nat.card {x : F // x ^ p - m * x + k ∈ A} = Nat.card A ∨
      Nat.card {x : F // x ^ p - m * x + k ∈ A} = p * Nat.card A := by
  intro p hp F _ _ _ A _ m k
  let f := difference p m
  change Nat.card {x : F // f x + k ∈ A} = 0 ∨
    Nat.card {x : F // f x + k ∈ A} = Nat.card A ∨
    Nat.card {x : F // f x + k ∈ A} = p * Nat.card A
  by_cases existsPoint : ∃ x : F, f x + k ∈ A
  · obtain ⟨x₀, hx₀⟩ := existsPoint
    have hcard := (Nat.card_congr (translateFiber f A k x₀ hx₀)).trans (preimage_card f A)
    have hd : (f.range ⊔ A).index ∣ Nat.card f.ker := by
      rw [← range_index]
      exact AddSubgroup.index_dvd_of_le le_sup_left
    have hindex : (f.range ⊔ A).index = 1 ∨ (f.range ⊔ A).index = p := by
      rcases kernel_card p m with h | h
      · exact Or.inl (Nat.dvd_one.mp (h ▸ hd))
      · exact (Nat.dvd_prime hp.out).mp (h ▸ hd)
    rcases hindex with h | h
    · exact Or.inr (Or.inl (by simpa only [h, one_mul] using hcard))
    · exact Or.inr (Or.inr (by simpa only [h] using hcard))
  · letI : IsEmpty {x : F // f x + k ∈ A} := ⟨fun x => existsPoint ⟨x.val, x.property⟩⟩
    exact Or.inl (by simp)
