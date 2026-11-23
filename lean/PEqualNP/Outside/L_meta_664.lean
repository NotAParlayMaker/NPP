import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta664

def Q {F : Type} [Field F] (b : F) (v : F × F) : F :=
  v.1 ^ 2 + b * v.1 * v.2 + v.2 ^ 2

lemma anisotropic {F : Type} [Field F] (b : F)
    (hb : ∀ x : F, x ^ 2 + b * x + 1 ≠ 0) (v : F × F)
    (hv : Q b v = 0) : v = 0 := by
  by_cases h : v.2 = 0
  · have hx : v.1 = 0 := by
      have : v.1 ^ 2 = 0 := by simpa [Q, h] using hv
      exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp this
    exact Prod.ext hx h
  · exfalso
    apply hb (v.1 / v.2)
    field_simp
    dsimp [Q] at hv
    linear_combination hv

lemma expansion {F : Type} [Field F] [CharP F 2] (b : F)
    (p d : F × F) (t : F) :
    Q b (p + t • d) = Q b p +
      (Q b d * t ^ 2 + (b * (p.1 * d.2 + d.1 * p.2)) * t) := by
  simp only [Q, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, CharTwo.add_sq]
  ring

def lineMap {F : Type} [Field F] [CharP F 2] (a c : F) : F →+ F where
  toFun t := a * t ^ 2 + c * t
  map_zero' := by simp
  map_add' x y := by simp only [CharTwo.add_sq]; ring

lemma kernel_zero {F : Type} [Field F] [CharP F 2] (a : F) (ha : a ≠ 0) :
    (lineMap a 0).ker = ⊥ := by
  ext t
  simp [lineMap, ha]

lemma kernel_two {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (a c : F) (ha : a ≠ 0) (hc : c ≠ 0) : Nat.card (lineMap a c).ker = 2 := by
  classical
  have hm (t : F) : t ∈ (lineMap a c).ker ↔ t = 0 ∨ t = c / a := by
    change a * t ^ 2 + c * t = 0 ↔ _
    rw [show a * t ^ 2 + c * t = t * (a * t + c) by ring, mul_eq_zero]
    congr 1
    rw [CharTwo.add_eq_iff_eq_add, zero_add, eq_div_iff ha]
    exact mul_comm a t ▸ Iff.rfl
  calc
    Nat.card (lineMap a c).ker = ({0, c / a} : Finset F).card :=
      Nat.subtype_card _ (fun t => by
        rw [Finset.mem_insert, Finset.mem_singleton]
        exact (hm t).symm)
    _ = 2 := by simp [Ne.symm (div_ne_zero hc ha)]

lemma comap_card {F : Type} [Field F] [Fintype F] (f : F →+ F)
    (A : AddSubgroup F) (hs : A ⊔ f.range = ⊤) :
    Nat.card (A.comap f) = Nat.card A := by
  have hi : (A.comap f).index = A.index := by
    rw [AddSubgroup.index_comap, ← AddSubgroup.relIndex_sup_left f.range A,
      hs, AddSubgroup.relIndex_top_right]
  have h₁ := (A.comap f).card_mul_index
  have h₂ := A.card_mul_index
  rw [hi] at h₁
  exact Nat.eq_of_mul_eq_mul_right A.index_pos (h₁.trans h₂.symm)

lemma sup_top {F : Type} [Field F] [Fintype F] (f : F →+ F)
    (hk : Nat.card f.ker = 2) (A : AddSubgroup F) (q : F)
    (hq : q ∈ A) (hn : q ∉ f.range) : A ⊔ f.range = ⊤ := by
  have hr : f.range.index = 2 := by rw [AddSubgroup.index_range, hk]
  have hd : (A ⊔ f.range).index ∣ 2 := by
    rw [← hr]
    exact AddSubgroup.index_dvd_of_le le_sup_right
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact AddSubgroup.index_eq_one.mp hi
  · have he : f.range = A ⊔ f.range :=
      AddSubgroup.eq_of_index_dvd_index le_sup_right (by rw [hr, hi])
    exact False.elim (hn (he.symm ▸ (show q ∈ A ⊔ f.range from (show A ≤ A ⊔ f.range from le_sup_left) hq)))

lemma shifted_card {F : Type} [Field F] [Fintype F]
    (f : F →+ F) (A : AddSubgroup F) (q t₀ : F) (ht : q + f t₀ ∈ A) :
    Nat.card {t : F // q + f t ∈ A} = Nat.card (A.comap f) := by
  apply Nat.card_congr
  exact {
    toFun := fun t => ⟨t.val - t₀, by
      change f (t.val - t₀) ∈ A
      convert A.sub_mem t.property ht using 1
      simp only [map_sub]
      abel⟩
    invFun := fun t => ⟨t.val + t₀, by
      convert A.add_mem ht t.property using 1
      simp only [map_add]
      abel⟩
    left_inv := fun t => by ext; simp
    right_inv := fun t => by ext; simp }

lemma offset_not_range {F : Type} [Field F] [CharP F 2] (b : F)
    (hb : ∀ x : F, x ^ 2 + b * x + 1 ≠ 0) (p d : F × F)
    (hc : b * (p.1 * d.2 + d.1 * p.2) ≠ 0) :
    Q b p ∉ (lineMap (Q b d) (b * (p.1 * d.2 + d.1 * p.2))).range := by
  rintro ⟨t, ht⟩
  have hz : Q b (p + t • d) = 0 := by
    rw [expansion]
    change Q b p + lineMap (Q b d) (b * (p.1 * d.2 + d.1 * p.2)) t = 0
    rw [ht, CharTwo.add_self_eq_zero]
  have hp := anisotropic b hb (p + t • d) hz
  have hx : p.1 + t * d.1 = 0 := congrArg Prod.fst hp
  have hy : p.2 + t * d.2 = 0 := congrArg Prod.snd hp
  have hx' : p.1 = t * d.1 := (CharTwo.add_eq_iff_eq_add.mp hx).trans (zero_add _)
  have hy' : p.2 = t * d.2 := (CharTwo.add_eq_iff_eq_add.mp hy).trans (zero_add _)
  apply hc
  rw [hx', hy', show t * d.1 * d.2 + d.1 * (t * d.2) =
    (t * d.1 * d.2) + (t * d.1 * d.2) by ring, CharTwo.add_self_eq_zero, mul_zero]

lemma line_count {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (b : F) (hb : ∀ x : F, x ^ 2 + b * x + 1 ≠ 0)
    (A : AddSubgroup F) (p d : F × F) (hd : d ≠ 0)
    (t₀ : F) (ht : Q b (p + t₀ • d) ∈ A) :
    Nat.card {t : F // Q b (p + t • d) ∈ A} = Nat.card A := by
  let a := Q b d
  let c := b * (p.1 * d.2 + d.1 * p.2)
  let f := lineMap a c
  have ha : a ≠ 0 := fun h => hd (anisotropic b hb d h)
  have hq : Q b p + f t₀ ∈ A := by simpa [f, a, c, lineMap, expansion] using ht
  have he : Nat.card {t : F // Q b (p + t • d) ∈ A} =
      Nat.card {t : F // Q b p + f t ∈ A} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro t
    simp [f, a, c, lineMap, expansion]
  rw [he, shifted_card f A (Q b p) t₀ hq]
  apply comap_card
  by_cases hc : c = 0
  · have hf : f.range = ⊤ := by
      apply AddSubgroup.index_eq_one.mp
      rw [AddSubgroup.index_range]
      change Nat.card (lineMap a c).ker = 1
      rw [hc, kernel_zero a ha]
      simp
    simp [hf]
  · have hn : Q b p ∉ f.range := offset_not_range b hb p d hc
    apply sup_top f (kernel_two a c ha hc) A (Q b p + f t₀) hq
    intro hh
    apply hn
    have hm : f t₀ ∈ f.range := ⟨t₀, rfl⟩
    convert f.range.sub_mem hh hm using 1
    abel

end PEqualNP.Outside.LMeta664

theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  classical
  have hc : (Finset.univ.filter (fun t : F =>
      (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 +
        (p + t • d).2 ^ 2 ∈ A)).card =
      Nat.card {t : F // PEqualNP.Outside.LMeta664.Q b (p + t • d) ∈ A} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  constructor
  · by_cases h : ∃ t : F, PEqualNP.Outside.LMeta664.Q b (p + t • d) ∈ A
    · obtain ⟨t, ht⟩ := h
      exact Or.inr (hc.trans (PEqualNP.Outside.LMeta664.line_count b hb A p d hd t ht))
    · left
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact h ⟨t, (Finset.mem_filter.mp ht).2⟩
  · intro hp
    apply hc.trans
    apply PEqualNP.Outside.LMeta664.line_count b hb A p d hd 0
    simp [hp, PEqualNP.Outside.LMeta664.Q]

