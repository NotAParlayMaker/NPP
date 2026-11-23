import Mathlib

namespace PEqualNP.Outside.L_meta_664_aux

variable {F : Type} [Field F]

def Q (b : F) (v : F × F) : F := v.1 ^ 2 + b * v.1 * v.2 + v.2 ^ 2

def C (b : F) (p d : F × F) : F := b * (p.1 * d.2 + p.2 * d.1)

def g [CharP F 2] (q c : F) : F →+ F where
  toFun t := q * t ^ 2 + c * t
  map_zero' := by simp
  map_add' s t := by
    show q * (s + t) ^ 2 + c * (s + t) = (q * s ^ 2 + c * s) + (q * t ^ 2 + c * t)
    rw [CharTwo.add_sq]
    ring

theorem g_apply [CharP F 2] (q c t : F) : g q c t = q * t ^ 2 + c * t := rfl

theorem aniso (b : F) (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) (v : F × F)
    (h : Q b v = 0) : v = 0 := by
  unfold Q at h
  by_cases hy : v.2 = 0
  · rw [hy] at h
    have hx : v.1 = 0 := by simpa using h
    exact Prod.ext hx hy
  · exfalso
    have e : (v.1 / v.2) ^ 2 + b * (v.1 / v.2) + 1
        = (v.1 ^ 2 + b * v.1 * v.2 + v.2 ^ 2) / v.2 ^ 2 := by
      field_simp
    exact hb (v.1 / v.2) (by rw [e, h, zero_div])

theorem line_val [CharP F 2] (b : F) (p d : F × F) (t : F) :
    (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2
      = g (Q b d) (C b p d) t + Q b p := by
  rw [g_apply]
  unfold Q C
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (p.1 * t * d.1 + p.2 * t * d.2) * h2

theorem card_coset [Fintype F] [DecidableEq F] (f : F →+ F) (A : AddSubgroup F)
    [DecidablePred (· ∈ A)] (r t0 : F) (h0 : f t0 + r ∈ A) :
    (Finset.univ.filter (fun t => f t + r ∈ A)).card = Nat.card (A.comap f) := by
  have e : {t // t ∈ Finset.univ.filter (fun t => f t + r ∈ A)} ≃ (A.comap f) :=
    { toFun := fun x => ⟨x.1 - t0, by
        have hx : f x.1 + r ∈ A := (Finset.mem_filter.1 x.2).2
        rw [AddSubgroup.mem_comap, map_sub]
        have hs := A.sub_mem hx h0
        convert hs using 1
        abel⟩
      invFun := fun y => ⟨y.1 + t0, by
        have hy : f y.1 ∈ A := AddSubgroup.mem_comap.1 y.2
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        rw [map_add, add_assoc]
        exact A.add_mem hy h0⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem card_comap_eq [Finite F] (f : F →+ F) (A : AddSubgroup F)
    (h : f.range = ⊤ ∨ (Nat.card f.ker = 2 ∧ ¬ A ≤ f.range)) :
    Nat.card (A.comap f) = Nat.card A := by
  have hidx : (A.comap f).index = A.index := by
    rw [AddSubgroup.index_comap]
    rcases h with h | ⟨hk, hA⟩
    · rw [h, AddSubgroup.relIndex_top_right]
    · have hR : f.range.index = 2 := by
        rw [AddSubgroup.index_range, hk]
      have h1 : f.range.relIndex A = 2 := by
        have hd : f.range.relIndex A ∣ 2 :=
          hR ▸ AddSubgroup.relIndex_dvd_index_of_normal (H := f.range) (K := A)
        have hne : f.range.relIndex A ≠ 1 := fun e => hA (AddSubgroup.relIndex_eq_one.1 e)
        rcases (Nat.dvd_prime Nat.prime_two).1 hd with e | e
        · exact absurd e hne
        · exact e
      have e1 := AddSubgroup.index_inf (H := A) (K := f.range)
      have e2 := AddSubgroup.index_inf (H := f.range) (K := A)
      rw [inf_comm, e1, hR, h1] at e2
      omega
  have c1 := AddSubgroup.card_mul_index (A.comap f)
  have c2 := AddSubgroup.card_mul_index A
  rw [hidx] at c1
  have hA0 : A.index ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hA0) (c1.trans c2.symm)

theorem range_top [CharP F 2] [Finite F] (q : F) (hq : q ≠ 0) : (g q 0).range = ⊤ := by
  rw [AddMonoidHom.range_eq_top]
  apply Finite.injective_iff_surjective.1
  intro s t hst
  rw [g_apply, g_apply] at hst
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : q * (s + t) ^ 2 = 0 := by
    rw [CharTwo.add_sq]
    linear_combination hst + q * t ^ 2 * h2
  have hst0 : s + t = 0 := by
    rcases mul_eq_zero.1 hsq with h | h
    · exact absurd h hq
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
  linear_combination hst0 - t * h2

theorem ker_card [CharP F 2] (q c : F) (hq : q ≠ 0) (hc : c ≠ 0) : Nat.card (g q c).ker = 2 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hk : c / q ∈ (g q c).ker := by
    rw [AddMonoidHom.mem_ker, g_apply]
    have e : q * (c / q) ^ 2 + c * (c / q) = 2 * (c ^ 2 / q) := by
      field_simp
      ring
    rw [e, h2, zero_mul]
  rw [Nat.card_eq_two_iff]
  refine ⟨0, ⟨c / q, hk⟩, ?_, ?_⟩
  · intro e
    have e' : (0 : F) = c / q := congrArg Subtype.val e
    exact hc (by
      have := (div_eq_zero_iff.1 e'.symm)
      rcases this with h | h
      · exact h
      · exact absurd h hq)
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have hz : q * z.1 ^ 2 + c * z.1 = 0 := by
      have := z.2
      rw [AddMonoidHom.mem_ker, g_apply] at this
      exact this
    have hm : z.1 * (q * z.1 + c) = 0 := by linear_combination hz
    rcases mul_eq_zero.1 hm with h | h
    · left
      exact Subtype.ext h
    · right
      apply Subtype.ext
      show z.1 = c / q
      rw [eq_div_iff hq]
      linear_combination h - c * h2

theorem main [CharP F 2] [Fintype F] [DecidableEq F] (b : F) (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0)
    (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F) (hd : d ≠ 0) (t0 : F)
    (h0 : g (Q b d) (C b p d) t0 + Q b p ∈ A) :
    (Finset.univ.filter (fun t => g (Q b d) (C b p d) t + Q b p ∈ A)).card = Nat.card A := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hq : Q b d ≠ 0 := fun e => hd (aniso b hb d e)
  rw [card_coset _ A _ t0 h0]
  apply card_comap_eq
  by_cases hc : C b p d = 0
  · left
    rw [hc]
    exact range_top _ hq
  · right
    refine ⟨ker_card _ _ hq hc, ?_⟩
    intro hle
    obtain ⟨s, hs⟩ := AddMonoidHom.mem_range.1 (hle h0)
    have hz : Q b (p + (s - t0) • d) = 0 := by
      have e := line_val b p d (s - t0)
      rw [map_sub, hs] at e
      show (p + (s - t0) • d).1 ^ 2 + b * (p + (s - t0) • d).1 * (p + (s - t0) • d).2
        + (p + (s - t0) • d).2 ^ 2 = 0
      rw [e]
      linear_combination (Q b p) * h2
    have hv := aniso b hb _ hz
    have hv1 : p.1 + (s - t0) * d.1 = 0 := by
      have := congrArg Prod.fst hv
      simpa using this
    have hv2 : p.2 + (s - t0) * d.2 = 0 := by
      have := congrArg Prod.snd hv
      simpa using this
    apply hc
    unfold C
    linear_combination b * d.2 * hv1 + b * d.1 * hv2 - b * (s - t0) * d.1 * d.2 * h2

end PEqualNP.Outside.L_meta_664_aux

open PEqualNP.Outside.L_meta_664_aux in
theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  simp only [line_val b p d]
  refine ⟨?_, ?_⟩
  · by_cases hne : ∃ t0, g (Q b d) (C b p d) t0 + Q b p ∈ A
    · right
      obtain ⟨t0, h0⟩ := hne
      exact main b hb A p d hd t0 h0
    · left
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t _ ht
      exact hne ⟨t, ht⟩
  · intro hp
    subst hp
    apply main b hb A 0 d hd 0
    simp [Q]
