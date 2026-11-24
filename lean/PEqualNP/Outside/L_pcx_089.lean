import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_089

private def bitDifference (a b : Bool) : ℕ :=
  if a ≠ b then 1 else 0

private lemma hammingDist_eq_sum {n : ℕ} (x y : Fin n → Bool) :
    hammingDist x y = ∑ k, bitDifference (x k) (y k) := by
  exact (Finset.sum_boole (fun k => x k ≠ y k) Finset.univ).symm

private def bitWeight (a : Bool) : ℕ :=
  if a = true then 1 else 0

private lemma bit_weight_relation (a b : Bool) :
    bitWeight a + bitWeight b = bitDifference a b + 2 * bitWeight (a && b) := by
  cases a <;> cases b <;> decide

private lemma odd_distance {n : ℕ} (x y : Fin n → Bool)
    (hx : Odd (Finset.univ.filter (fun k => x k = true)).card)
    (hy : Even (Finset.univ.filter (fun k => y k = true)).card) :
    Odd (hammingDist x y) := by
  classical
  have hweight :
      (Finset.univ.filter (fun k => x k = true)).card +
        (Finset.univ.filter (fun k => y k = true)).card =
        hammingDist x y + 2 * (∑ k, bitWeight (x k && y k)) := by
    calc
      _ = ∑ k, (bitWeight (x k) + bitWeight (y k)) := by
        simp [bitWeight, Finset.sum_add_distrib]
      _ = ∑ k, (bitDifference (x k) (y k) + 2 * bitWeight (x k && y k)) :=
        Finset.sum_congr rfl fun k _ => bit_weight_relation (x k) (y k)
      _ = _ := by rw [Finset.sum_add_distrib, hammingDist_eq_sum, Finset.mul_sum]
  rw [Nat.odd_iff] at hx ⊢
  rw [Nat.even_iff] at hy
  omega

private def prefixCount {n : ℕ} (x y : Fin n → Bool) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n => k.val < i ∧ x k ≠ y k)).card

private lemma prefix_step {n i : ℕ} (x y : Fin n → Bool) (hi : i < n) :
    prefixCount x y (i + 1) = prefixCount x y i + bitDifference (x ⟨i, hi⟩) (y ⟨i, hi⟩) := by
  classical
  let k : Fin n := ⟨i, hi⟩
  change prefixCount x y (i + 1) = prefixCount x y i + bitDifference (x k) (y k)
  by_cases h : x k ≠ y k
  · have hinsert :
        Finset.univ.filter (fun j : Fin n => j.val < i + 1 ∧ x j ≠ y j) =
          insert k (Finset.univ.filter (fun j : Fin n => j.val < i ∧ x j ≠ y j)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hj : j = k
      · subst j
        simp [k, h]
      · have hval : j.val ≠ i := fun he => hj (Fin.ext he)
        have hlt : j.val < i + 1 ↔ j.val < i := by omega
        simp only [hlt, hj, false_or]
    have hk : k ∉ Finset.univ.filter (fun j : Fin n => j.val < i ∧ x j ≠ y j) := by
      simp [k]
    unfold prefixCount
    rw [hinsert, Finset.card_insert_of_notMem hk, bitDifference, ite_eq_left h]
  · have hsame :
        Finset.univ.filter (fun j : Fin n => j.val < i + 1 ∧ x j ≠ y j) =
          Finset.univ.filter (fun j : Fin n => j.val < i ∧ x j ≠ y j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hj : j = k
      · subst j
        simp [h]
      · have hval : j.val ≠ i := fun he => hj (Fin.ext he)
        have hlt : j.val < i + 1 ↔ j.val < i := by omega
        rw [hlt]
    unfold prefixCount
    rw [hsame, bitDifference, ite_eq_right h, Nat.add_zero]

private abbrev down {n : ℕ} (x y : Fin n → Bool) (i : ℕ) : Prop :=
  2 ≤ i ∧ Odd (prefixCount x y (i - 1)) ∧ ¬ Odd (prefixCount x y i)

private lemma half_prefix_eq_down_count {n : ℕ} (x y : Fin n → Bool) (m : ℕ)
    (hm : m ≤ n) :
    (prefixCount x y m) / 2 = ∑ i ∈ Finset.range (m + 1), if down x y i then 1 else 0 := by
  induction m with
  | zero =>
    change prefixCount x y 0 / 2 = ∑ i ∈ Finset.range 1, if down x y i then 1 else 0
    rw [Finset.sum_range_one]
    simp [prefixCount, down]
  | succ m ih =>
    have hlt : m < n := by omega
    have hstep := prefix_step x y hlt
    have hthreshold (hp : prefixCount x y m % 2 = 1) : 2 ≤ m + 1 := by
      by_contra! h
      have hm0 : m = 0 := by omega
      simp [hm0, prefixCount] at hp
    rw [Finset.sum_range_succ, ← ih (by omega)]
    change prefixCount x y (m + 1) / 2 = _
    simp only [down, Nat.add_sub_cancel, Nat.odd_iff]
    by_cases hb : x ⟨m, hlt⟩ ≠ y ⟨m, hlt⟩
    · rw [bitDifference, ite_eq_left hb] at hstep
      by_cases hp : prefixCount x y m % 2 = 1
      · have hd : 2 ≤ m + 1 ∧ prefixCount x y m % 2 = 1 ∧
            ¬ prefixCount x y (m + 1) % 2 = 1 := ⟨hthreshold hp, hp, by omega⟩
        rw [ite_eq_left hd]
        omega
      · simp [hp]
        omega
    · rw [bitDifference, ite_eq_right hb, Nat.add_zero] at hstep
      simp [hstep]

end PEqualNP.Outside.L_pcx_089

theorem PEqualNP.Outside.L_pcx_089 :
    ∀ (n : ℕ) (x y : Fin n → Bool),
      Odd (Finset.univ.filter (fun k => x k = true)).card →
      Even (Finset.univ.filter (fun k => y k = true)).card →
      hammingDist x y =
        2 * ((Finset.range n).filter (fun i => 2 ≤ i ∧
          Odd (Finset.univ.filter (fun k : Fin n => k.val < i - 1 ∧ x k ≠ y k)).card ∧
          ¬ Odd (Finset.univ.filter (fun k : Fin n => k.val < i ∧ x k ≠ y k)).card)).card + 1 := by
  intro n x y hx hy
  have hodd := L_pcx_089.odd_distance x y hx hy
  have htotal : L_pcx_089.prefixCount x y n = hammingDist x y := by
    simp [L_pcx_089.prefixCount, hammingDist]
  have hdown : ¬ L_pcx_089.down x y n := by
    simp [L_pcx_089.down, htotal, hodd]
  have hcount := L_pcx_089.half_prefix_eq_down_count x y n le_rfl
  rw [htotal, Finset.sum_range_succ, ite_eq_right hdown, Nat.add_zero, Finset.sum_boole] at hcount
  change hammingDist x y = 2 * ((Finset.range n).filter (L_pcx_089.down x y)).card + 1
  have hcard : hammingDist x y / 2 = ((Finset.range n).filter (L_pcx_089.down x y)).card :=
    hcount
  rw [← hcard]
  rw [Nat.odd_iff] at hodd
  omega
