import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_232

open PEqualNP.MetaComplexity

abbrev Word := Fin 4 → Bool

def parity (x : Word) : Bool := xor (xor (xor (x 0) (x 1)) (x 2)) (x 3)

def word (k : ℕ) : Word := fun i => k.testBit i.val

def charge (n i : ℕ) : ℕ := if n = i then 1 else 0

lemma rankTwo {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (x y u v : α)
    (h1 : M x u = 1) (h2 : M y v = 1) (hz : M x v = 0) : 2 ≤ M.rank := by
  have hs : (M.submatrix ![x, y] ![u, v]).rank = 2 := by
    rw [Matrix.rank_of_isUnit]
    · simp
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two]
      simp [h1, h2, hz]
  exact hs ▸ M.rank_submatrix_le ![x, y] ![u, v]

lemma rankThree {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (r c : Fin 3 → α) (hd : ∀ j, M (r j) (c j) = 1)
    (h01 : M (r 0) (c 1) = 0) (h02 : M (r 0) (c 2) = 0)
    (h12 : M (r 1) (c 2) = 0) : 3 ≤ M.rank := by
  have hs : (M.submatrix r c).rank = 3 := by
    rw [Matrix.rank_of_isUnit]
    · simp
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_three]
      simp [Matrix.submatrix_apply, hd, h01, h02, h12]
  exact hs ▸ M.rank_submatrix_le r c

lemma triangle {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (r c : Fin 3 → α) (a b d i : ℕ)
    (hd : ∀ j, M (r j) (c j) = 1)
    (h01 : M (r 0) (c 1) = if a = i then 1 else 0)
    (h02 : M (r 0) (c 2) = if b = i then 1 else 0)
    (h12 : M (r 1) (c 2) = if d = i then 1 else 0) :
    3 ≤ M.rank + charge a i + charge b i + charge d i := by
  have za (h : a ≠ i) := rankTwo M _ _ _ _ (hd 0) (hd 1) (by simpa [h] using h01)
  have zb (h : b ≠ i) := rankTwo M _ _ _ _ (hd 0) (hd 2) (by simpa [h] using h02)
  have zd (h : d ≠ i) := rankTwo M _ _ _ _ (hd 1) (hd 2) (by simpa [h] using h12)
  have z3 (ha : a ≠ i) (hb : b ≠ i) (hd' : d ≠ i) := rankThree M r c hd
    (by simpa [ha] using h01) (by simpa [hb] using h02) (by simpa [hd'] using h12)
  by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hd' : d = i <;>
    simp_all [charge] <;> omega

abbrev Matched (i : Fin 4) (b : Bool) (x y : Word) :=
  parity x = true ∧ parity y = false ∧ x i = b ∧ ∀ j : Fin 4, x j ≠ y j → j = i

lemma literal (τ : Word → Word → ℕ) (ht : IsTyping 4 parity τ) (i : Fin 4) (b : Bool)
    (r c : Fin 4 → Word) (hm : ∀ j, Matched i b (r j) (c j))
    (p q s : Fin 4) :
    3 ≤ (typedMatrix 4 parity τ i b).rank + charge (τ (r p) (c q)) i +
      charge (τ (r p) (c s)) i + charge (τ (r q) (c s)) i := by
  let M := typedMatrix 4 parity τ i b
  have diag (j : Fin 4) : M (r j) (c j) = 1 := by
    obtain ⟨hx, hy, hb, hu⟩ := hm j
    obtain ⟨k, hk, hne⟩ := ht _ _ hx hy
    have he : τ (r j) (c j) = i := (hu k hne) ▸ hk
    simp [M, typedMatrix, hx, hy, hb, he]
  have entry (j k : Fin 4) : M (r j) (c k) =
      if τ (r j) (c k) = i then 1 else 0 := by
    simp [M, typedMatrix, (hm j).1, (hm k).2.1, (hm j).2.2.1]
  apply triangle M ![r p, r q, r s] ![c p, c q, c s] _ _ _ i
  · intro j
    fin_cases j <;> apply diag
  · exact entry p q
  · exact entry p s
  · exact entry q s

lemma uniqueCharge (n i j k : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    charge n i + charge n j + charge n k ≤ 1 := by
  unfold charge
  split_ifs <;> omega


lemma block (τ : Word → Word → ℕ) (ht : IsTyping 4 parity τ) (i : Fin 4) (b : Bool)
    (r c : Fin 4 → Word) (hm : ∀ j, Matched i b (r j) (c j)) :
    12 ≤ 4 * (typedMatrix 4 parity τ i b).rank +
      charge (τ (r 0) (c 1)) i + charge (τ (r 0) (c 2)) i +
      charge (τ (r 0) (c 3)) i + charge (τ (r 1) (c 0)) i +
      charge (τ (r 1) (c 2)) i + charge (τ (r 1) (c 3)) i +
      charge (τ (r 2) (c 0)) i + charge (τ (r 2) (c 1)) i +
      charge (τ (r 2) (c 3)) i + charge (τ (r 3) (c 0)) i +
      charge (τ (r 3) (c 1)) i + charge (τ (r 3) (c 2)) i := by
  have t0 := literal τ ht i b r c hm 0 1 2
  have t1 := literal τ ht i b r c hm 1 0 3
  have t2 := literal τ ht i b r c hm 2 3 0
  have t3 := literal τ ht i b r c hm 3 2 1
  omega

lemma lower : ¬ HasTypedRank 4 parity 15 := by
  rintro ⟨τ, ht, hsum⟩
  simp only [Fin.sum_univ_four, Fintype.sum_bool] at hsum
  let pair (x y : ℕ) := τ (word x) (word y)
  have h0f : 12 ≤ 4 * (typedMatrix 4 parity τ 0 false).rank +
      charge (pair 2 5) 0 + charge (pair 2 9) 0 + charge (pair 2 15) 0 +
      charge (pair 4 3) 0 + charge (pair 4 9) 0 + charge (pair 4 15) 0 +
      charge (pair 8 3) 0 + charge (pair 8 5) 0 + charge (pair 8 15) 0 +
      charge (pair 14 3) 0 + charge (pair 14 5) 0 + charge (pair 14 9) 0 :=
    block τ ht 0 false ![word 2, word 4, word 8, word 14] ![word 3, word 5, word 9, word 15] (by decide)
  have h0t : 12 ≤ 4 * (typedMatrix 4 parity τ 0 true).rank +
      charge (pair 1 6) 0 + charge (pair 1 10) 0 + charge (pair 1 12) 0 +
      charge (pair 7 0) 0 + charge (pair 7 10) 0 + charge (pair 7 12) 0 +
      charge (pair 11 0) 0 + charge (pair 11 6) 0 + charge (pair 11 12) 0 +
      charge (pair 13 0) 0 + charge (pair 13 6) 0 + charge (pair 13 10) 0 :=
    block τ ht 0 true ![word 1, word 7, word 11, word 13] ![word 0, word 6, word 10, word 12] (by decide)
  have h1f : 12 ≤ 4 * (typedMatrix 4 parity τ 1 false).rank +
      charge (pair 1 6) 1 + charge (pair 1 10) 1 + charge (pair 1 15) 1 +
      charge (pair 4 3) 1 + charge (pair 4 10) 1 + charge (pair 4 15) 1 +
      charge (pair 8 3) 1 + charge (pair 8 6) 1 + charge (pair 8 15) 1 +
      charge (pair 13 3) 1 + charge (pair 13 6) 1 + charge (pair 13 10) 1 :=
    block τ ht 1 false ![word 1, word 4, word 8, word 13] ![word 3, word 6, word 10, word 15] (by decide)
  have h1t : 12 ≤ 4 * (typedMatrix 4 parity τ 1 true).rank +
      charge (pair 2 5) 1 + charge (pair 2 9) 1 + charge (pair 2 12) 1 +
      charge (pair 7 0) 1 + charge (pair 7 9) 1 + charge (pair 7 12) 1 +
      charge (pair 11 0) 1 + charge (pair 11 5) 1 + charge (pair 11 12) 1 +
      charge (pair 14 0) 1 + charge (pair 14 5) 1 + charge (pair 14 9) 1 :=
    block τ ht 1 true ![word 2, word 7, word 11, word 14] ![word 0, word 5, word 9, word 12] (by decide)
  have h2f : 12 ≤ 4 * (typedMatrix 4 parity τ 2 false).rank +
      charge (pair 1 6) 2 + charge (pair 1 12) 2 + charge (pair 1 15) 2 +
      charge (pair 2 5) 2 + charge (pair 2 12) 2 + charge (pair 2 15) 2 +
      charge (pair 8 5) 2 + charge (pair 8 6) 2 + charge (pair 8 15) 2 +
      charge (pair 11 5) 2 + charge (pair 11 6) 2 + charge (pair 11 12) 2 :=
    block τ ht 2 false ![word 1, word 2, word 8, word 11] ![word 5, word 6, word 12, word 15] (by decide)
  have h2t : 12 ≤ 4 * (typedMatrix 4 parity τ 2 true).rank +
      charge (pair 4 3) 2 + charge (pair 4 9) 2 + charge (pair 4 10) 2 +
      charge (pair 7 0) 2 + charge (pair 7 9) 2 + charge (pair 7 10) 2 +
      charge (pair 13 0) 2 + charge (pair 13 3) 2 + charge (pair 13 10) 2 +
      charge (pair 14 0) 2 + charge (pair 14 3) 2 + charge (pair 14 9) 2 :=
    block τ ht 2 true ![word 4, word 7, word 13, word 14] ![word 0, word 3, word 9, word 10] (by decide)
  have h3f : 12 ≤ 4 * (typedMatrix 4 parity τ 3 false).rank +
      charge (pair 1 10) 3 + charge (pair 1 12) 3 + charge (pair 1 15) 3 +
      charge (pair 2 9) 3 + charge (pair 2 12) 3 + charge (pair 2 15) 3 +
      charge (pair 4 9) 3 + charge (pair 4 10) 3 + charge (pair 4 15) 3 +
      charge (pair 7 9) 3 + charge (pair 7 10) 3 + charge (pair 7 12) 3 :=
    block τ ht 3 false ![word 1, word 2, word 4, word 7] ![word 9, word 10, word 12, word 15] (by decide)
  have h3t : 12 ≤ 4 * (typedMatrix 4 parity τ 3 true).rank +
      charge (pair 8 3) 3 + charge (pair 8 5) 3 + charge (pair 8 6) 3 +
      charge (pair 11 0) 3 + charge (pair 11 5) 3 + charge (pair 11 6) 3 +
      charge (pair 13 0) 3 + charge (pair 13 3) 3 + charge (pair 13 6) 3 +
      charge (pair 14 0) 3 + charge (pair 14 3) 3 + charge (pair 14 5) 3 :=
    block τ ht 3 true ![word 8, word 11, word 13, word 14] ![word 0, word 3, word 5, word 6] (by decide)
  have counted := (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h0f h0t) (Nat.add_le_add h1f h1t)) (Nat.add_le_add (Nat.add_le_add h2f h2t) (Nat.add_le_add h3f h3t)))
  have cap (x y : ℕ) (i j k : ℕ) (h : i ≠ j ∧ i ≠ k ∧ j ≠ k) :=
    uniqueCharge (pair x y) i j k h.1 h.2.1 h.2.2
  have available := (Nat.add_le_add
      (Nat.add_le_add
      (Nat.add_le_add
      (Nat.add_le_add
      (Nat.add_le_add (cap 1 6 0 1 2 (by decide)) (cap 1 10 0 1 3 (by decide)))
      (Nat.add_le_add (cap 1 12 0 2 3 (by decide)) (cap 1 15 1 2 3 (by decide))))
      (Nat.add_le_add
      (Nat.add_le_add (cap 2 5 0 1 2 (by decide)) (cap 2 9 0 1 3 (by decide)))
      (Nat.add_le_add (cap 2 12 1 2 3 (by decide)) (cap 2 15 0 2 3 (by decide)))))
      (Nat.add_le_add
      (Nat.add_le_add
      (Nat.add_le_add (cap 4 3 0 1 2 (by decide)) (cap 4 9 0 2 3 (by decide)))
      (Nat.add_le_add (cap 4 10 1 2 3 (by decide)) (cap 4 15 0 1 3 (by decide))))
      (Nat.add_le_add
      (Nat.add_le_add (cap 7 0 0 1 2 (by decide)) (cap 7 9 1 2 3 (by decide)))
      (Nat.add_le_add (cap 7 10 0 2 3 (by decide)) (cap 7 12 0 1 3 (by decide))))))
      (Nat.add_le_add
      (Nat.add_le_add
      (Nat.add_le_add
      (Nat.add_le_add (cap 8 3 0 1 3 (by decide)) (cap 8 5 0 2 3 (by decide)))
      (Nat.add_le_add (cap 8 6 1 2 3 (by decide)) (cap 8 15 0 1 2 (by decide))))
      (Nat.add_le_add
      (Nat.add_le_add (cap 11 0 0 1 3 (by decide)) (cap 11 5 1 2 3 (by decide)))
      (Nat.add_le_add (cap 11 6 0 2 3 (by decide)) (cap 11 12 0 1 2 (by decide)))))
      (Nat.add_le_add
      (Nat.add_le_add
      (Nat.add_le_add (cap 13 0 0 2 3 (by decide)) (cap 13 3 1 2 3 (by decide)))
      (Nat.add_le_add (cap 13 6 0 1 3 (by decide)) (cap 13 10 0 1 2 (by decide))))
      (Nat.add_le_add
      (Nat.add_le_add (cap 14 0 1 2 3 (by decide)) (cap 14 3 0 2 3 (by decide)))
      (Nat.add_le_add (cap 14 5 0 1 3 (by decide)) (cap 14 9 0 1 2 (by decide)))))))
  clear h0f h0t h1f h1t h2f h2t h3f h3t cap
  omega

end PEqualNP.Outside.L_meta_232

theorem PEqualNP.Outside.L_meta_232 : ¬ PEqualNP.MetaComplexity.HasTypedRank 4 (fun x : Fin 4 → Bool => xor (xor (xor (x 0) (x 1)) (x 2)) (x 3)) 15 :=
  PEqualNP.Outside.L_meta_232.lower
