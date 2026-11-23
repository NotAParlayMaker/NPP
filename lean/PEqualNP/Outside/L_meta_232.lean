import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_232

def ent (p : Bool) : ℚ := if p then 1 else 0

def bm (P : Fin 4 → Fin 4 → Bool) : Matrix (Fin 4) (Fin 4) ℚ := Matrix.of fun k l => ent (P k l)

def ei (p : Bool) : ℤ := if p then 1 else 0

def det3 (P : Fin 4 → Fin 4 → Bool) (s : Fin 3 → Fin 4) : ℤ :=
  ei (P (s 0) (s 0)) * ei (P (s 1) (s 1)) * ei (P (s 2) (s 2))
  - ei (P (s 0) (s 0)) * ei (P (s 1) (s 2)) * ei (P (s 2) (s 1))
  - ei (P (s 0) (s 1)) * ei (P (s 1) (s 0)) * ei (P (s 2) (s 2))
  + ei (P (s 0) (s 1)) * ei (P (s 1) (s 2)) * ei (P (s 2) (s 0))
  + ei (P (s 0) (s 2)) * ei (P (s 1) (s 0)) * ei (P (s 2) (s 1))
  - ei (P (s 0) (s 2)) * ei (P (s 1) (s 1)) * ei (P (s 2) (s 0))

lemma ent_eq (p : Bool) : ent p = ((ei p : ℤ) : ℚ) := by
  cases p <;> simp [ent, ei]

lemma rank_ge3 (P : Fin 4 → Fin 4 → Bool) (s : Fin 3 → Fin 4) (h : det3 P s ≠ 0) :
    3 ≤ (bm P).rank := by
  have hd : ((bm P).submatrix s s).det ≠ 0 := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.submatrix_apply, bm, Matrix.of_apply, ent_eq]
    intro h0
    apply h
    unfold det3
    exact_mod_cast h0
  have hr : ((bm P).submatrix s s).rank = 3 := by
    rw [Matrix.rank_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)]
    simp
  rw [← hr]
  exact Matrix.rank_submatrix_le _ _ _

lemma rank_ge2 (P : Fin 4 → Fin 4 → Bool) (hP : ∀ k, P k k = true) (k l : Fin 4)
    (h : P k l = false) : 2 ≤ (bm P).rank := by
  have hd : ((bm P).submatrix ![k, l] ![k, l]).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [bm, ent, hP, h]
  have hr : ((bm P).submatrix ![k, l] ![k, l]).rank = 2 := by
    rw [Matrix.rank_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)]
    simp
  rw [← hr]
  exact Matrix.rank_submatrix_le _ _ _

lemma rank_ge1 (P : Fin 4 → Fin 4 → Bool) (hP : ∀ k, P k k = true) : 1 ≤ (bm P).rank := by
  have hd : ((bm P).submatrix ![0] ![0]).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    simp [bm, ent, hP]
  have hr : ((bm P).submatrix ![(0 : Fin 4)] ![0]).rank = 1 := by
    rw [Matrix.rank_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)]
    simp
  rw [← hr]
  exact Matrix.rank_submatrix_le _ _ _

def cnt (P : Fin 4 → Fin 4 → Bool) : ℕ := ∑ k : Fin 4, ∑ l : Fin 4, if P k l then 1 else 0

def mk (a01 a02 a03 a10 a12 a13 a20 a21 a23 a30 a31 a32 : Bool) : Fin 4 → Fin 4 → Bool :=
  ![![true, a01, a02, a03], ![a10, true, a12, a13], ![a20, a21, true, a23], ![a30, a31, a32, true]]

def Lb (P : Fin 4 → Fin 4 → Bool) : ℕ :=
  if det3 P ![1, 2, 3] ≠ 0 ∨ det3 P ![0, 2, 3] ≠ 0 ∨ det3 P ![0, 1, 3] ≠ 0 ∨ det3 P ![0, 1, 2] ≠ 0
  then 3 else if ∃ k l : Fin 4, P k l = false then 2 else 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma key : ∀ a01 a02 a03 a10 a12 a13 a20 a21 a23 a30 a31 a32 : Bool,
    16 ≤ 4 * Lb (mk a01 a02 a03 a10 a12 a13 a20 a21 a23 a30 a31 a32)
      + cnt (mk a01 a02 a03 a10 a12 a13 a20 a21 a23 a30 a31 a32) := by
  decide +kernel


lemma mk_eq (P : Fin 4 → Fin 4 → Bool) (hP : ∀ k, P k k = true) :
    P = mk (P 0 1) (P 0 2) (P 0 3) (P 1 0) (P 1 2) (P 1 3) (P 2 0) (P 2 1) (P 2 3)
      (P 3 0) (P 3 1) (P 3 2) := by
  funext k l
  fin_cases k <;> fin_cases l <;> simp [mk, hP]

lemma Lb_le (P : Fin 4 → Fin 4 → Bool) (hP : ∀ k, P k k = true) : Lb P ≤ (bm P).rank := by
  unfold Lb
  split_ifs with h1 h2
  · rcases h1 with h | h | h | h <;> exact rank_ge3 P _ h
  · obtain ⟨k, l, h⟩ := h2
    exact rank_ge2 P hP k l h
  · exact rank_ge1 P hP

lemma core (P : Fin 4 → Fin 4 → Bool) (hP : ∀ k, P k k = true) :
    16 ≤ 4 * (bm P).rank + cnt P := by
  have hk := key (P 0 1) (P 0 2) (P 0 3) (P 1 0) (P 1 2) (P 1 3) (P 2 0) (P 2 1) (P 2 3)
      (P 3 0) (P 3 1) (P 3 2)
  rw [← mk_eq P hP] at hk
  have := Lb_le P hP
  omega

def F : (Fin 4 → Bool) → Bool := fun x => xor (xor (xor (x 0) (x 1)) (x 2)) (x 3)

def allx : List (Fin 4 → Bool) := (List.finRange 16).map fun m => fun j => Nat.testBit m j

def rows (i : Fin 4) (b : Bool) (k : Fin 4) : Fin 4 → Bool :=
  (allx.filter fun x => F x && (x i == b)).getD k (fun _ => false)

def cols (i : Fin 4) (b : Bool) (k : Fin 4) : Fin 4 → Bool :=
  Function.update (rows i b k) i (!b)

set_option maxRecDepth 100000 in
lemma facts : ∀ i : Fin 4, ∀ b : Bool, ∀ k : Fin 4, F (rows i b k) = true ∧ rows i b k i = b ∧
    F (cols i b k) = false ∧ (∀ j : Fin 4, rows i b k j ≠ cols i b k j → j = i) := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma inj : ∀ i : Fin 4, ∀ b : Bool, ∀ k l : Fin 4, (rows i b k = rows i b l → k = l) ∧
    (cols i b k = cols i b l → k = l) := by
  decide +kernel

lemma sum_inj_le {α : Type} [Fintype α] [DecidableEq α] (r : Fin 4 → α)
    (hr : ∀ k l, r k = r l → k = l) (g : α → ℕ) : ∑ k, g (r k) ≤ ∑ x, g x := by
  calc ∑ k, g (r k) = ∑ x ∈ Finset.univ.image r, g x := by
        rw [Finset.sum_image (fun a _ b _ h => hr a b h)]
    _ ≤ ∑ x, g x := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def N (τ : (Fin 4 → Bool) → (Fin 4 → Bool) → ℕ) (i : Fin 4) (b : Bool) : ℕ :=
  ∑ x : Fin 4 → Bool, ∑ y : Fin 4 → Bool,
    if F x = true ∧ F y = false ∧ τ x y = (i : ℕ) ∧ x i = b then 1 else 0

lemma lit (τ : (Fin 4 → Bool) → (Fin 4 → Bool) → ℕ)
    (hτ : PEqualNP.MetaComplexity.IsTyping 4 F τ) (i : Fin 4) (b : Bool) :
    16 ≤ 4 * (PEqualNP.MetaComplexity.typedMatrix 4 F τ i b).rank + N τ i b := by
  let P : Fin 4 → Fin 4 → Bool := fun k l => decide (τ (rows i b k) (cols i b l) = (i : ℕ))
  have hP : ∀ k, P k k = true := by
    intro k
    obtain ⟨h1, -, h3, h4⟩ := facts i b k
    obtain ⟨j, hj, hne⟩ := hτ (rows i b k) (cols i b k) h1 h3
    have := h4 j hne
    subst this
    simp [P, hj]
  have hsub : (PEqualNP.MetaComplexity.typedMatrix 4 F τ i b).submatrix (rows i b) (cols i b)
      = bm P := by
    ext k l
    obtain ⟨h1, h2, -, -⟩ := facts i b k
    obtain ⟨-, -, h3, -⟩ := facts i b l
    simp [PEqualNP.MetaComplexity.typedMatrix, bm, ent, P, h1, h2, h3]
  have hr : (bm P).rank ≤ (PEqualNP.MetaComplexity.typedMatrix 4 F τ i b).rank := by
    rw [← hsub]
    exact Matrix.rank_submatrix_le _ _ _
  have hc : cnt P ≤ N τ i b := by
    have e : cnt P = ∑ k : Fin 4, ∑ l : Fin 4, (fun x y => if F x = true ∧ F y = false ∧
        τ x y = (i : ℕ) ∧ x i = b then 1 else 0) (rows i b k) (cols i b l) := by
      unfold cnt
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      obtain ⟨h1, h2, -, -⟩ := facts i b k
      obtain ⟨-, -, h3, -⟩ := facts i b l
      simp [P, h1, h2, h3]
    rw [e]
    unfold N
    calc _ ≤ ∑ k : Fin 4, ∑ y : Fin 4 → Bool, (fun x y => if F x = true ∧ F y = false ∧
          τ x y = (i : ℕ) ∧ x i = b then 1 else 0) (rows i b k) y :=
          Finset.sum_le_sum fun k _ => sum_inj_le (cols i b) (fun k l h => (inj i b k l).2 h) _
      _ ≤ _ := sum_inj_le (rows i b) (fun k l h => (inj i b k l).1 h)
          (fun x => ∑ y : Fin 4 → Bool, if F x = true ∧ F y = false ∧
            τ x y = (i : ℕ) ∧ x i = b then 1 else 0)
  have := core P hP
  omega

set_option maxRecDepth 100000 in
lemma one_lit : ∀ j : Fin 4, ∀ x : Fin 4 → Bool,
    (∑ i : Fin 4, ∑ b : Bool, if (j : ℕ) = (i : ℕ) ∧ x i = b then 1 else 0) = 1 := by
  decide +kernel

def G (x y : Fin 4 → Bool) : ℕ := if F x = true ∧ F y = false then 1 else 0

set_option maxRecDepth 100000 in
lemma pairs : (∑ x : Fin 4 → Bool, ∑ y : Fin 4 → Bool, G x y) = 64 := by
  decide +kernel

def H (τ : (Fin 4 → Bool) → (Fin 4 → Bool) → ℕ) (x y : Fin 4 → Bool) (i : Fin 4) (b : Bool) : ℕ :=
  if F x = true ∧ F y = false ∧ τ x y = (i : ℕ) ∧ x i = b then 1 else 0

lemma total (τ : (Fin 4 → Bool) → (Fin 4 → Bool) → ℕ)
    (hτ : PEqualNP.MetaComplexity.IsTyping 4 F τ) : ∑ i : Fin 4, ∑ b : Bool, N τ i b = 64 := by
  have e : ∀ x y : Fin 4 → Bool, (∑ i : Fin 4, ∑ b : Bool, H τ x y i b) = G x y := by
    intro x y
    unfold H G
    by_cases hx : F x = true
    · by_cases hy : F y = false
      · obtain ⟨j, hj, -⟩ := hτ x y hx hy
        simp only [hx, hy, hj, true_and, and_self, ite_true]
        exact one_lit j x
      · simp [hy]
    · simp [hx]
  have hN : ∀ i b, N τ i b = ∑ x : Fin 4 → Bool, ∑ y : Fin 4 → Bool, H τ x y i b :=
    fun i b => rfl
  calc ∑ i : Fin 4, ∑ b : Bool, N τ i b
      = ∑ i : Fin 4, ∑ b : Bool, ∑ x : Fin 4 → Bool, ∑ y : Fin 4 → Bool, H τ x y i b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => hN i b
    _ = ∑ i : Fin 4, ∑ x : Fin 4 → Bool, ∑ b : Bool, ∑ y : Fin 4 → Bool, H τ x y i b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ x : Fin 4 → Bool, ∑ i : Fin 4, ∑ b : Bool, ∑ y : Fin 4 → Bool, H τ x y i b :=
        Finset.sum_comm
    _ = ∑ x : Fin 4 → Bool, ∑ i : Fin 4, ∑ y : Fin 4 → Bool, ∑ b : Bool, H τ x y i b :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ x : Fin 4 → Bool, ∑ y : Fin 4 → Bool, ∑ i : Fin 4, ∑ b : Bool, H τ x y i b :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x : Fin 4 → Bool, ∑ y : Fin 4 → Bool, G x y :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => e x y
    _ = 64 := pairs

lemma main : ¬ PEqualNP.MetaComplexity.HasTypedRank 4 F 15 := by
  rintro ⟨τ, hτ, hs⟩
  have h3 : ∑ i : Fin 4, ∑ b : Bool, (16 : ℕ) ≤ ∑ i : Fin 4, ∑ b : Bool,
      (4 * (PEqualNP.MetaComplexity.typedMatrix 4 F τ i b).rank + N τ i b) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => lit τ hτ i b
  have h4 : ∑ i : Fin 4, ∑ b : Bool,
      (4 * (PEqualNP.MetaComplexity.typedMatrix 4 F τ i b).rank + N τ i b)
      = 4 * ∑ i : Fin 4, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 4 F τ i b).rank
        + ∑ i : Fin 4, ∑ b : Bool, N τ i b := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [h4, total τ hτ] at h3
  have h5 : (∑ i : Fin 4, ∑ b : Bool, (16 : ℕ)) = 128 := by simp
  omega

end PEqualNP.Outside.L_meta_232

theorem PEqualNP.Outside.L_meta_232 : ¬ PEqualNP.MetaComplexity.HasTypedRank 4 (fun x : Fin 4 → Bool => xor (xor (xor (x 0) (x 1)) (x 2)) (x 3)) 15 :=
  PEqualNP.Outside.L_meta_232.main
