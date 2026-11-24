import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4647_aux

def cols : List ℕ :=
  [(16771220242439 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ),
   (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ),
   (133412159488 : ℕ), (182572334459126281 : ℕ), (218716039641305168 : ℕ),
   (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ),
   (270286071509155872 : ℕ), (288160007408582916 : ℕ)]

def rowVec (k : Fin 58) : Fin 14 → Bool :=
  fun i => (cols.getD i.val 0).testBit k.val

def fano (x : Fin 14 → Bool) : Bool :=
  decide (∃ (p : Fin 7) (l : Fin 7),
    (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)

theorem fano_true_iff (x : Fin 14 → Bool) :
    fano x = true ↔ ∃ (p : Fin 7) (l : Fin 7),
      (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  simp [fano]

theorem fano_monotone : Monotone fano := by
  intro x y hxy
  by_cases hx : fano x = true
  · rw [hx]
    suffices hy : fano y = true by rw [hy]
    rw [fano_true_iff] at hx ⊢
    obtain ⟨p, l, hinc, hp, hl⟩ := hx
    exact ⟨p, l, hinc, Bool.eq_true_of_true_le (hp ▸ hxy _), Bool.eq_true_of_true_le (hl ▸ hxy _)⟩
  · have hxf : fano x = false := Bool.eq_false_iff.mpr hx
    rw [hxf]
    exact Bool.false_le _

-- Rows 0..20 of cols all satisfy fano = true; rows 21..57 all satisfy fano = false.
theorem fano_rows : ∀ k : Fin 58, fano (rowVec k) = decide (k.val < 21) := by
  decide +kernel

-- Every incident pair (p, l) has a witnessing row k < 21 whose support is contained in {p, 7 + l}.
theorem fano_true_covered : ∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) →
    ∃ k : Fin 58, k.val < 21 ∧ ∀ i : Fin 14, rowVec k i = true →
      (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l) := by
  decide +kernel

-- For any 7-bit point mask m, define the maximal avoiding line mask and package into Fin 14 -> Bool.
def maxAvoiding (m : Fin 128) : Fin 14 → Bool :=
  fun i =>
    if h : i.val < 7 then
      m.val.testBit i.val
    else
      let l : Fin 7 := ⟨i.val - 7, by have := i.isLt; omega⟩
      !(m.val.testBit l.val || m.val.testBit (l + 1).val || m.val.testBit (l + 3).val)

-- Every maximal avoiding vector (only 128 cases!) is dominated by one of rows 21..57.
theorem maxAvoiding_covered : ∀ m : Fin 128, ∃ k : Fin 58, 21 ≤ k.val ∧
    ∀ i : Fin 14, maxAvoiding m i = true → rowVec k i = true := by
  decide +kernel

theorem le_row_of_fano_false (x : Fin 14 → Bool) (hf : fano x = false) :
    ∃ k : Fin 58, 21 ≤ k.val ∧ x ≤ rowVec k := by
  let mVal : ℕ := Finset.univ.sum fun p : Fin 7 => if x (Fin.castAdd 7 p) = true then 2 ^ p.val else 0
  have hmLt : mVal < 128 := by
    have hle : mVal ≤ Finset.univ.sum (fun p : Fin 7 => 2 ^ p.val) := by
      apply Finset.sum_le_sum
      intro p _
      split_ifs <;> simp
    have hsum : Finset.univ.sum (fun p : Fin 7 => 2 ^ p.val) = 127 := by decide
    omega
  let m : Fin 128 := ⟨mVal, hmLt⟩
  have hbit : ∀ p : Fin 7, m.val.testBit p.val = x (Fin.castAdd 7 p) := by
    intro p
    have hmem : ∀ q : Fin 7, (if x (Fin.castAdd 7 q) = true then 2 ^ q.val else 0) =
        (if x (Fin.castAdd 7 q) = true then 1 else 0) * 2 ^ q.val := by
      intro q; split_ifs <;> simp
    have htest : ∀ (f : Fin 7 → Bool) (p : Fin 7),
        (Finset.univ.sum fun q : Fin 7 => if f q = true then 2 ^ q.val else 0).testBit p.val = f p := by
      intro f p
      clear m hmLt mVal hf hmem x
      revert f p
      decide +kernel
    exact htest (fun q => x (Fin.castAdd 7 q)) p
  obtain ⟨k, hk, hcov⟩ := maxAvoiding_covered m
  refine ⟨k, hk, fun i => ?_⟩
  cases hxi : x i
  · exact Bool.false_le _
  · suffices hmax : maxAvoiding m i = true by
      rw [hcov i hmax]
    by_cases hi : i.val < 7
    · have hp : i = Fin.castAdd 7 ⟨i.val, hi⟩ := Fin.ext (by show i.val = i.val; rfl)
      simp only [maxAvoiding, hi, ↓reduceDIte]
      rw [hbit ⟨i.val, hi⟩, ← hp, hxi]
    · let l : Fin 7 := ⟨i.val - 7, by have := i.isLt; omega⟩
      have hl : i = Fin.natAdd 7 l := Fin.ext (by show i.val = 7 + (i.val - 7); omega)
      simp only [maxAvoiding, hi, ↓reduceDIte, Bool.not_eq_true',
        Bool.or_eq_false_eq_eq_false_and_eq_false]
      have hno : ∀ p : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) → x (Fin.castAdd 7 p) = false := by
        intro p hp
        by_contra hpt
        have hpt' : x (Fin.castAdd 7 p) = true := Bool.eq_true_of_not_eq_false hpt
        have hft : fano x = true := by
          rw [fano_true_iff]
          exact ⟨p, l, hp, hpt', hl ▸ hxi⟩
        rw [hf] at hft
        cases hft
      rw [hbit l, hbit (l + 1), hbit (l + 3)]
      exact ⟨⟨hno _ (Or.inl rfl), hno _ (Or.inr (Or.inl rfl))⟩, hno _ (Or.inr (Or.inr rfl))⟩

end PEqualNP.Outside.L_meta_4647_aux

open PEqualNP.Outside.L_meta_4647_aux in
theorem PEqualNP.Outside.L_meta_4647 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool), (∀ (x2 : Fin (14 : ℕ) → Bool), x1 x2 = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ↔ Monotone x1 ∧ ∀ (x2 : Fin (58 : ℕ)), (x1 fun (x3 : Fin (14 : ℕ)) => ([(16771220242439 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (182572334459126281 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑x2) = Decidable.decide (↑x2 < (21 : ℕ)) := by
  intro f
  constructor
  · intro hf
    have heq : f = fano := by
      funext x
      apply Bool.eq_iff_iff.mpr
      rw [hf, fano_true_iff]
    subst heq
    exact ⟨fano_monotone, fano_rows⟩
  · rintro ⟨hmono, hrows⟩ x
    constructor
    · intro hfx
      by_contra hnot
      have hfalse : fano x = false := Bool.eq_false_iff.mpr (fun h => hnot ((fano_true_iff x).mp h))
      obtain ⟨k, hk, hle⟩ := le_row_of_fano_false x hfalse
      have hfk : f (rowVec k) = false := by
        have h := hrows k
        change f (rowVec k) = decide (k.val < 21) at h
        rw [h]
        exact decide_eq_false (by omega)
      have hle_val : f x ≤ f (rowVec k) := hmono hle
      rw [hfx, hfk] at hle_val
      exact absurd hle_val (by decide)
    · intro hinc
      obtain ⟨p, l, hpl, hp, hl⟩ := hinc
      obtain ⟨k, hk, hcov⟩ := fano_true_covered p l hpl
      have hle : rowVec k ≤ x := by
        intro i
        cases hr : rowVec k i
        · exact Bool.false_le _
        · rcases hcov i hr with rfl | rfl
          · rw [hp]
          · rw [hl]
      have hfk : f (rowVec k) = true := by
        have h := hrows k
        change f (rowVec k) = decide (k.val < 21) at h
        rw [h]
        exact decide_eq_true hk
      have hle_val : f (rowVec k) ≤ f x := hmono hle
      rw [hfk] at hle_val
      exact Bool.eq_true_of_true_le hle_val
