import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_gct_202_aux

private lemma sum_const_omit1 {q : ℕ} (c : ℂ) (l : Fin q) :
    (∑ j : Fin q, if j = l then (0 : ℂ) else c) = ((q - 1 : ℕ) : ℂ) * c := by
  have h : (∑ j : Fin q, if j = l then (0 : ℂ) else c) =
      ∑ j ∈ Finset.univ.erase l, c := by
    calc (∑ j : Fin q, if j = l then (0 : ℂ) else c)
        = ∑ j : Fin q, if j ≠ l then c else 0 :=
            Finset.sum_congr rfl fun j _ => by by_cases hj : j = l <;> simp [hj]
      _ = ∑ j ∈ Finset.univ.filter (fun j : Fin q => j ≠ l), c := (Finset.sum_filter _ _).symm
      _ = ∑ j ∈ Finset.univ.erase l, c := by
            congr 1; ext j; simp [Finset.mem_erase]
  rw [h, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ l),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma sum_const_omit2 {q : ℕ} (c : ℂ) {l m : Fin q} (hlm : l ≠ m) :
    (∑ j : Fin q, if j = l ∨ j = m then (0 : ℂ) else c) = ((q - 2 : ℕ) : ℂ) * c := by
  have h : (∑ j : Fin q, if j = l ∨ j = m then (0 : ℂ) else c) =
      ∑ j ∈ (Finset.univ.erase l).erase m, c := by
    calc (∑ j : Fin q, if j = l ∨ j = m then (0 : ℂ) else c)
        = ∑ j : Fin q, if ¬(j = l ∨ j = m) then c else 0 :=
            Finset.sum_congr rfl fun j _ => by by_cases hj : j = l ∨ j = m <;> simp [hj]
      _ = ∑ j ∈ Finset.univ.filter (fun j : Fin q => ¬(j = l ∨ j = m)), c :=
            (Finset.sum_filter _ _).symm
      _ = ∑ j ∈ (Finset.univ.erase l).erase m, c := by
            congr 1; ext j; simp [Finset.mem_erase, not_or, and_comm]
  have hm : m ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨hlm.symm, Finset.mem_univ m⟩
  rw [h, Finset.sum_const, Finset.card_erase_of_mem hm,
    Finset.card_erase_of_mem (Finset.mem_univ l),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.sub_sub]

private lemma sum_const_omit3 {q : ℕ} (c : ℂ) {l m n : Fin q}
    (hlm : l ≠ m) (hln : l ≠ n) (hmn : m ≠ n) :
    (∑ j : Fin q, if j = l ∨ j = m ∨ j = n then (0 : ℂ) else c) =
      ((q - 3 : ℕ) : ℂ) * c := by
  have h : (∑ j : Fin q, if j = l ∨ j = m ∨ j = n then (0 : ℂ) else c) =
      ∑ j ∈ ((Finset.univ.erase l).erase m).erase n, c := by
    calc (∑ j : Fin q, if j = l ∨ j = m ∨ j = n then (0 : ℂ) else c)
        = ∑ j : Fin q, if ¬(j = l ∨ j = m ∨ j = n) then c else 0 :=
            Finset.sum_congr rfl fun j _ => by by_cases hj : j = l ∨ j = m ∨ j = n <;> simp [hj]
      _ = ∑ j ∈ Finset.univ.filter (fun j : Fin q => ¬(j = l ∨ j = m ∨ j = n)), c :=
            (Finset.sum_filter _ _).symm
      _ = ∑ j ∈ ((Finset.univ.erase l).erase m).erase n, c := by
            congr 1; ext j; simp [Finset.mem_erase, not_or, and_assoc, and_left_comm, and_comm]
  have hm : m ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨hlm.symm, Finset.mem_univ m⟩
  have hn : n ∈ (Finset.univ.erase l).erase m :=
    Finset.mem_erase.mpr ⟨hmn.symm, Finset.mem_erase.mpr ⟨hln.symm, Finset.mem_univ n⟩⟩
  rw [h, Finset.sum_const, Finset.card_erase_of_mem hn, Finset.card_erase_of_mem hm,
    Finset.card_erase_of_mem (Finset.mem_univ l),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.sub_sub, Nat.sub_sub]

theorem main (q : ℕ) (t : Fin 4 × Fin q → ℂ) (c : ℂ)
    (hq : 4 ≤ q) (hrow0 : ∀ j, t (0, j) = c)
    (h1 : (∑ i : Fin 4, ∑ j, t (i, j)) = 0)
    (h2 : (∑ j, ∑ l, if j = l then 0 else
      ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0)
    (h3 : (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ d : Fin 4,
        if a < b ∧ b < d then t (a, j) * t (b, l) * t (d, m) else 0) = 0)
    (h4 : (∑ j, ∑ l, ∑ m, ∑ n,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0
      else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) :
    c = 0 := by
  let S1 : ℂ := ∑ j : Fin q, (t (1, j) + t (2, j) + t (3, j))
  let S2 : ℂ := ∑ l : Fin q, ∑ m : Fin q, if l = m then (0 : ℂ) else
    t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m)
  let S3 : ℂ := ∑ l : Fin q, ∑ m : Fin q, ∑ n : Fin q,
    if l = m ∨ l = n ∨ m = n then (0 : ℂ) else t (1, l) * t (2, m) * t (3, n)
  have e1 : (q : ℂ) * c + S1 = 0 := by
    have h1' : (∑ i : Fin 4, ∑ j, t (i, j)) = (q : ℂ) * c + S1 := by
      rw [Fin.sum_univ_four]
      simp only [hrow0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        S1, Finset.sum_add_distrib]
      ring
    rw [← h1', h1]
  have e2 : ((q - 1 : ℕ) : ℂ) * c * S1 + S2 = 0 := by
    have hinner : ∀ j l : Fin q,
        (∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) =
          c * (t (1, l) + t (2, l) + t (3, l)) +
          (t (1, j) * t (2, l) + t (1, j) * t (3, l) + t (2, j) * t (3, l)) := by
      intro j l
      simp only [Fin.sum_univ_four, hrow0]
      norm_num
      ring
    have h2' : (∑ j, ∑ l, if j = l then 0 else
        ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) =
        ((q - 1 : ℕ) : ℂ) * c * S1 + S2 := by
      simp_rw [hinner]
      have hsplit : ∀ j l : Fin q,
          (if j = l then (0 : ℂ) else
            c * (t (1, l) + t (2, l) + t (3, l)) +
            (t (1, j) * t (2, l) + t (1, j) * t (3, l) + t (2, j) * t (3, l))) =
          (if j = l then (0 : ℂ) else c) * (t (1, l) + t (2, l) + t (3, l)) +
          (if j = l then (0 : ℂ) else
            t (1, j) * t (2, l) + t (1, j) * t (3, l) + t (2, j) * t (3, l)) := by
        intro j l
        split_ifs <;> ring
      simp_rw [hsplit, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, sum_const_omit1 c, ← Finset.mul_sum]
      rfl
    rw [← h2', h2]
  have e3 : ((q - 2 : ℕ) : ℂ) * c * S2 + S3 = 0 := by
    have hinner : ∀ j l m : Fin q,
        (∑ a : Fin 4, ∑ b : Fin 4, ∑ d : Fin 4,
          if a < b ∧ b < d then t (a, j) * t (b, l) * t (d, m) else 0) =
          c * (t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m)) +
          t (1, j) * t (2, l) * t (3, m) := by
      intro j l m
      simp only [Fin.sum_univ_four, hrow0]
      norm_num
      ring
    have h3' : (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
        ∑ a : Fin 4, ∑ b : Fin 4, ∑ d : Fin 4,
          if a < b ∧ b < d then t (a, j) * t (b, l) * t (d, m) else 0) =
        ((q - 2 : ℕ) : ℂ) * c * S2 + S3 := by
      simp_rw [hinner]
      have hsplit : ∀ j l m : Fin q,
          (if j = l ∨ j = m ∨ l = m then (0 : ℂ) else
            c * (t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m)) +
            t (1, j) * t (2, l) * t (3, m)) =
          (if j = l ∨ j = m then (0 : ℂ) else c) *
            (if l = m then (0 : ℂ) else
              t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m)) +
          (if j = l ∨ j = m ∨ l = m then (0 : ℂ) else t (1, j) * t (2, l) * t (3, m)) := by
        intro j l m
        by_cases hlm : l = m <;> by_cases hjl : j = l <;> by_cases hjm : j = m <;>
          simp [hlm, hjl, hjm]
      simp_rw [hsplit, Finset.sum_add_distrib]
      congr 1
      have hcomm :
          (∑ j : Fin q, ∑ l : Fin q, ∑ m : Fin q,
            (if j = l ∨ j = m then (0 : ℂ) else c) *
              (if l = m then (0 : ℂ) else
                t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m))) =
          ∑ l : Fin q, ∑ m : Fin q,
            (∑ j : Fin q, if j = l ∨ j = m then (0 : ℂ) else c) *
              (if l = m then (0 : ℂ) else
                t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m)) := by
        calc _ = ∑ l : Fin q, ∑ j : Fin q, ∑ m : Fin q, _ := Finset.sum_comm
          _ = ∑ l : Fin q, ∑ m : Fin q, ∑ j : Fin q, _ :=
                Finset.sum_congr rfl fun l _ => Finset.sum_comm
          _ = _ := by
                refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
                rw [← Finset.sum_mul]
      rw [hcomm]
      have hterm : ∀ l m : Fin q,
          (∑ j : Fin q, if j = l ∨ j = m then (0 : ℂ) else c) *
            (if l = m then (0 : ℂ) else
              t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m)) =
          ((q - 2 : ℕ) : ℂ) * c *
            (if l = m then (0 : ℂ) else
              t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m)) := by
        intro l m
        by_cases hlm : l = m
        · simp [hlm]
        · rw [sum_const_omit2 c hlm]
      simp_rw [hterm, ← Finset.mul_sum]
      rfl
    rw [← h3', h3]
  have e4 : ((q - 3 : ℕ) : ℂ) * c * S3 = 0 := by
    have h4' : (∑ j, ∑ l, ∑ m, ∑ n,
        if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0
        else t (0, j) * t (1, l) * t (2, m) * t (3, n)) =
        ((q - 3 : ℕ) : ℂ) * c * S3 := by
      have hfactor : ∀ j l m n : Fin q,
          (if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ)
            else t (0, j) * t (1, l) * t (2, m) * t (3, n)) =
          (if j = l ∨ j = m ∨ j = n then (0 : ℂ) else c) *
            (if l = m ∨ l = n ∨ m = n then (0 : ℂ) else t (1, l) * t (2, m) * t (3, n)) := by
        intro j l m n
        rw [hrow0 j]
        by_cases h1' : j = l <;> by_cases h2' : j = m <;> by_cases h3' : j = n <;>
          by_cases h4' : l = m <;> by_cases h5' : l = n <;> by_cases h6' : m = n <;>
          (simp [h1', h2', h3', h4', h5', h6']; try ring)
      simp_rw [hfactor]
      have hcomm :
          (∑ j : Fin q, ∑ l : Fin q, ∑ m : Fin q, ∑ n : Fin q,
            (if j = l ∨ j = m ∨ j = n then (0 : ℂ) else c) *
              (if l = m ∨ l = n ∨ m = n then (0 : ℂ) else t (1, l) * t (2, m) * t (3, n))) =
          ∑ l : Fin q, ∑ m : Fin q, ∑ n : Fin q,
            (∑ j : Fin q, if j = l ∨ j = m ∨ j = n then (0 : ℂ) else c) *
              (if l = m ∨ l = n ∨ m = n then (0 : ℂ) else t (1, l) * t (2, m) * t (3, n)) := by
        calc _ = ∑ l, ∑ j, ∑ m, ∑ n, _ := Finset.sum_comm
          _ = ∑ l, ∑ m, ∑ j, ∑ n, _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ l, ∑ m, ∑ n, ∑ j, _ :=
                Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = _ := by
                refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
                  Finset.sum_congr rfl fun _ _ => ?_
                rw [← Finset.sum_mul]
      rw [hcomm]
      have hterm : ∀ l m n : Fin q,
          (∑ j : Fin q, if j = l ∨ j = m ∨ j = n then (0 : ℂ) else c) *
            (if l = m ∨ l = n ∨ m = n then (0 : ℂ) else t (1, l) * t (2, m) * t (3, n)) =
          ((q - 3 : ℕ) : ℂ) * c *
            (if l = m ∨ l = n ∨ m = n then (0 : ℂ) else t (1, l) * t (2, m) * t (3, n)) := by
        intro l m n
        by_cases hlm : l = m
        · simp [hlm]
        · by_cases hln : l = n
          · simp [hln]
          · by_cases hmn : m = n
            · simp [hmn]
            · rw [sum_const_omit3 c hlm hln hmn]
      simp_rw [hterm, ← Finset.mul_sum]
      rfl
    rw [← h4', h4]
  have hS1 : S1 = -((q : ℂ) * c) := by
    have := congrArg (fun x => x - (q : ℂ) * c) e1
    simpa [sub_eq_add_neg] using this
  have hS2 : S2 = ((q - 1 : ℕ) : ℂ) * (q : ℂ) * c ^ 2 := by
    rw [hS1] at e2
    have := congrArg (fun x => x + ((q - 1 : ℕ) : ℂ) * (q : ℂ) * c ^ 2) e2
    convert this using 1 <;> ring
  have hS3 : S3 = -(((q - 2 : ℕ) : ℂ) * ((q - 1 : ℕ) : ℂ) * (q : ℂ) * c ^ 3) := by
    rw [hS2] at e3
    have := congrArg (fun x => x - ((q - 2 : ℕ) : ℂ) * ((q - 1 : ℕ) : ℂ) * (q : ℂ) * c ^ 3) e3
    convert this using 1 <;> ring
  have hpow : (((q - 3 : ℕ) : ℂ) * ((q - 2 : ℕ) : ℂ) * ((q - 1 : ℕ) : ℂ) * (q : ℂ)) * c ^ 4 = 0 := by
    rw [hS3] at e4
    have := congrArg (fun x => -x) e4
    convert this using 1 <;> ring
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq1 : ((q - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq2 : ((q - 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq3 : ((q - 3 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcoeff : ((q - 3 : ℕ) : ℂ) * ((q - 2 : ℕ) : ℂ) * ((q - 1 : ℕ) : ℂ) * (q : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hq3 hq2) hq1) hq0
  have hc4 : c ^ 4 = 0 := (mul_eq_zero.mp hpow).resolve_left hcoeff
  have hc2 : c * c = 0 := by
    have hmul : (c * c) * (c * c) = 0 := by rw [← hc4]; ring
    rcases mul_eq_zero.mp hmul with h | h <;> exact h
  rcases mul_eq_zero.mp hc2 with h | h <;> exact h

end PEqualNP.Outside.L_gct_202_aux

theorem PEqualNP.Outside.L_gct_202 :
    ∀ (q : ℕ) (t : Fin 4 × Fin q → ℂ) (c : ℂ), 4 ≤ q → (∀ j, t (0, j) = c) →
      (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧
      (∑ j, ∑ l, if j = l then 0 else
        ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧
      (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
        ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧
      (∑ j, ∑ l, ∑ m, ∑ n,
        if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0
        else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0 →
      c = 0 :=
  fun q t c hq hrow0 ⟨h1, h2, h3, h4⟩ =>
    PEqualNP.Outside.L_gct_202_aux.main q t c hq hrow0 h1 h2 h3 h4
