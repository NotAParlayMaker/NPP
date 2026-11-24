import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Truncate proof trees by their number of line leaves. The second statement
-- counts incidences in an actual circuit of line-degree two.
theorem PEqualNP.Outside.R_meta_1942_9
    (truncate : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      PEqualNP.ReadK.IsReadK (N + N) C 2 →
      ∃ D : Circuit, Monotone2 D ∧ HasLineDegree (N + N) (Finset.Ico N (N + N)) D 2 ∧
        D.size ≤ 9 * C.size + 1 ∧ circuitFun (N + N) D = circuitFun (N + N) C)
    (count : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (∑ p : Fin N, (if I p l then 1 else 0 : ℕ)) = q + 1) →
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      Monotone2 D → HasLineDegree (N + N) (Finset.Ico N (N + N)) D 2 →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      (∑ l : Fin N, ∑ p : Fin N, (if I p l then 1 else 0 : ℕ)) ≤ 11 * D.size + N) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size := by
  intro q N I _ C hq hN hregular hunique hAO hfun hread
  obtain ⟨D, hmono, hdegree, hsize, hequiv⟩ := truncate N I C hAO hfun hread
  have hrect : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by
    rintro p p' l l' hp hl ⟨ha, hb, hc, hd⟩
    exact hl ((hunique p p' hp).unique ⟨ha, hc⟩ ⟨hb, hd⟩)
  have row (l : Fin N) : (∑ p : Fin N, (if I p l then 1 else 0 : ℕ)) = q + 1 := by
    simpa only [Finset.card_filter] using hregular l
  have bound := count q N I D hq hN row hrect hmono hdegree
    (fun z => (congrFun hequiv z).trans (hfun z))
  have total : (∑ l : Fin N, ∑ p : Fin N, (if I p l then 1 else 0 : ℕ)) =
      N * (q + 1) := by
    simp_rw [row]
    simp
  rw [total, Nat.mul_add, Nat.mul_one] at bound
  have hrough : N * q ≤ 99 * C.size + 11 := by omega
  by_cases hs : 11 ≤ C.size
  · omega
  -- With at most ten gates the rounded inequality leaves only small orders.
  have hsmall : N * q ≤ 1001 := by omega
  have hqsmall : q ≤ 9 := by
    by_contra! hten
    have hsq : 100 ≤ q ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hten hten
    have hpoints : 111 ≤ N := by omega
    have hlarge : 111 * 10 ≤ N * q := Nat.mul_le_mul hpoints hten
    omega
  subst N
  interval_cases q <;> norm_num at hrough ⊢ <;> omega
