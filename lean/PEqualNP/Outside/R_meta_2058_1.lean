import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2058_1
    (incidence_support : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → 2 * N ≤ C.size + 1)
    (read_two_bound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 223 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * (q + 1) ≤ 112 * C.size := by
  intro q N I inst C hq hN lines points fan computes read
  have columns (l : Fin N) : Fintype.card {p : Fin N // I p l} = q + 1 := by
    rw [Fintype.card_subtype]; exact lines l
  have support := incidence_support q N I C hq hN columns points fan computes
  by_cases small : q ≤ 222
  · by_cases low : q ≤ 110
    · have a : N ≤ C.size := by omega
      have b : N * (q + 1) ≤ N * 111 := Nat.mul_le_mul_left _ (by omega)
      omega
    · have a : 112 ≤ N := by omega
      have b : N * (q + 1) ≤ N * 223 := Nat.mul_le_mul_left _ (by omega)
      omega
  · have b := read_two_bound q N I C (by omega) hN columns points fan computes read
    have a : N ≤ C.size := by omega
    rw [Nat.mul_add, Nat.mul_one]
    omega
