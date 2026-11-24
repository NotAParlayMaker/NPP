import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2120_1 (h1 : ∃ (q N : ℕ) (I : Fin N → Fin N → Prop) (_ : DecidableRel I), 224 ≤ q ∧ N = q ^ 2 + q + 1 ∧ (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) ∧ (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)) (h2 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 224 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧ PEqualNP.ReadK.IsReadK (N + N) C 2 ∧ C.size ≤ 2 * N) : ¬ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * (q + 1) ≤ 112 * C.size) := by
  intro hU
  obtain ⟨q, N, I, decI, hq, hN, hlines, hpairs⟩ := h1
  letI : DecidableRel I := decI
  have lines' : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    intro l
    simpa only [Fintype.card_subtype] using hlines l
  obtain ⟨C, hAO, hfun, hread, hsize⟩ := h2 q N I hq hN hlines hpairs
  have hle := hU q N I C (by omega) hN lines' hpairs hAO hfun hread
  have hNpos : 0 < N := by
    rw [hN]
    positivity
  have hsmall : 112 * C.size ≤ 224 * N := by
    calc
      112 * C.size ≤ 112 * (2 * N) := Nat.mul_le_mul_left 112 hsize
      _ = 224 * N := by ring
  have hstep1 : 224 * N < 225 * N := by
    nlinarith
  have hq1 : 225 ≤ q + 1 := by omega
  have hstep2 : 225 * N ≤ N * (q + 1) := by
    have hmul : N * 225 ≤ N * (q + 1) := Nat.mul_le_mul_left N hq1
    have hcomm : 225 * N = N * 225 := by ring
    rw [hcomm]
    exact hmul
  have hbig : 224 * N < N * (q + 1) :=
    lt_of_lt_of_le hstep1 hstep2
  omega
