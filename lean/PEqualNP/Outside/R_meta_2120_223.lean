import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm

-- Recover the incidence relation from the circuit on point-line pairs.
-- For a chosen point set, one negative test enables every line disjoint from it.
theorem PEqualNP.Outside.R_meta_2120_223
    (boundary : ∀ (N : ℕ) (C : Circuit),
      let edge := fun (p l : Fin N) => circuitFun (N + N) C (setInput {Fin.castAdd N p, Fin.natAdd N l})
      IsAO2 (N + N) C →
      (∀ a : Fin N → Bool, circuitFun (N + N) C (Fin.append a
        (fun l => decide (∀ p : Fin N, a p = true → edge p l = false))) = false) →
      (∀ p l : Fin N, edge p l = true →
        readsAtMost C (N + N) (setList {Fin.castAdd N p, Fin.natAdd N l}) 2 = true) →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, edge p l = true ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧ IsReadK (N + N) C 2)
    (candidate : ∃ (q N : ℕ) (C : Circuit),
      let edge := fun (p l : Fin N) => circuitFun (N + N) C (setInput {Fin.castAdd N p, Fin.natAdd N l})
      223 ≤ q ∧ N = q ^ 2 + q + 1 ∧ 112 * C.size < N * (q + 1) ∧ IsAO2 (N + N) C ∧
      (∀ l : Fin N, Fintype.card {p : Fin N // edge p l = true} = q + 1) ∧
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, edge p l = true ∧ edge p' l = true) ∧
      (∀ a : Fin N → Bool, circuitFun (N + N) C (Fin.append a
        (fun l => decide (∀ p : Fin N, a p = true → edge p l = false))) = false) ∧
      (∀ p l : Fin N, edge p l = true →
        readsAtMost C (N + N) (setList {Fin.castAdd N p, Fin.natAdd N l}) 2 = true)) :
    ¬ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * (q + 1) ≤ 112 * C.size) := by
  rintro bound
  obtain ⟨q, N, C, hq, hN, small, model, lines, pairs, negative, reads⟩ := candidate
  obtain ⟨correct, readTwo⟩ := boundary N C model negative reads
  exact (Nat.not_le_of_gt small) (bound q N
    (fun p l => circuitFun (N + N) C (setInput {Fin.castAdd N p, Fin.natAdd N l}) = true)
    C (by omega) hN (fun l => by simpa only [Fintype.card_subtype] using lines l)
    pairs model correct readTwo)
