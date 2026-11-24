import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1948_1 :
    (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      (∀ p l : Fin N, I p l → PEqualNP.ReadK.readsAtMost D (N + N) [p.val, N + l.val] 2 = true) →
      PEqualNP.ReadK.IsReadK (N + N) D 2) →
    (∀ (n : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n D →
      (∀ g ∈ D.gates, 2 ≤ g.inputs.length) →
      PEqualNP.ReadK.IsReadK n D 2 →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 n C ∧
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.circuitFun n D ∧
        PEqualNP.ReadK.IsReadK n C 2 ∧
        C.size ≤ (D.gates.map fun g => g.inputs.length - 1).sum) →
    (¬ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D →
      (∀ g ∈ D.gates, 2 ≤ g.inputs.length) →
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      (∀ p l : Fin N, I p l → PEqualNP.ReadK.readsAtMost D (N + N) [p.val, N + l.val] 2 = true) →
      N * q ≤ 100 * (D.gates.map fun g => g.inputs.length - 1).sum)) →
    ¬ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size) := by
  intro h1 h2 h3 hAll
  apply h3
  intro q N I dec D hq hN hl hp hMono hRB hLen hFun hReads
  have hRK : PEqualNP.ReadK.IsReadK (N + N) D 2 := h1 N I D hFun hReads
  obtain ⟨C, hAO2, hCFun, hCRK, hCSize⟩ := h2 (N + N) D hMono hRB hLen hRK
  have hBase := hAll q N I C hq hN (fun l => by simpa only [Fintype.card_subtype] using hl l) hp hAO2
    (fun z => by rw [hCFun]; exact hFun z) hCRK
  omega
