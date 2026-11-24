import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Sum
import PEqualNP.Defs

-- The small read-vector count is the bound proved by the core of L-meta-4344.
-- The remaining count concerns incidence pairs outside those three read patterns.
theorem PEqualNP.Outside.R_meta_2990_571
    (boundedReadCount : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      300 ≤ q → (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧ (let v := (PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []
        [2, 2] ∈ v ∨ [1, 1] ∈ v ∨ [2, 1] ∈ v)} ≤ 42 * C.size + N)
    (remainingCount : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      300 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      PEqualNP.TopForm.IsAO2 (N + N) C → C.output < N + N + C.size →
      (∀ p l, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      100 * C.size < N * q →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧ ¬ (let v := (PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []
        [2, 2] ∈ v ∨ [1, 1] ∈ v ∨ [2, 1] ∈ v)} ≤ 58 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I inst C hq hN degree join mono output ordered accepts rejects
  classical
  have model : PEqualNP.TopForm.IsAO2 (N + N) C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (mono g hg).1
    · intro j hj wire hwire
      obtain ⟨a, b, hin, hab, hlast⟩ := ordered j C.gates[j] (List.getElem?_eq_getElem hj)
      rw [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hj, hin] at hwire
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
      rcases hwire with rfl | rfl
      · exact hab.trans hlast
      · exact hlast
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨a, b, hin, _, _⟩ := ordered j C.gates[j] (List.getElem?_eq_getElem hj)
      rw [hin]
      rfl
  by_contra hSmall
  have small : 100 * C.size < N * q := Nat.lt_of_not_ge hSmall
  let good (e : Fin N × Fin N) : Prop :=
    let v := (PEqualNP.ReadK.readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []
    [2, 2] ∈ v ∨ [1, 1] ∈ v ∨ [2, 1] ∈ v
  let incidence := {e : Fin N × Fin N // I e.1 e.2}
  let bounded := {e : Fin N × Fin N // I e.1 e.2 ∧ good e}
  let remaining := {e : Fin N × Fin N // I e.1 e.2 ∧ ¬ good e}
  have hGood : Fintype.card bounded ≤ 42 * C.size + N :=
    boundedReadCount q N I C hq join model rejects
  have hRemaining : Fintype.card remaining ≤ 58 * C.size :=
    remainingCount q N I C hq hN degree join model output accepts rejects small
  have total : Fintype.card incidence = N * (q + 1) := by
    let byLine : incidence ≃ Σ l : Fin N, {p : Fin N // I p l} :=
      { toFun := fun e => ⟨e.val.2, ⟨e.val.1, e.property⟩⟩
        invFun := fun e => ⟨(e.2.val, e.1), e.2.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr byLine, Fintype.card_sigma]
    simp [degree]
  have partition : Fintype.card incidence = Fintype.card bounded + Fintype.card remaining := by
    let present : {e : incidence // good e.val} ≃ bounded :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun e => I e.1 e.2) good
    let absent : {e : incidence // ¬ good e.val} ≃ remaining :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun e => I e.1 e.2) (fun e => ¬ good e)
    let splitByReads : incidence ≃ bounded ⊕ remaining :=
      (Equiv.sumCompl (fun e : incidence => good e.val)).symm.trans
        (Equiv.sumCongr present absent)
    rw [Fintype.card_congr splitByReads, Fintype.card_sum]
  rw [total, Nat.mul_add, Nat.mul_one] at partition
  omega
