import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3310_317
    (normalize : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      (∃ u v : Fin n → Bool, circuitFun n C u = false ∧ circuitFun n C v = true) →
      ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.output < n + D.size ∧
        circuitFun n D = circuitFun n C ∧ D.size ≤ C.size)
    (saturatedBound :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
        200 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
        (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
        PEqualNP.TopForm.IsAO2 (N + N) C → C.output < N + N + C.size →
        (∀ p l, I p l → circuitFun (N + N) C
          (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
        (∀ y : Fin N → Bool, Fintype.card {l : Fin N // y l = true} ≤ q →
          circuitFun (N + N) C
            (Fin.addCases (fun p => decide (¬ ∃ l, I p l ∧ y l = true)) y) = false) →
        N * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (200 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →               (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →                 have x13 : ℕ := (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length;                 (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ x13 → (100 : ℕ) * x13 < x2 * x1 → x2 * x1 - (100 : ℕ) * x13 ≤ (100 : ℕ) * (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => !x16.op.eval [Bool.true, Bool.false]) x5.gates).length := by
  intro q N I _ C hq hN hdegree hunique hmono haccept hsound ors _ _
  let l : Fin N := ⟨0, by omega⟩
  have hp : Nonempty {p : Fin N // I p l} := by
    apply Fintype.card_pos_iff.mp
    rw [hdegree l]
    omega
  obtain ⟨⟨p, hpl⟩⟩ := hp
  let zero : Fin (N + N) → Bool := fun _ => false
  have hzero : circuitFun (N + N) C zero = false := by
    apply hsound zero
    · simp [zero]
    · simp [zero]
  obtain ⟨D, hD, hout, hEq, hSize⟩ := normalize (N + N) C hmono
    ⟨zero, _, hzero, haccept p l hpl⟩
  have hDsat (y : Fin N → Bool) (hy : Fintype.card {k : Fin N // y k = true} ≤ q) :
      circuitFun (N + N) D
        (Fin.addCases (fun p => decide (¬ ∃ k, I p k ∧ y k = true)) y) = false := by
    rw [hEq]
    apply hsound
    · simpa only [Fin.addCases_right] using hy
    · rintro ⟨p, k, hpk, hx, hk⟩
      simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hx hk
      exact hx ⟨k, hpk, hk⟩
  have hlower : N * q ≤ 100 * C.size :=
    (saturatedBound q N I D hq hN hdegree hunique hD hout
      (fun p l h => by rw [hEq]; exact haccept p l h) hDsat).trans
      (Nat.mul_le_mul_left 100 hSize)
  let isOr (g : Gate) := g.op.eval [true, false]
  have hpart : C.gates.length = ors + (C.gates.filter (fun g => !(isOr g))).length := by
    simpa only [ors, List.countP_eq_length_filter, decide_not, Bool.decide_coe] using
      (List.length_eq_countP_add_countP isOr (l := C.gates))
  change N * q ≤ 100 * C.gates.length at hlower
  rw [hpart] at hlower
  change N * q - 100 * ors ≤ 100 * (C.gates.filter (fun g => !(isOr g))).length
  omega
