import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3600_713
    (single : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ l : Fin N, PEqualNP.MetaComplexity.circuitFun (N + N) C (Fin.append (fun p : Fin N => decide (¬ I p l)) (fun k : Fin N => decide (k = l))) = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = true} ≤ 6 * C.size)
    (residual : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      300 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      N + N ≤ C.output → C.output < N + N + C.size →
      (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[C.output - (N + N)]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q → (¬∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧ ¬ PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = true} ≤ 94 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq hN cols unique mono lo hi out norm accepts sound
  have model : PEqualNP.TopForm.IsAO2 (N + N) C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (mono g hg).1
    · intro j hj i hij
      have get : C.gates[j]? = some C.gates[j] := by simp [hj]
      obtain ⟨a,b,hab,ha,hb⟩ := norm j _ get
      have gate : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
      rw [gate, hab] at hij
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hij
      rcases hij with rfl | rfl <;> omega
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      obtain ⟨a,b,hab,_,_⟩ := norm j C.gates[j] (by simp [hj])
      simp [hab]
  have oneLine (l : Fin N) : PEqualNP.MetaComplexity.circuitFun (N + N) C
      (Fin.append (fun p : Fin N => decide (¬ I p l)) (fun k : Fin N => decide (k = l))) = false := by
    apply sound
    · simp only [Fin.append_right, decide_eq_true_eq]
      have : Fintype.card {k : Fin N // k = l} = 1 := by simp
      rw [this]
      omega
    · rintro ⟨p,k,hI,hp,hk⟩
      simp only [Fin.append_left, Fin.append_right, decide_eq_true_eq] at hp hk
      subst k
      exact hp hI
  have small := single N I C unique model oneLine
  have rest := residual q N I C hq hN cols unique model lo hi out accepts sound
  have partition :
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = true} +
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧ ¬ PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = true} =
      Fintype.card {e : Fin N × Fin N // I e.1 e.2} := by
    simp only [Fintype.card_subtype]
    simpa only [Finset.filter_filter] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2))
        (fun e => PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = true))
  let e : {pl : Fin N × Fin N // I pl.1 pl.2} ≃ (Σ l : Fin N, {p : Fin N // I p l}) :=
    { toFun := fun x => ⟨x.val.2,⟨x.val.1,x.property⟩⟩
      invFun := fun x => ⟨(x.2.val,x.1),x.2.property⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl }
  have total : Fintype.card {e : Fin N × Fin N // I e.1 e.2} = N * (q + 1) := by
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [cols, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [total] at partition
  have : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (Nat.le_succ q)
  omega
