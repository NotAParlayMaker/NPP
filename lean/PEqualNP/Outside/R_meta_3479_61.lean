import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm

-- Count pairs by the output on one point together with all its nonincident lines.
theorem PEqualNP.Outside.R_meta_3479_61
    (good : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) → IsAO2 (N+N) C →
      Fintype.card { e : Fin N × Fin N // (I e.1 e.2 ∧ lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = true) ∧ circuitFun (N+N) C (Fin.addCases (fun p : Fin N => decide (p = e.1)) (fun l : Fin N => decide (¬ I e.1 l))) = false } ≤ 6*C.size)
    (many : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      10 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) → IsAO2 (N+N) C → (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N+N) C x = false) →
      let E : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2 ∧ lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = true
      4*C.size < (E.filter fun e => circuitFun (N+N) C (Fin.addCases (fun p : Fin N => decide (p = e.1)) (fun l : Fin N => decide (¬ I e.1 l))) = true).card → E.card ≤ 10*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (10 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.true } ≤ (10 : ℕ) * x5.size := by
  intro q N I inst C hq hN degree uniqueLines model sound
  let E : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2 ∧ lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = true
  let test (e : Fin N × Fin N) := circuitFun (N+N) C (Fin.addCases (fun p : Fin N => decide (p = e.1)) (fun l : Fin N => decide (¬ I e.1 l)))
  have clean := good N I C uniqueLines model
  rw [Fintype.card_subtype] at clean ⊢
  change E.card ≤ 10*C.size
  have cleanEq : (E.filter (fun e => test e = false)) =
      Finset.univ.filter (fun e : Fin N × Fin N => (I e.1 e.2 ∧ lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = true) ∧ test e = false) := by
    rw [Finset.filter_filter]
  rw [← cleanEq] at clean
  by_cases expensive : 4*C.size < (E.filter fun e => test e = true).card
  · exact many q N I C hq hN degree uniqueLines model sound expensive
  · have count := Finset.card_filter_add_card_filter_not (s := E) (fun e => test e = true)
    simp only [Bool.not_eq_true] at count
    omega
