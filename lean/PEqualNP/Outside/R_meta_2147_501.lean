import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2147_501
    (orBound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.Ico (13 : ℕ) ((13 : ℕ) + (13 : ℕ))) C (1 : ℕ) →
      ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.range (13 : ℕ)) C (1 : ℕ) →
      (∀ p w : Fin 13, (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) →
      (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (pp = w2 ∨ pp = w2 + 1 ∨ pp = w2 + 3 ∨ pp = w2 + 9)) ∧ (v = w2 ∨ v = w2 + 1 ∨ v = w2 + 3 ∨ v = w2 + 9)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (p3 = w3 ∨ p3 = w3 + 1 ∨ p3 = w3 + 3 ∨ p3 = w3 + 9)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (pp = w4 ∨ pp = w4 + 1 ∨ pp = w4 + 3 ∨ pp = w4 + 9)) → (v4 = w4 ∨ v4 = w4 + 1 ∨ v4 = w4 + 3 ∨ v4 = w4 + 9)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (pp = ww ∨ pp = ww + 1 ∨ pp = ww + 3 ∨ pp = ww + 9))))) = false) →
      51 ≤ {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)
    (andBound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.Ico (13 : ℕ) ((13 : ℕ) + (13 : ℕ))) C (1 : ℕ) →
      ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.range (13 : ℕ)) C (1 : ℕ) →
      (∀ p w : Fin 13, (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) →
      (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (pp = w2 ∨ pp = w2 + 1 ∨ pp = w2 + 3 ∨ pp = w2 + 9)) ∧ (v = w2 ∨ v = w2 + 1 ∨ v = w2 + 3 ∨ v = w2 + 9)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (p3 = w3 ∨ p3 = w3 + 1 ∨ p3 = w3 + 3 ∨ p3 = w3 + 9)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (pp = w4 ∨ pp = w4 + 1 ∨ pp = w4 + 3 ∨ pp = w4 + 9)) → (v4 = w4 ∨ v4 = w4 + 1 ∨ v4 = w4 + 3 ∨ v4 = w4 + 9)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (pp = ww ∨ pp = ww + 1 ∨ pp = ww + 3 ∨ pp = ww + 9))))) = false) →
      13 ≤ {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.Ico (13 : ℕ) ((13 : ℕ) + (13 : ℕ))) x2 (1 : ℕ) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.range (13 : ℕ)) x2 (1 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((¬∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∧ ¬∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false := by
  intro x1 hex
  obtain ⟨C, hmono, hsize, hnl, hnp, h1, h2⟩ := hex
  have key : ∀ a b : Fin 13, (∃ dd ∈ x1, a = b + dd) ↔
      (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) := by
    intro a b
    change (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), a = b + dd) ↔ _
    simp
  simp only [key] at h1 h2
  have e1 := orBound C hmono hnl hnp h1 h2
  have e2 := andBound C hmono hnl hnp h1 h2
  have hdisj : Disjoint {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}
      {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
    rw [Set.disjoint_left]
    intro i ha hb
    rw [Set.mem_ofPred_eq] at ha hb
    rw [ha] at hb
    exact PEqualNP.CircuitLowerBounds.GateOp.noConfusion hb
  have hsum := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle : ({i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or} ∪
      {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}).ncard ≤
      C.gates.length := by
    calc _ ≤ (Set.univ : Set (Fin C.gates.length)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = C.gates.length := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hs : C.size = C.gates.length := rfl
  omega
