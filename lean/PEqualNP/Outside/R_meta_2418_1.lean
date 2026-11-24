import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3200000 in
theorem PEqualNP.Outside.R_meta_2418_1
    (hLow : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4;
      let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4;
      have x4 : Circuit → Prop := fun (x4 : Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false;
      have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6;
      ∀ (x6 : Circuit), Monotone2 x6 → x6.size ≤ (63 : ℕ) → x4 x6  →
        (∀ (i : ℕ), (x6.lineDegrees (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ))).getD ((26 : ℕ) + i) (0 : ℕ) ≤ (1 : ℕ)) →
        ∃ (x10 : Circuit), Monotone2 x10 ∧ x10.size ≤ x6.size ∧ HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x10 (1 : ℕ) ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), x5 x11 → circuitFun (26 : ℕ) x10 x11 = circuitFun (26 : ℕ) x6 x11)
    (hAnd : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4;
      let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4;
      have x4 : Circuit → Prop := fun (x4 : Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false;
      have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6;
      ∀ (x6 : Circuit), Monotone2 x6 → x6.size ≤ (63 : ℕ) → x4 x6  →
        (∃ (i : ℕ), (2 : ℕ) ≤ (x6.lineDegrees (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ))).getD ((26 : ℕ) + i) (0 : ℕ) ∧ (x6.gates.getD i ⟨GateOp.and, []⟩).op = GateOp.and) →
        ∃ (x10 : Circuit), Monotone2 x10 ∧ x10.size ≤ x6.size ∧ HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x10 (1 : ℕ) ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), x5 x11 → circuitFun (26 : ℕ) x10 x11 = circuitFun (26 : ℕ) x6 x11)
    (hOr : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4;
      let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4;
      have x4 : Circuit → Prop := fun (x4 : Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false;
      have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6;
      ∀ (x6 : Circuit), Monotone2 x6 → x6.size ≤ (63 : ℕ) → x4 x6  →
        (∃ (i : ℕ), (2 : ℕ) ≤ (x6.lineDegrees (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ))).getD ((26 : ℕ) + i) (0 : ℕ) ∧ (x6.gates.getD i ⟨GateOp.or, []⟩).op = GateOp.or) →
        ∃ (x10 : Circuit), Monotone2 x10 ∧ x10.size ≤ x6.size ∧ HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x10 (1 : ℕ) ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), x5 x11 → circuitFun (26 : ℕ) x10 x11 = circuitFun (26 : ℕ) x6 x11) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false; have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ (63 : ℕ) → x4 x6 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x6.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x10 (1 : ℕ) ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), x5 x11 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x10 x11 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 x11 := by
  classical
  intro x1 x2 x3 x4 x5 x6 hmono hsize hgood
  by_cases hdeg : ∃ (i : ℕ), (2 : ℕ) ≤ (x6.lineDegrees (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ))).getD ((26 : ℕ) + i) (0 : ℕ)
  · obtain ⟨i, hi⟩ := hdeg
    have hlen : (x6.lineDegrees (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ))).length = 26 + x6.gates.length := by
      have hfold : ∀ (l : List Gate) (d : List ℕ),
          (l.foldl (fun d g => d ++ [g.lineDegree d]) d).length = d.length + l.length := by
        intro l d
        induction l generalizing d with
        | nil => simp
        | cons g gs ih =>
            rw [List.foldl_cons, ih]
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
      unfold Circuit.lineDegrees
      rw [hfold]
      simp
    have hi_lt : i < x6.gates.length := by
      by_contra hc
      have hge : (x6.lineDegrees (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ))).length ≤ 26 + i := by
        rw [hlen]; omega
      rw [List.getD_eq_default _ _ hge] at hi
      omega
    have hmem : x6.gates.getD i ⟨GateOp.and, []⟩ ∈ x6.gates := by
      rw [List.getD_eq_getElem _ _ hi_lt]
      exact List.getElem_mem _
    have hget : x6.gates.getD i ⟨GateOp.or, []⟩ = x6.gates.getD i ⟨GateOp.and, []⟩ := by
      rw [List.getD_eq_getElem _ _ hi_lt, List.getD_eq_getElem _ _ hi_lt]
    have hop := (hmono _ hmem).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hopa | hopo
    · exact hAnd x6 hmono hsize hgood ⟨i, hi, hopa⟩
    · exact hOr x6 hmono hsize hgood ⟨i, hi, hget ▸ hopo⟩
  · push Not at hdeg
    exact hLow x6 hmono hsize hgood fun i => by have h2 := hdeg i; omega
