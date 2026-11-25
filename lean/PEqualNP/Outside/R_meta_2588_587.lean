import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.LowMerge

theorem PEqualNP.Outside.R_meta_2588_587
    (erase : ∀ (C : Circuit) (j a : ℕ), IsAO2 26 C → j < C.size → a < 26+j →
      let D := eraseGate 26 C j a
      IsAO2 26 D ∧ D.size < C.size ∧ ∀ x : List Bool, x.length = 26 →
        (((C.wires x).getD (26+j) false ≤ (C.wires x).getD a false) → C.eval x ≤ D.eval x) ∧
        (((C.wires x).getD a false ≤ (C.wires x).getD (26+j) false) → D.eval x ≤ C.eval x))
    (low : let N := fun Q => incidenceInput Q (missLines singerLines3 Q)
      ∀ C : Circuit, IsAO2 26 C → andPairs 26 C ≤ 1 → RightOnIncidentPairs singerLines3 C →
        (∀ Q ∈ quadrangles singerLines3, C.eval (N Q) = false) → 64 ≤ C.size)
    (irreducible : let N := fun Q => incidenceInput Q (missLines singerLines3 Q)
      ∀ C : Circuit, IsAO2 26 C → 2 ≤ andPairs 26 C → RightOnIncidentPairs singerLines3 C →
        (∀ Q ∈ quadrangles singerLines3, C.eval (N Q) = false) →
        (∀ j < C.size, ∀ a < 26+j,
          ¬ ((∀ p l : Fin 13, p ∈ singerLines3 l →
            wireVal C (incidenceInput {p} {l}) (26+j) ≤ wireVal C (incidenceInput {p} {l}) a) ∧
            (∀ Q ∈ quadrangles singerLines3, wireVal C (N Q) a ≤ wireVal C (N Q) (26+j)))) →
        64 ≤ C.size)
    : have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → (∀ x4 ∈ x2.gates, x4.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x4.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x2 → (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ PEqualNP.HeptadCover.singerLines3 x7 → x2.eval ((List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x6)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) = Bool.true) → (∀ x7 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x2.eval (x1 x7) = Bool.false) → (∀ x8 < x2.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).inputs, ∃ x13 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, (x2.wires (x1 x13)).getD ((26 : ℕ) + x8) Bool.false ≠ (x2.wires (x1 x13)).getD x11 Bool.false) → (64 : ℕ) ≤ x2.size := by
  dsimp only
  intro C ao _ _ pos neg _
  have positive : RightOnIncidentPairs singerLines3 C := by
    intro l p hp
    have single (u : Fin 13) :
        (List.ofFn fun i : Fin 13 => decide (i ∈ ({u} : Finset (Fin 13)))) =
          List.ofFn (fun i : Fin 13 => decide (i = u)) :=
      congrArg List.ofFn (funext fun i => decide_eq_decide.mpr Finset.mem_singleton)
    change C.eval (List.ofFn (fun i : Fin 13 => decide (i ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn (fun i : Fin 13 => decide (i ∈ ({l} : Finset (Fin 13))))) = true
    rw [single p, single l]
    exact pos p l hp
  have negative : ∀ Q ∈ quadrangles singerLines3,
      C.eval (incidenceInput Q (missLines singerLines3 Q)) = false := neg
  have lengthRow (P L : Finset (Fin 13)) : (incidenceInput P L).length = 26 := by
    change (List.ofFn (fun i : Fin 13 => decide (i ∈ P)) ++
      List.ofFn (fun i : Fin 13 => decide (i ∈ L))).length = 26
    simp only [List.length_append, List.length_ofFn]
  classical
  let N := fun Q => incidenceInput Q (missLines singerLines3 Q)
  let valid (A : Circuit) : Prop := IsAO2 26 A ∧ RightOnIncidentPairs singerLines3 A ∧
    ∀ Q ∈ quadrangles singerLines3, A.eval (N Q) = false
  have existsSize : ∃ s : ℕ, ∃ A, valid A ∧ A.size = s := ⟨C.size,C,⟨ao,positive,negative⟩,rfl⟩
  obtain ⟨A,good,sizeA⟩ := Nat.find_spec existsSize
  have minimal (D : Circuit) (hD : valid D) : A.size ≤ D.size := by
    rw [sizeA]
    exact Nat.find_min' existsSize ⟨D,hD,rfl⟩
  have nd (j : ℕ) (hj : j < A.size) (a : ℕ) (ha : a < 26+j) :
      ¬ ((∀ p l : Fin 13, p ∈ singerLines3 l →
        wireVal A (incidenceInput {p} {l}) (26+j) ≤ wireVal A (incidenceInput {p} {l}) a) ∧
        (∀ Q ∈ quadrangles singerLines3, wireVal A (N Q) a ≤ wireVal A (N Q) (26+j))) := by
    intro dom
    obtain ⟨shape,small,order⟩ := erase A j a good.1 hj ha
    let D := eraseGate 26 A j a
    have gD : valid D := by
      refine ⟨shape, ?_, ?_⟩
      · intro l p hp
        let x := incidenceInput {p} {l}
        have h := (order x (lengthRow {p} {l})).1 (dom.1 p l hp)
        change A.eval x ≤ D.eval x at h
        rw [good.2.1 l p hp] at h
        exact Bool.eq_true_of_true_le h
      · intro Q hQ
        have h := (order (N Q) (lengthRow Q (missLines singerLines3 Q))).2 (dom.2 Q hQ)
        change D.eval (N Q) ≤ A.eval (N Q) at h
        rw [good.2.2 Q hQ] at h
        exact Bool.eq_false_of_le_false h
    exact (Nat.not_lt_of_ge (minimal D gD)) small
  have size : 64 ≤ A.size := by
    by_cases h : andPairs 26 A ≤ 1
    · exact low A good.1 h good.2.1 good.2.2
    · exact irreducible A good.1 (by omega) good.2.1 good.2.2 nd
  exact size.trans (minimal C ⟨ao,positive,negative⟩)

