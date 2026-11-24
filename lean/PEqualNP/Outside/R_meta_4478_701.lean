import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Recurse on the number of edges. The two components use disjoint sets of input vertices.
theorem PEqualNP.Outside.R_meta_4478_701
    (connected : ∀ (P L : ℕ) (E : Finset (Fin P × Fin L)) (C : Circuit),
      let near := fun (v : Fin (P+L)) (e : Fin P × Fin L) =>
      Fin.castAdd L e.1 = v ∨ Fin.natAdd P e.2 = v
      let realizes := fun (X : Finset (Fin P × Fin L)) (D : Circuit) =>
      IsAO2 (P+L) D ∧ ∀ x, circuitFun (P+L) D x =
        decide (∃ e ∈ X, x (Fin.castAdd L e.1) = true ∧ x (Fin.natAdd P e.2) = true)
      (∀ a b : Fin P, ∀ i j : Fin L, a ≠ b → i ≠ j → ¬ ((a,i) ∈ E ∧ (a,j) ∈ E ∧ (b,i) ∈ E ∧ (b,j) ∈ E)) → realizes E C →
      (∀ v, (E.filter (near v)).card ≠ 1) →
      (¬ ∃ A B : Finset (Fin P × Fin L), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
        A ∪ B = E ∧ ∀ v, A.filter (near v) = ∅ ∨ B.filter (near v) = ∅) →
      ∃ W : Finset (Fin (P+L)), (∀ e ∈ E, Fin.castAdd L e.1 ∈ W ∨ Fin.natAdd P e.2 ∈ W) ∧ E.card + W.card ≤ C.size + 1)
    (split_cost : ∀ (P L : ℕ) (A B : Finset (Fin P × Fin L)) (C : Circuit),
      let near := fun (v : Fin (P+L)) (e : Fin P × Fin L) =>
      Fin.castAdd L e.1 = v ∨ Fin.natAdd P e.2 = v
      let realizes := fun (X : Finset (Fin P × Fin L)) (D : Circuit) =>
      IsAO2 (P+L) D ∧ ∀ x, circuitFun (P+L) D x =
        decide (∃ e ∈ X, x (Fin.castAdd L e.1) = true ∧ x (Fin.natAdd P e.2) = true)
      A.Nonempty → B.Nonempty → Disjoint A B →
      (∀ v, A.filter (near v) = ∅ ∨ B.filter (near v) = ∅) →
      (∀ a b : Fin P, ∀ i j : Fin L, a ≠ b → i ≠ j → ¬ ((a,i) ∈ (A ∪ B) ∧ (a,j) ∈ (A ∪ B) ∧ (b,i) ∈ (A ∪ B) ∧ (b,j) ∈ (A ∪ B))) →
      (∀ v, ((A ∪ B).filter (near v)).card ≠ 1) → realizes (A ∪ B) C →
      ∃ D F : Circuit, realizes A D ∧ realizes B F ∧ D.size + F.size + 1 ≤ C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ ∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ x9 ∈ x6, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → x6 x3 x4 → (∀ (x9 : Fin (x1 + x2)), (Finset.filter (x5 x9) x3).card ≠ (1 : ℕ)) → ∃ (x10 : Finset (Fin (x1 + x2))), (∀ x11 ∈ x3, Fin.castAdd x2 x11.1 ∈ x10 ∨ Fin.natAdd x1 x11.2 ∈ x10) ∧ x3.card + x10.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro P L E C
  dsimp only
  intro noFour model noLeaves
  let near := fun (v : Fin (P+L)) (e : Fin P × Fin L) =>
      Fin.castAdd L e.1 = v ∨ Fin.natAdd P e.2 = v
  let realizes := fun (X : Finset (Fin P × Fin L)) (D : Circuit) =>
      IsAO2 (P+L) D ∧ ∀ x, circuitFun (P+L) D x =
        decide (∃ e ∈ X, x (Fin.castAdd L e.1) = true ∧ x (Fin.natAdd P e.2) = true)
  let square := fun X : Finset (Fin P × Fin L) => (∀ a b : Fin P, ∀ i j : Fin L, a ≠ b → i ≠ j → ¬ ((a,i) ∈ X ∧ (a,j) ∈ X ∧ (b,i) ∈ X ∧ (b,j) ∈ X))
  let covers := fun (X : Finset (Fin P × Fin L)) (W : Finset (Fin (P+L))) => (∀ e ∈ X, Fin.castAdd L e.1 ∈ W ∨ Fin.natAdd P e.2 ∈ W)
  have solve : ∀ k (X : Finset (Fin P × Fin L)) (D : Circuit), X.card = k →
      square X → realizes X D → (∀ v, (X.filter (near v)).card ≠ 1) →
      ∃ W, covers X W ∧ X.card + W.card ≤ D.size + 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro X D count sq code leaf
      by_cases cut : ∃ A B : Finset (Fin P × Fin L), A.Nonempty ∧ B.Nonempty ∧
          Disjoint A B ∧ A ∪ B = X ∧ ∀ v, A.filter (near v) = ∅ ∨ B.filter (near v) = ∅
      · obtain ⟨A, B, hA, hB, disj, joined, separate⟩ := cut
        subst X
        obtain ⟨D₁, D₂, code₁, code₂, budget⟩ :=
          split_cost P L A B D hA hB disj separate sq leaf code
        have inherit {Y Z : Finset (Fin P × Fin L)} (sub : Y ⊆ Z) (free : square Z) :
            square Y := by
          intro a b i j ab ij box
          exact free a b i j ab ij ⟨sub box.1, sub box.2.1, sub box.2.2.1, sub box.2.2.2⟩
        have sizes := Finset.card_union_of_disjoint disj
        have pA := Finset.card_pos.mpr hA
        have pB := Finset.card_pos.mpr hB
        have leafA (v : Fin (P+L)) : (A.filter (near v)).card ≠ 1 := by
          rcases separate v with ea | eb
          · simp [ea]
          · have w := leaf v
            rwa [Finset.filter_union, eb, Finset.union_empty] at w
        have leafB (v : Fin (P+L)) : (B.filter (near v)).card ≠ 1 := by
          rcases separate v with ea | eb
          · have w := leaf v
            rwa [Finset.filter_union, ea, Finset.empty_union] at w
          · simp [eb]
        obtain ⟨W₁, c₁, n₁⟩ := ih A.card (by omega) A D₁ rfl
          (inherit Finset.subset_union_left sq) code₁ leafA
        obtain ⟨W₂, c₂, n₂⟩ := ih B.card (by omega) B D₂ rfl
          (inherit Finset.subset_union_right sq) code₂ leafB
        refine ⟨W₁ ∪ W₂, ?_, ?_⟩
        · intro e he
          rcases Finset.mem_union.mp he with ea | eb
          · exact (c₁ e ea).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
          · exact (c₂ e eb).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
        · have joinedSize := Finset.card_union_le W₁ W₂
          omega
      · exact connected P L X D sq code leaf cut
  exact solve E.card E C rfl noFour model noLeaves
