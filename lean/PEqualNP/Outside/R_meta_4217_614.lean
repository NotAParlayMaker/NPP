import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4217_614
    (trace : ∀ C : Circuit, IsAO2 14 C →
    have V : ℕ → Fin 14 → Fin 14 → Bool := fun w u v => wireVal 14 C w (pairInput u v);
    have R : ℕ → ℕ → Prop := fun w j => 14+j=w ∨ InCone 14 C j (w-14);
    have B : ℕ → ℕ → Prop := fun w j => R w j ∧ (gateAt C j).op=.and ∧
      V (14+j) 0 0=false ∧ V (14+j) 7 7=false ∧
      ∃ b : Fin 2, V (opnd C j b) 0 0=true ∧ V (opnd C j (1-b)) 7 7=true;
    have F : ℕ → ℕ → ℕ → Prop := fun w₁ w₂ r =>
      ∃ i<C.gates.length, ∃ j<C.gates.length, (R w₁ i ∨ R w₂ i) ∧
        (R w₁ j ∨ R w₂ j) ∧ i≠j ∧ r∈(gateAt C i).inputs ∧ r∈(gateAt C j).inputs;
    ∀ w₁ w₂ a b, B w₁ a → B w₂ b → (¬∃ j, B w₁ j ∧ B w₂ j) →
      (∀ j, R w₁ j → R w₂ j →
        ¬(V (14+j) 0 7=true ∧ V (14+j) 0 0=false ∧ V (14+j) 7 7=false)) ∧
      ∃ r s, r≠s ∧ V r 0 0=true ∧ V r 7 7=false ∧
        V s 7 7=true ∧ V s 0 0=false ∧ F w₁ w₂ r ∧ F w₁ w₂ s)
    (operands : ∀ C : Circuit, IsAO2 14 C → ∀ j : ℕ,
      (gateAt C j).op=.and →
      wireVal 14 C (14+j) (pairInput (0 : Fin 14) 7)=true →
      ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput (0 : Fin 14) 7)=true)
    (budget : 
    ∀ C : Circuit,
      have V : ℕ → Fin 14 → Fin 14 → Bool := fun w u v => wireVal 14 C w (pairInput u v);
      have M : ℕ → Prop := fun w => V w 0 7=true ∧ V w 0 0=false ∧ V w 7 7=false;
      have R : ℕ → ℕ → Prop := fun w j => 14+j=w ∨ InCone 14 C j (w-14);
      have F : ℕ → ℕ → ℕ → Prop := fun w₁ w₂ r =>
        ∃ i j, i≠j ∧ ∀ k ∈ [i,j], (R w₁ k ∨ R w₂ k) ∧ r∈(gateAt C k).inputs;
      C.size≤27 → IsAO2 14 C → (∀ j<C.gates.length, (gateAt C j).inputs.Nodup) →
      circuitFun 14 C = PEqualNP.ReadTwo.fpl 7 (fun p l : Fin 7 => p∈fanoLines l) →
      ∀ g, (gateAt C g).op=.and → R C.output g →
        (∀ b : Fin 2, M (opnd C g b)) →
        have w₁ : ℕ := opnd C g 0;
        have w₂ : ℕ := opnd C g 1;
        (∀ j, R w₁ j → R w₂ j → ¬ M (14+j)) →
        (∃ r s, r≠s ∧ V r 0 0=true ∧ V r 7 7=false ∧ V s 7 7=true ∧
          V s 0 0=false ∧ F w₁ w₂ r ∧ F w₁ w₂ s) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).inputs.Nodup) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x7 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x8 : Fin (7 : ℕ)) (x9 : Fin (7 : ℕ)), x8 ∈ PEqualNP.CircuitLowerBounds.fanoLines x9 ∧ x7 (Fin.castAdd (7 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (7 : ℕ) x9) = Bool.true)) → ∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → (14 : ℕ) + x8 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x8 (x1.output - (14 : ℕ)) → x2 ((14 : ℕ) + x8) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x12 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x8 x12) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x8 x12) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → (¬∃ (x13 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x13 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x13) → ¬∃ (x14 : ℕ) (x15 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x14 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x15 := by
  intro C V B size ao nodup eval g hand live truth quiet none
  rintro ⟨a,b,ha,hb⟩
  obtain ⟨sep,branched⟩ := trace C ao (opnd C g 0) (opnd C g 1) a b ha hb none
  have mixed (b : Fin 2) : V (opnd C g b) 0 7=true ∧ V (opnd C g b) 0 0=false ∧ V (opnd C g b) 7 7=false :=
    ⟨operands C ao g hand truth b,quiet b⟩
  apply budget C size ao nodup eval g hand live mixed sep
  obtain ⟨r,s,hne,r0,r7,s7,s0,fr,fs⟩ := branched
  refine ⟨r,s,hne,r0,r7,s7,s0,?_,?_⟩
  · obtain ⟨i,_hi,j,_hj,ri,rj,ne,wi,wj⟩ := fr
    refine ⟨i,j,ne,?_⟩
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with e | e
    · subst k; exact ⟨ri,wi⟩
    · subst k; exact ⟨rj,wj⟩
  · obtain ⟨i,_hi,j,_hj,ri,rj,ne,wi,wj⟩ := fs
    refine ⟨i,j,ne,?_⟩
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with e | e
    · subst k; exact ⟨ri,wi⟩
    · subst k; exact ⟨rj,wj⟩
