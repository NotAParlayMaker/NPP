import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CircuitMoves PEqualNP.ReadK

-- L_meta_2230 identifies read-one witnesses with a single AND reached through ORs
-- from the output, together with OR paths from its operands to the two input leaves.
theorem PEqualNP.Outside.R_meta_2846_827
    (edgeRead : ∀ (p l : ℕ) (I : Fin p → Fin l → Prop) [DecidableRel I] (C : Circuit),
      let n := p+l
      let g := gateAt C
      let O := fun i => (g i).op=GateOp.or
      let r := fun w => (Finset.range C.size).filter (fun i => w∈(g i).inputs)
      let ok := fun D : Circuit => IsAO2 n D ∧ ∀ x : Fin n → Bool, circuitFun n D x =
        decide (∃ a b, I a b ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)
      (∀ a b i j, a≠b → i≠j → ¬(I a i ∧ I a j ∧ I b i ∧ I b j)) →
      ok C → (∀ D, ok D → C.size≤D.size) →
      (∃ T : Finset ℕ, (∀ i∈T, i<C.size ∧ O i ∧ (n+i=C.output ∨ ∃ k∈T, r (n+i)={k})) ∧
        ∀ w, WireBelowOutput n C w → (∃ i∈r w, O i) → r w ⊆ T) →
      ∀ a b, I a b → readsAtMost C n [a.val,p+b.val] 1=true)
    (prune : ∀ (p l : ℕ) (I : Fin p → Fin l → Prop) [DecidableRel I] (C : Circuit),
      let n := p+l
      let g := gateAt C
      let f := circuitFun n C
      let pure := fun (B : ℕ→Prop) (S : Finset ℕ) => ∀ w∈S, B w ∨ ∃ i<C.size,
        w=n+i ∧ (g i).op=GateOp.or ∧ ∀ u∈(g i).inputs, u∈S
      IsAO2 n C → (∀ D : Circuit, IsAO2 n D → circuitFun n D=f → C.size≤D.size) →
      (∀ x, f x=decide (∃ a b,I a b ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)) →
      (∀ a b, I a b → readsAtMost C n [a.val,p+b.val] 1=true) →
      ∃ P L : Finset ℕ, pure (fun w => w<p) P ∧ pure (fun w => p≤w ∧ w<n) L ∧
        ∀ i<C.size, (g i).op=GateOp.and → ∃ a b, (g i).inputs=[a,b] ∧
          ((a∈P ∧ b∈L) ∨ (a∈L ∧ b∈P))) :
∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) ∧ ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  intro p l I inst C four ao correct least stuck
  have minC (D : Circuit) (hD : IsAO2 (p+l) D) (e : circuitFun (p+l) D = circuitFun (p+l) C) :
      C.size ≤ D.size := least D hD (fun x => (congrFun e x).trans (correct x))
  obtain ⟨T,parents,reader⟩ := stuck
  have read := edgeRead p l I C four ⟨ao,correct⟩ (fun D h => least D h.1 h.2) (by
    refine ⟨T,?_,?_⟩
    · intro i hi
      obtain ⟨ii,op,out | ⟨k,hk,only⟩⟩ := parents i hi
      · exact ⟨ii,op,Or.inl out⟩
      · refine ⟨ii,op,Or.inr ⟨k,hk,?_⟩⟩
        ext j
        rw [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
        constructor
        · exact fun h => (only j h.1).mp h.2
        · rintro rfl
          exact ⟨(parents j hk).1,(only j (parents j hk).1).mpr rfl⟩
    · intro w below hor k hk
      obtain ⟨i,hi,op⟩ := hor
      have ir := Finset.mem_filter.mp hi
      have kr := Finset.mem_filter.mp hk
      apply reader w _ ⟨i,Finset.mem_range.mp ir.1,op,ir.2⟩ k (Finset.mem_range.mp kr.1) kr.2
      intro z hw
      exact of_decide_eq_true ((correct z).symm.trans (below z hw)))
  exact prune p l I C ao minC correct read
