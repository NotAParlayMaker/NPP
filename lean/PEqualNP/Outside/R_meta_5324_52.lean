import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- A minimally violating family must pay for a terminal and its private gates.
-- Across any partition more gates must be shared than weighted edge tests.
theorem PEqualNP.Outside.R_meta_5324_52
    (prune : ∀ (J A B : Type) [DecidableEq J] [DecidableEq A] [DecidableEq B]
      (F : J → Finset A) (D : J → Finset B) (T : Finset J),
      (∀ U ⊆ T, (∀ j ∈ U, 2+(D j \ (U.erase j).biUnion D).card < (F j \ (U.erase j).biUnion F).card) →
        (∀ S ⊆ U, S.Nonempty → S ≠ U →
          (S.biUnion F ∩ (U \ S).biUnion F).card < (S.biUnion D ∩ (U \ S).biUnion D).card) →
        (U.biUnion F).card ≤ (U.biUnion D).card+2*U.card) →
      (T.biUnion F).card ≤ (T.biUnion D).card+2*T.card)
    (core : ∀ (n m : Nat) (G M : Finset (Fin n × Fin m)) (C : Circuit) (T : Finset (Nat × Nat)),
      let k := n+m
      let v := fun (i : Nat) (z : Fin (n+m) → Bool) => (C.wires (List.ofFn z)).getD i false
      let edge := fun z : Fin (n+m) → Bool => ∃ p l, (p,l) ∈ G ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true
      let sample := fun (e : Fin n × Fin m) => pairInput (Fin.castAdd m e.1) (Fin.natAdd n e.2)
      let F := fun t : Nat × Nat =>
        let s := G.filter fun e => v t.1 (sample e) && v t.2 (sample e)
        s.disjSum (s ∩ M)
      let D := fun t : Nat × Nat => (Finset.range C.size).filter fun i =>
        ∃ w ∈ [t.1,t.2], w = k+i ∨ k ≤ w ∧ InCone k C i (w-k)
      (∀ p q l r, p ≠ q → l ≠ r → ¬((p,l) ∈ G ∧ (p,r) ∈ G ∧ (q,l) ∈ G ∧ (q,r) ∈ G)) →
      IsAO2 k C → (∀ j < C.size, (gateAt C j).op = .and → ∃ z, v (k+j) z = true ∧ ¬edge z) →
      (∀ t ∈ T, ∀ z, v t.1 z = true → v t.2 z = true → edge z) →
      (M.image Prod.fst).card = M.card → (M.image Prod.snd).card = M.card →
      (∀ j ∈ T, 2+(D j \ (T.erase j).biUnion D).card < (F j \ (T.erase j).biUnion F).card) →
      (∀ S ⊆ T, S.Nonempty → S ≠ T →
        (S.biUnion F ∩ (T \ S).biUnion F).card < (S.biUnion D ∩ (T \ S).biUnion D).card) →
      (T.biUnion F).card ≤ (T.biUnion D).card+2*T.card) :
    ∀ (x1 x2 : ℕ) (x3 x4 x5 : Finset (Fin x1 × Fin x2)) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Finset (ℕ × ℕ)), (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 → ¬((x8, x10) ∈ x3 ∧ (x8, x11) ∈ x3 ∧ (x9, x10) ∈ x3 ∧ (x9, x11) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x6 → (∀ x10 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD (x1 + x2 + x10) Bool.false = Bool.true ∧ ¬∃ (x14 : Fin x1) (x15 : Fin x2), (x14, x15) ∈ x3 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x1 x15) = Bool.true) → (∀ x11 ∈ x7, ∀ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD x11.1 Bool.false = Bool.true → (x6.wires (List.ofFn x13)).getD x11.2 Bool.false = Bool.true → ∃ (x16 : Fin x1) (x17 : Fin x2), (x16, x17) ∈ x3 ∧ x13 (Fin.castAdd x2 x16) = Bool.true ∧ x13 (Fin.natAdd x1 x17) = Bool.true) → (∀ x12 ∈ x4, x12 ∈ x3 ∧ ∃ x14 ∈ x7, (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.1 Bool.false = Bool.true ∧ (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.2 Bool.false = Bool.true) → x5 ⊆ x4 → (∀ x14 ∈ x5, ∀ x16 ∈ x5, x14.1 = x16.1 → x14 = x16) → (∀ x15 ∈ x5, ∀ x17 ∈ x5, x15.2 = x17.2 → x15 = x17) → x4.card + x5.card ≤ x6.size + (2 : ℕ) * x7.card := by
  intro n m G H M C T noSquare ao dirty safe along sub left right
  let k := n+m
  let v := fun (i : Nat) (z : Fin (n+m) → Bool) => (C.wires (List.ofFn z)).getD i false
  let sample := fun (e : Fin n × Fin m) (a : Fin (n+m)) => decide (a = Fin.castAdd m e.1 ∨ a = Fin.natAdd n e.2)
  let E := fun t : Nat × Nat => G.filter fun e => v t.1 (sample e) && v t.2 (sample e)
  let F := fun t => (E t).disjSum (E t ∩ M)
  let D := fun t : Nat × Nat => (Finset.range C.size).filter fun i =>
    ∃ w ∈ [t.1,t.2], w = k+i ∨ k ≤ w ∧ InCone k C i (w-k)
  have bound := prune _ _ _ F D T (fun U u =>
    core n m G M C U noSquare ao dirty (fun j hj => safe j (u hj))
      (Finset.card_image_iff.mpr (fun _ a _ b e => left _ a _ b e))
      (Finset.card_image_iff.mpr (fun _ a _ b e => right _ a _ b e)))
  have covered (e : Fin n × Fin m) (he : e ∈ H) : ∃ j ∈ T, e ∈ E j := by
    obtain ⟨edge,j,hj,l,r⟩ := along e he
    exact ⟨j,hj,Finset.mem_filter.mpr ⟨edge,Bool.and_eq_true_iff.mpr ⟨l,r⟩⟩⟩
  have inc : H.disjSum M ⊆ T.biUnion F := by
    intro e he
    cases e with
    | inl x =>
      obtain ⟨t,ht,hit⟩ := covered x (Finset.inl_mem_disjSum.mp he)
      exact Finset.mem_biUnion.mpr ⟨t,ht,Finset.inl_mem_disjSum.mpr hit⟩
    | inr x =>
      have hm := Finset.inr_mem_disjSum.mp he
      obtain ⟨t,ht,hit⟩ := covered x (sub hm)
      exact Finset.mem_biUnion.mpr ⟨t,ht,Finset.inr_mem_disjSum.mpr (Finset.mem_inter.mpr ⟨hit,hm⟩)⟩
  have used : T.biUnion D ⊆ Finset.range C.size := by
    intro i hi
    obtain ⟨t,_,hx⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hx).1
  have low := Finset.card_le_card inc
  have hi := Finset.card_le_card used
  rw [Finset.card_disjSum] at low
  rw [Finset.card_range] at hi
  omega
