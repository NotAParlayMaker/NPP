import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadTwo PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2978_1
    (pin : ∀ (p l : ℕ) (I J : Fin p → Fin l → Prop) [DecidableRel I] [DecidableRel J] (C : Circuit),
      IsAO2 (p+l) C → circuitFun (p+l) C = fpl p I →
      ((∃ b k, I b k ∧ ∀ i j, J i j ↔ i ≠ b ∧ I i j) ∨
       (∃ a b, I a b ∧ ∀ i j, J i j ↔ j ≠ b ∧ I i j)) →
      ∃ E : Circuit, IsAO2 (p+l) E ∧ circuitFun (p+l) E = fpl p J ∧ E.size < C.size)
    (core : ∀ (p l : ℕ) (I : Fin p → Fin l → Prop) [DecidableRel I] (C : Circuit),
      Lin I → IsAO2 (p+l) C → circuitFun (p+l) C = fpl p I →
      (∀ a b k, I a k → (∀ j, I a j ↔ I b j) → a=b) →
      (∀ a b k, I k a → (∀ i, I i a ↔ I i b) → a=b) →
      ∃ T : Finset (Fin (p+l)), (∀ i j, I i j → Fin.castAdd l i ∈ T ∨ Fin.natAdd p j ∈ T) ∧
        (incid I).card + T.card ≤ C.size+1)
    (synthesize : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [DecidableRel x3] (T : Finset (Fin (x1+x2))), (∀ p l, x3 p l → Fin.castAdd x2 p ∈ T ∨ Fin.natAdd x1 l ∈ T) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ (PEqualNP.ReadTwo.incid x3).card + T.card - 1 ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [_x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10 := by
  intro p l I inst C square valid computes
  have linear : Lin I := by
    intro a b j k ab jk h
    exact square a b j k ab jk ⟨h.1,h.2.2.1,h.2.1,h.2.2.2⟩
  have lower (R : Fin p → Fin l → Prop) [DecidableRel R] (D : Circuit)
      (lin : Lin R) (ao : IsAO2 (p+l) D) (ev : circuitFun (p+l) D = fpl p R) :
      ∃ T : Finset (Fin (p+l)), (∀ i j, R i j → Fin.castAdd l i ∈ T ∨ Fin.natAdd p j ∈ T) ∧
        (incid R).card + T.card ≤ D.size+1 := by
    classical
    generalize hN : D.size = N
    induction N using Nat.strong_induction_on generalizing R D with
    | ind N ih =>
      by_cases rows : ∀ a b k, R a k → (∀ j, R a j ↔ R b j) → a=b
      · by_cases cols : ∀ a b k, R k a → (∀ i, R i a ↔ R i b) → a=b
        · simpa [hN] using core p l R D lin ao ev rows cols
        · push Not at cols
          obtain ⟨a,b,k,e,twins,ab⟩ := cols
          have ek : R k b := (twins k).mp e
          have only (j) (h : R j a) : j=k := by
            by_contra ne
            exact lin k j a b (Ne.symm ne) ab ⟨e,h,(twins k).mp e,(twins j).mp h⟩
          let J := fun i j => j≠b ∧ R i j
          obtain ⟨F,af,vf,sm⟩ := pin p l R J D ao ev (Or.inr ⟨k,b,ek,fun _ _ => Iff.rfl⟩)
          have lj : Lin J := by
            intro i i' j j' hi hj h
            exact lin i i' j j' hi hj ⟨h.1.2,h.2.1.2,h.2.2.1.2,h.2.2.2.2⟩
          obtain ⟨T,cov,budget⟩ := ih F.size (by omega) J F lj af vf rfl
          have remove : incid J = (incid R).erase (k,b) := by
            ext ⟨i,j⟩
            delta incid
            simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,J]
            constructor
            · rintro ⟨nq,h⟩
              exact ⟨fun z => nq (congrArg Prod.snd z),h⟩
            · rintro ⟨nq,h⟩
              refine ⟨?_,h⟩
              rintro rfl
              exact nq (Prod.ext (only _ ((twins _).mpr h)) rfl)
          have member : (k,b) ∈ incid R := by
            delta incid
            simpa using ek
          have count := Finset.card_erase_add_one member
          rw [←remove] at count
          by_cases hc : Fin.castAdd l k ∈ T
          · refine ⟨T,?_,by omega⟩
            intro i j h
            by_cases bad : j=b
            · subst j
              have same := only _ ((twins _).mpr h)
              subst i
              exact Or.inl hc
            · exact cov i j ⟨bad,h⟩
          · have ha : Fin.natAdd p a ∈ T := (cov k a ⟨ab,e⟩).resolve_left hc
            let U := insert (Fin.castAdd l k) (T.erase (Fin.natAdd p a))
            have d1 := Finset.card_insert_le (Fin.castAdd l k) (T.erase (Fin.natAdd p a))
            have d2 := Finset.card_erase_add_one ha
            refine ⟨U,?_,by dsimp [U]; omega⟩
            intro i j h
            have done_ (z : i=k) : Fin.castAdd l i ∈ U ∨ Fin.natAdd p j ∈ U := by
              subst i
              exact Or.inl (Finset.mem_insert_self ..)
            by_cases a' : j=a
            · subst j
              exact done_ (only _ h)
            by_cases b' : j=b
            · subst j
              exact done_ (only _ ((twins _).mpr h))
            have fa : Fin.natAdd p j ≠ Fin.natAdd p a := by
              intro h'
              apply a'
              apply Fin.ext
              have z := congrArg (fun t : Fin (p+l) => t.val) h'
              change p+j.val=p+a.val at z
              omega
            have cross : Fin.castAdd l i ≠ Fin.natAdd p a := by
              intro bad
              have z := congrArg Fin.val bad
              change i.val=p+a.val at z
              omega
            exact (cov i j ⟨b',h⟩).imp
              (fun hm => Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨cross,hm⟩))
              (fun hm => Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fa,hm⟩))
      · push Not at rows
        obtain ⟨a,b,k,e,twins,ab⟩ := rows
        have ek : R b k := (twins k).mp e
        have only (j) (h : R a j) : j=k := by
          by_contra ne
          exact lin a b k j ab (Ne.symm ne) ⟨e,(twins k).mp e,h,(twins j).mp h⟩
        let J := fun i j => i≠b ∧ R i j
        obtain ⟨F,af,vf,sm⟩ := pin p l R J D ao ev (Or.inl ⟨b,k,ek,fun _ _ => Iff.rfl⟩)
        have lj : Lin J := by
          intro i i' j j' hi hj h
          exact lin i i' j j' hi hj ⟨h.1.2,h.2.1.2,h.2.2.1.2,h.2.2.2.2⟩
        obtain ⟨T,cov,budget⟩ := ih F.size (by omega) J F lj af vf rfl
        have remove : incid J = (incid R).erase (b,k) := by
          ext ⟨i,j⟩
          delta incid
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,J]
          constructor
          · rintro ⟨nq,h⟩
            exact ⟨fun z => nq (congrArg Prod.fst z),h⟩
          · rintro ⟨nq,h⟩
            refine ⟨?_,h⟩
            rintro rfl
            exact nq (Prod.ext rfl (only _ ((twins _).mpr h)))
        have member : (b,k) ∈ incid R := by
          delta incid
          simpa using ek
        have count := Finset.card_erase_add_one member
        rw [←remove] at count
        by_cases hc : Fin.natAdd p k ∈ T
        · refine ⟨T,?_,by omega⟩
          intro i j h
          by_cases bad : i=b
          · subst i
            have same := only _ ((twins _).mpr h)
            subst j
            exact Or.inr hc
          · exact cov i j ⟨bad,h⟩
        · have ha : Fin.castAdd l a ∈ T := (cov a k ⟨ab,e⟩).resolve_right hc
          let U := insert (Fin.natAdd p k) (T.erase (Fin.castAdd l a))
          have d1 := Finset.card_insert_le (Fin.natAdd p k) (T.erase (Fin.castAdd l a))
          have d2 := Finset.card_erase_add_one ha
          refine ⟨U,?_,by dsimp [U]; omega⟩
          intro i j h
          have done_ (z : j=k) : Fin.castAdd l i ∈ U ∨ Fin.natAdd p j ∈ U := by
            subst j
            exact Or.inr (Finset.mem_insert_self ..)
          by_cases a' : i=a
          · subst i
            exact done_ (only _ h)
          by_cases b' : i=b
          · subst i
            exact done_ (only _ ((twins _).mpr h))
          have fa : Fin.castAdd l i ≠ Fin.castAdd l a := by
            intro h'
            apply a'
            apply Fin.ext
            have z := congrArg (fun t : Fin (p+l) => t.val) h'
            change i.val=a.val at z
            omega
          have cross : Fin.natAdd p j ≠ Fin.castAdd l a := by
            intro bad
            have z := congrArg Fin.val bad
            change p+j.val=a.val at z
            omega
          exact (cov i j ⟨b',h⟩).imp
            (fun hm => Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fa,hm⟩))
            (fun hm => Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨cross,hm⟩))
  obtain ⟨T,covers,budget⟩ := lower I C linear valid (funext computes)
  obtain ⟨D,P,L,ok,eqv,sz,rest⟩ := synthesize p l I T covers
  exact ⟨D,P,L,ok,eqv,by omega,rest⟩
