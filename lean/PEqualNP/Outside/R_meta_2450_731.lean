import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Coalesce two vertices having the same nonempty neighborhood. Four-cycle
-- freeness forces their common neighborhood to consist of a single vertex.
-- This makes a star centered at the split input a star at its old neighbor.
theorem PEqualNP.Outside.R_meta_2450_731
    (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∃ u v s t, G.Adj u v ∧ G.Adj s t ∧ ¬((s = u ∧ t = v) ∨ (s = v ∧ t = u))) →
      (∀ p q z, p ≠ q → G.Adj p z → G.Adj q z → ∃ w, ¬(G.Adj p w ↔ G.Adj q w)) →
      (∀ u v w, G.Adj u v → G.Adj v w → ¬G.Adj w u) →
      (∀ u v w z, G.Adj u v → G.Adj v w → G.Adj w z → G.Adj z u → u = w ∨ v = z) →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → HasStarProfile n G C →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        HasStarProfile n G D ∧ ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
          ∃ u v, G.Adj u v ∧ Owns n D j u v)
    (contract : ∀ (n : ℕ) (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
      (p q z : Fin (n+1)) (C : Circuit), p ≠ q → G.Adj p z →
      (∀ w, G.Adj p w ↔ G.Adj q w) →
      IsMinimalMonoCircuit (n+1) C → circuitFun (n+1) C = graphFun G ∅ →
      HasStarProfile (n+1) G C →
      let H := G.comap q.succAbove
      ∃ B : Circuit, IsMinimalMonoCircuit n B ∧ circuitFun n B = graphFun H ∅ ∧
        B.size + 1 ≤ C.size ∧ HasStarProfile n H B)
    (expand : ∀ (n : ℕ) (q : Fin (n+1)) (a : Fin n) (D : Circuit),
      let f : Fin (n+1) → Fin n := q.insertNth a id
      Monotone2 D →
      ∃ E : Circuit, Monotone2 E ∧ E.size ≤ D.size+1 ∧
        (∀ x, circuitFun (n+1) E x = circuitFun n D
          (fun v => decide (∃ w, f w = v ∧ x w = true))) ∧
        ∀ j < E.gates.length, (gateAt E j).op = GateOp.and →
          ∃ i < D.gates.length, (gateAt D i).op = GateOp.and ∧
            ∀ u v, Owns (n+1) E j u v ↔ Owns n D i (f u) (f v)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj]
      (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) →
      (∀ (x6 x7 x8 x9 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 →
        x2.Adj x8 x9 → x2.Adj x9 x6 → x6 = x8 ∨ x7 = x9) →
      PEqualNP.MetaComplexity.Monotone2 x4 →
      PEqualNP.MetaComplexity.circuitFun x1 x4 =
        PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
      (∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x9 →
        PEqualNP.MetaComplexity.circuitFun x1 x9 =
          PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x4.size ≤ x9.size) →
      PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x4 →
      ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x11 ∧
        PEqualNP.MetaComplexity.circuitFun x1 x11 =
          PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
        x11.size ≤ x4.size ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x11 ∧
        ∀ x12 < x11.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧
            PEqualNP.EdgeOwnership.Owns x1 x11 x12 x15 x16 := by
  classical
  have small (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (one : ¬∃ u v s t, G.Adj u v ∧ G.Adj s t ∧ ¬((s = u ∧ t = v) ∨ (s = v ∧ t = u)))
      (mon : Monotone2 C) (correct : circuitFun n C = graphFun G ∅) (stars : HasStarProfile n G C) :
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        HasStarProfile n G D ∧ ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
          ∃ u v, G.Adj u v ∧ Owns n D j u v := by
    by_cases zero : C.gates = []
    · exact ⟨C,mon,correct,le_rfl,stars,by simp [zero]⟩
    by_cases edge : ∃ u v, G.Adj u v
    · obtain ⟨u,v,uv⟩ := edge
      have all (s t : Fin n) (st : G.Adj s t) : (s = u ∧ t = v) ∨ (s = v ∧ t = u) :=
        by_contra fun h => one ⟨u,v,s,t,uv,st,h⟩
      let D : Circuit := ⟨[⟨.and,[u.val,v.val]⟩], n⟩
      have val (x : Fin n → Bool) : circuitFun n D x = (x u && x v) := by
        change ((List.ofFn x) ++ [((List.ofFn x).getD u.val false &&
          ((List.ofFn x).getD v.val false && true))]).getD n false = _
        simp [List.getD_eq_getElem?_getD]
      have computes : circuitFun n D = graphFun G ∅ := by
        funext x
        rw [val]
        delta graphFun
        simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨hu,hv⟩
          exact ⟨u,v,uv,hu,hv⟩
        · rintro ⟨s,t,st,hs,ht⟩
          rcases all s t st with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact ⟨hs,ht⟩
          · exact ⟨ht,hs⟩
      refine ⟨D,?_,computes,?_,?_,?_⟩
      · intro g hg
        have hg' : g = ⟨.and,[u.val,v.val]⟩ := List.mem_singleton.mp hg
        subst g
        exact ⟨Or.inl rfl,le_rfl⟩
      · change 1 ≤ C.gates.length
        exact List.length_pos_iff.mpr zero
      · intro j hj op
        right
        refine ⟨u, fun s t st _ => ?_⟩
        rcases all s t st with h | h
        · exact Or.inl h.1
        · exact Or.inr h.2
      · intro j hj op
        have hj' : j < 1 := hj
        have ej : j = 0 := by omega
        subst j
        refine ⟨u,v,uv,hj,op,?_,by simp⟩
        change circuitFun n D (pairInput u v) = true
        rw [val]
        change (decide (u = u ∨ u = v) && decide (v = u ∨ v = v)) = true
        simp
    · let D : Circuit := ⟨[],n⟩
      refine ⟨D,?_,?_,Nat.zero_le _,?_,?_⟩
      · intro g hg
        exact (List.not_mem_nil hg).elim
      rotate_left
      · intro j hj
        exact (Nat.not_lt_zero j hj).elim
      · intro j hj
        exact (Nat.not_lt_zero j hj).elim
      funext x
      have noPair : ¬∃ u v, G.Adj u v ∧ x u = true ∧ x v = true :=
        by
          rintro ⟨u,v,e,_⟩
          exact edge ⟨u,v,e⟩
      change (List.ofFn x).getD n false = _
      rw [List.getD_eq_default _ _ (by simp)]
      delta graphFun
      simp [noPair]
  intro n
  induction n with
  | zero =>
    intro G _ C tri four mono eq least stars
    exact small 0 G C (by rintro ⟨u,_⟩; exact Fin.elim0 u) mono eq stars
  | succ n ih =>
    intro G _ C tri four mono eq least stars
    have minC : IsMinimalMonoCircuit (n+1) C :=
      ⟨mono, fun D dm de => least D dm (de.trans eq)⟩
    by_cases rich : ∃ u v s t, G.Adj u v ∧ G.Adj s t ∧ ¬((s = u ∧ t = v) ∨ (s = v ∧ t = u))
    swap
    · exact small _ G C rich mono eq stars
    by_cases sep : ∀ p q z, p ≠ q → G.Adj p z → G.Adj q z → ∃ w, ¬(G.Adj p w ↔ G.Adj q w)
    · exact core _ G C rich sep tri four minC eq stars
    push Not at sep
    obtain ⟨p,q,z,pq,pz,qz,twins⟩ := sep
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq pq
    let H := G.comap q.succAbove
    let f : Fin (n+1) → Fin n := q.insertNth a id
    have sec (v : Fin n) : f (q.succAbove v) = v := Fin.insertNth_apply_succAbove _ _ _ _
    have retract (u v : Fin (n+1)) : G.Adj u v ↔ H.Adj (f u) (f v) := by
      have row (t w : Fin (n+1)) : G.Adj t w ↔ G.Adj (q.succAbove (f t)) w := by
        induction t using q.succAboveCases with
        | x =>
          have fq : f q = a := Fin.insertNth_apply_same _ _ _
          rw [fq, ha]
          exact (twins w).symm
        | p t => rw [sec]
      exact (row u v).trans ((G.adj_comm _ _).trans ((row v _).trans (G.adj_comm _ _)))
    have htri : ∀ u v w, H.Adj u v → H.Adj v w → ¬H.Adj w u :=
      fun u v w => tri (q.succAbove u) (q.succAbove v) (q.succAbove w)
    have hfour : ∀ u v w z, H.Adj u v → H.Adj v w → H.Adj w z → H.Adj z u → u = w ∨ v = z := by
      intro u v w t e₁ e₂ e₃ e₄
      exact (four _ _ _ _ e₁ e₂ e₃ e₄).imp (fun h => q.succAbove_right_injective h) (fun h => q.succAbove_right_injective h)
    obtain ⟨B, minB, eqB, costB, starB⟩ := contract n G p q z C pq pz twins minC eq stars
    obtain ⟨D, dm, de, ds, starD, liveD⟩ := ih H B htri hfour minB.1 eqB
      (fun E em ee => minB.2 E em (ee.trans eqB.symm)) starB
    obtain ⟨E, em, es, evalE, ports⟩ := expand n q a D dm
    have ee : circuitFun (n+1) E = graphFun G ∅ := by
      funext x
      rw [evalE, de]
      delta graphFun
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq, decide_eq_decide]
      constructor
      · rintro ⟨s,t,adj,⟨u,hu,xu⟩,v,hv,xv⟩
        refine ⟨u,v,(retract u v).mpr ?_,xu,xv⟩
        change f u = s at hu
        change f v = t at hv
        rwa [hu,hv]
      · rintro ⟨u,v,adj,xu,xv⟩
        exact ⟨f u,f v,(retract u v).mp adj,⟨u,rfl,xu⟩,v,rfl,xv⟩
    have uniqueNbr (t : Fin (n+1)) (ht : G.Adj p t) : z = t :=
      (four p z q t pz qz.symm ((twins t).mp ht) ht.symm).resolve_left pq
    have vertex (u : Fin (n+1)) (h : f u ≠ a) : q.succAbove (f u) = u := by
      induction u using q.succAboveCases with
      | x => exact False.elim (h (Fin.insertNth_apply_same _ _ _))
      | p v => rw [sec]
    have leaf (u v : Fin (n+1)) (hu : f u = a) (adj : G.Adj u v) : v = z := by
      have step := (retract u v).mp adj
      rw [hu] at step
      change G.Adj (q.succAbove a) (q.succAbove (f v)) at step
      rw [ha] at step
      have same : f p = a := by rw [← ha, sec]
      apply (uniqueNbr v ?_).symm
      apply (retract p v).mpr
      change G.Adj (q.succAbove (f p)) (q.succAbove (f v))
      rwa [same, ha]
    refine ⟨E,em,ee,by omega,?_,?_⟩
    · intro j hj op
      obtain ⟨i,hi,oi,owns⟩ := ports j hj op
      rcases starD i hi oi with none | ⟨c,center⟩
      · exact Or.inl (fun u v adj own => none _ _ ((retract u v).mp adj) ((owns u v).mp own))
      · right
        by_cases h : c = a
        · subst c
          refine ⟨z, ?_⟩
          intro u v adj own
          rcases center _ _ ((retract u v).mp adj) ((owns u v).mp own) with hu | hv
          · exact Or.inr (leaf u v hu adj)
          · exact Or.inl (leaf v u hv adj.symm)
        · refine ⟨q.succAbove c, ?_⟩
          intro u v adj own
          rcases center _ _ ((retract u v).mp adj) ((owns u v).mp own) with hu | hv
          · exact Or.inl ((vertex u (hu ▸ h)).symm.trans (congrArg q.succAbove hu))
          · exact Or.inr ((vertex v (hv ▸ h)).symm.trans (congrArg q.succAbove hv))
    · intro j hj op
      obtain ⟨i,hi,oi,owns⟩ := ports j hj op
      obtain ⟨u,v,adj,own⟩ := liveD i hi oi
      refine ⟨q.succAbove u,q.succAbove v,adj,(owns _ _).mpr ?_⟩
      simpa only [Fin.insertNth_apply_succAbove, id_eq] using own
