import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

namespace PEqualNP.Outside

-- The two-gate construction handles every case above the one-gate threshold.
theorem R_meta_4626_731
    (strictRestriction : ∀ (n : ℕ) (G H : SimpleGraph (Fin n))
      [DecidableRel G.Adj] [DecidableRel H.Adj] (a b : Fin n),
      G.degree a = 1 → G.Adj a b → H = G.deleteEdges {s(a,b)} →
      (∃ u v, H.Adj u v) →
      ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun H ∅ ∧ D.size < C.size)
    (tightExtension : ∀ (n : ℕ) (G H : SimpleGraph (Fin n))
      [DecidableRel G.Adj] [DecidableRel H.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → PEqualNP.TopForm.NoFourCycle G →
      ∀ a b : Fin n, G.degree a = 1 → G.Adj a b → H = G.deleteEdges {s(a,b)} →
      (∃ u v, H.Adj u v) →
      ∀ B : Circuit, IsMinimalMonoCircuit n B → circuitFun n B = graphFun H ∅ →
        (∀ j < B.gates.length, (gateAt B j).op = GateOp.and →
          ∃ u v, H.Adj u v ∧ Owns n B j u v) →
        (∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧ C.size ≤ B.size + 1) →
        ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧
          (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
            ∃ u v, G.Adj u v ∧ Owns n C j u v) ∧ C.size ≤ B.size + 1) :
    ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → PEqualNP.TopForm.NoFourCycle G →
      ∀ a b : Fin n, G.degree a = 1 → G.Adj a b → H = G.deleteEdges {s(a,b)} →
      (∃ B : Circuit, IsMinimalMonoCircuit n B ∧ circuitFun n B = graphFun H ∅ ∧
        ∀ j < B.gates.length, (gateAt B j).op = GateOp.and →
          ∃ u v, H.Adj u v ∧ Owns n B j u v) →
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∃ u v, G.Adj u v ∧ Owns n C j u v := by
  classical
  intro n G H _ _ htri hfour a b ha hab hdel hB
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := by rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := by rfl

  let AllOwners : ∀ {n : ℕ}, SimpleGraph (Fin n) → Circuit → Prop := fun {n} G C =>
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ u v, G.Adj u v ∧ Owns n C j u v

  -- A missing old output must still read false after the two new wires are created.
  let addLeaf : ∀ {n : ℕ}, Circuit → Fin n → Fin n → Circuit := fun {n} C a b =>
    let k := n + C.gates.length
    ⟨C.gates ++ [⟨GateOp.and, [a.val, b.val]⟩,
      ⟨GateOp.or, [if C.output < k then C.output else k + 2, k]⟩], k + 1⟩

  have foldAppendLength {α β : Type} (f : List α → β → α)
      (gs : List β) (ws : List α) :
      (gs.foldl (fun l g => l ++ [f l g]) ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons g gs ih => simp [ih, Nat.add_assoc, Nat.add_comm 1]

  have wiresLength {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
      (C.wires (List.ofFn x)).length = n + C.gates.length := by
    delta Circuit.wires
    rw [foldAppendLength, List.length_ofFn]

  have conesLength (n : ℕ) (C : Circuit) :
      (cones n C).length = C.gates.length := by
    delta cones coneStep
    rw [foldAppendLength]
    simp

  have getDAppendLeft {α : Type} (l r : List α) (d : α) {j : ℕ}
      (h : j < l.length) : (l ++ r).getD j d = l.getD j d := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

  have getDAppendAt {α : Type} (l r : List α) (d : α) (j : ℕ) :
      (l ++ r).getD (l.length + j) d = r.getD j d := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

  have addLeafWires {n : ℕ} (C : Circuit) (a b : Fin n)
      (x : Fin n → Bool) :
      (addLeaf C a b).wires (List.ofFn x) =
        C.wires (List.ofFn x) ++ [x a && x b, circuitFun n C x || (x a && x b)] := by
    let w := C.wires (List.ofFn x)
    let k := n + C.gates.length
    have hw : w.length = k := wiresLength C x
    have hinput (u : Fin n) : w.getD u.val false = x u := by
      have pref : ∀ (gs : List Gate) (l : List Bool) (i : ℕ), i < l.length →
          (Circuit.wires ⟨gs, 0⟩ l).getD i false = l.getD i false := by
        intro gs
        induction gs with
        | nil => intros; rfl
        | cons g gs ih =>
          intro l i hi
          change (Circuit.wires ⟨gs, 0⟩
            (l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])).getD i false = _
          have hnext : i < (l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)]).length := by
            simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_of_lt hi
          rw [ih _ _ hnext, getDAppendLeft _ _ _ hi]
      have hu : u.val < (List.ofFn x).length := by simp
      have hp := pref C.gates (List.ofFn x) u.val hu
      change w.getD u.val false = _ at hp
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu,
        Option.getD_some, List.getElem_ofFn] using hp
    have hleaf : (w ++ [x a && x b]).getD k false = (x a && x b) := by
      simp [← hw, List.getD_eq_getElem?_getD]
    have hout : (w ++ [x a && x b]).getD
        (if C.output < k then C.output else k + 2) false = circuitFun n C x := by
      change _ = w.getD C.output false
      split <;> rename_i h
      · exact getDAppendLeft _ _ _ (by simpa only [hw] using h)
      · rw [List.getD_eq_default _ _ (by simp [hw]),
          List.getD_eq_default _ _ (by rw [hw]; exact Nat.le_of_not_lt h)]
    change (C.gates ++ _).foldl _ (List.ofFn x) = _
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, evalAnd, evalOr,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
    let z := w.getD a.val false && w.getD b.val false
    change (w ++ [z]) ++ [(w ++ [z]).getD (if C.output < k then C.output else k + 2) false ||
      (w ++ [z]).getD k false] = w ++ _
    have hz : z = (x a && x b) := by simp only [z, hinput]
    rw [hz, hout, hleaf, List.append_assoc]
    rfl

  have addLeafFun {n : ℕ} (C : Circuit) (a b : Fin n) (x : Fin n → Bool) :
      circuitFun n (addLeaf C a b) x = (circuitFun n C x || (x a && x b)) := by
    change ((addLeaf C a b).wires (List.ofFn x)).getD (n + C.gates.length + 1) false = _
    rw [addLeafWires]
    simpa only [wiresLength, List.getD_cons_succ, List.getD_cons_zero] using
      getDAppendAt (C.wires (List.ofFn x))
        [x a && x b, circuitFun n C x || (x a && x b)] false 1

  have addLeafMono {n : ℕ} {C : Circuit} (h : Monotone2 C) (a b : Fin n) :
      Monotone2 (addLeaf C a b) := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h g hg
    · rcases List.mem_cons.mp hg with rfl | hg
      · simp
      · obtain rfl := List.mem_singleton.mp hg
        simp

  have addLeafOwners {n : ℕ} {G H : SimpleGraph (Fin n)} {C : Circuit}
      (hC : AllOwners H C) (hsub : H ≤ G) {a b : Fin n} (hab : G.Adj a b) :
      AllOwners G (addLeaf C a b) := by
    let D := addLeaf C a b
    let m := C.gates.length
    let ga : Gate := ⟨GateOp.and, [a.val, b.val]⟩
    let go : Gate := ⟨GateOp.or,
      [if C.output < n + m then C.output else n + m + 2, n + m]⟩
    have hg : D.gates = C.gates ++ [ga, go] := rfl
    have hd : D.gates.length = m + 2 := by simp [hg, m]
    have hgOld (j : ℕ) (hj : j < m) : gateAt D j = gateAt C j := by
      delta gateAt
      rw [hg, getDAppendLeft _ _ _ hj]
    have hgNew (i : ℕ) : gateAt D (m + i) = [ga, go].getD i ⟨GateOp.or, []⟩ := by
      delta gateAt
      rw [hg]
      exact getDAppendAt _ _ _ _
    have hvOld (j : ℕ) (hj : j < m) (x : Fin n → Bool) :
        gateVal n D j x = gateVal n C j x := by
      delta gateVal
      rw [show D = addLeaf C a b from rfl, addLeafWires, getDAppendLeft]
      rw [wiresLength]
      exact Nat.add_lt_add_left hj n
    have hc : cones n D = coneStep n (coneStep n (cones n C) ga) go := by
      delta cones
      rw [hg, List.foldl_append]
      rfl
    have hcOld (i j : ℕ) (hj : j < m) : InCone n D i j ↔ InCone n C i j := by
      have h : j < (cones n C).length := by rw [conesLength]; exact hj
      delta InCone
      rw [hc]
      delta coneStep
      rw [getDAppendLeft, getDAppendLeft _ _ _ h]
      simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_of_lt h
    have hcNew (i : ℕ) : ¬ InCone n D i m := by
      have hlen : (cones n C).length = m := conesLength n C
      have hn : (ga.inputs.filter (fun w =>
          decide (n ≤ w ∧ w < n + (cones n C).length))) = [] := by
        simp [ga, Nat.not_le_of_lt a.isLt, Nat.not_le_of_lt b.isLt]
      delta InCone
      rw [hc]
      change i ∉ ((cones n C ++ [_]) ++ [_]).getD m []
      rw [getDAppendLeft _ _ _ (by simp [hlen])]
      rw [hn, List.flatMap_nil]
      rw [← hlen]
      simp [List.getD_eq_getElem?_getD]
    intro j hj hop
    change j < D.gates.length at hj
    change (gateAt D j).op = GateOp.and at hop
    by_cases hjm : j < m
    · obtain ⟨u, v, huv, ho⟩ := hC j hjm (by rwa [hgOld j hjm] at hop)
      refine ⟨u, v, hsub huv, hj, hop, (hvOld j hjm _).trans ho.2.2.1, ?_⟩
      intro i hi hcone hand
      have him : i < m := hi.trans hjm
      rw [hvOld i him _]
      exact ho.2.2.2 i hi ((hcOld i j hjm).mp hcone) (by rwa [hgOld i him] at hand)
    · rw [hd] at hj
      have casesJ : j = m ∨ j = m + 1 := by
        rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hjm) with he | hlt
        · exact Or.inl he.symm
        · exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ hj) (Nat.succ_le_of_lt hlt))
      rcases casesJ with rfl | rfl
      · refine ⟨a, b, hab, by rw [hd]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _), hop, ?_, fun i _ hi => (hcNew i hi).elim⟩
        delta gateVal
        rw [addLeafWires]
        have ha : pairInput a b a = true := by delta pairInput; simp
        have hb : pairInput a b b = true := by delta pairInput; simp
        simp [m, ← wiresLength C (pairInput a b), ha, hb, List.getD_eq_getElem?_getD]
      · simp [hgNew 1, go] at hop

  have leafGraphFun {n : ℕ} {G H : SimpleGraph (Fin n)}
      [DecidableRel G.Adj] [DecidableRel H.Adj] {a b : Fin n}
      (hab : G.Adj a b) (hdel : H = G.deleteEdges {s(a,b)}) (x : Fin n → Bool) :
      graphFun G ∅ x = (graphFun H ∅ x || (x a && x b)) := by
    have hadj (u v : Fin n) : H.Adj u v ↔ G.Adj u v ∧ s(u,v) ≠ s(a,b) := by
      rw [hdel, SimpleGraph.deleteEdges_adj]
      rfl
    apply Bool.eq_iff_iff.mpr
    delta graphFun
    simp [Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      by_cases he : s(u,v) = s(a,b)
      · right
        rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨hu,hv⟩
        · exact ⟨hv,hu⟩
      · exact Or.inl ⟨u, v, (hadj u v).mpr ⟨huv,he⟩, hu, hv⟩
    · rintro (⟨u, v, huv, hu, hv⟩ | ⟨ha,hb⟩)
      · exact ⟨u, v, ((hadj u v).mp huv).1, hu, hv⟩
      · exact ⟨a,b,hab,ha,hb⟩

  have singleEdgeCase {n : ℕ} {G H : SimpleGraph (Fin n)}
      [DecidableRel G.Adj] [DecidableRel H.Adj] {a b : Fin n}
      (hab : G.Adj a b) (hdel : H = G.deleteEdges {s(a,b)})
      (hH : ∀ u v, ¬ H.Adj u v) :
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        AllOwners G C := by
    let C : Circuit := ⟨[⟨GateOp.and, [a.val, b.val]⟩], n⟩
    have evalC (x : Fin n → Bool) : circuitFun n C x = (x a && x b) := by
      have hin (u : Fin n) : (List.ofFn x).getD u.val false = x u :=
        by rw [List.getD_eq_getElem _ _ (by simp)]; simp
      delta circuitFun Circuit.eval Circuit.wires
      simp only [C, List.foldl_cons, List.foldl_nil,
        List.map_cons, List.map_nil, evalAnd, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      change ((List.ofFn x) ++ [((List.ofFn x).getD a.val false &&
        (List.ofFn x).getD b.val false)]).getD n false = _
      simp only [hin]
      simp [List.getD_eq_getElem?_getD]
    have hfun : circuitFun n C = graphFun G ∅ := by
      funext x
      rw [evalC, leafGraphFun hab hdel]
      delta graphFun; simp [hH]
    refine ⟨C, ⟨?_, ?_⟩, hfun, ?_⟩
    · intro g hg
      change g ∈ [⟨GateOp.and, [a.val, b.val]⟩] at hg
      obtain rfl := List.mem_singleton.mp hg
      simp
    · intro D _ hD
      change 1 ≤ D.gates.length
      by_contra! h
      have hnil : D.gates = [] := List.length_eq_zero_iff.mp (Nat.lt_one_iff.mp h)
      have evalD (x : Fin n → Bool) :
          circuitFun n D x = (List.ofFn x).getD D.output false := by
        delta circuitFun Circuit.eval Circuit.wires; simp [hnil]
      by_cases hlt : D.output < n
      · let u : Fin n := ⟨D.output, hlt⟩
        let x : Fin n → Bool := fun v => decide (v = u)
        have hx : circuitFun n D x = true := by
          rw [evalD, List.getD_eq_getElem _ _ (by simpa using hlt)]
          simp [x, u]
        rw [hD, hfun] at hx
        have hh : graphFun G ∅ x = false := by
          delta graphFun; simp [x]
        rw [hh] at hx
        contradiction
      · have hx : circuitFun n D (pairInput a b) = false := by
          rw [evalD, List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_lt hlt)]
        rw [hD, evalC] at hx
        delta pairInput at hx; simp at hx
    · intro j hj hop
      change j < 1 at hj
      have : j = 0 := Nat.lt_one_iff.mp hj
      subst j
      refine ⟨a,b,hab,hj,hop,?_, by simp⟩
      change circuitFun n C (pairInput a b) = true
      rw [evalC]
      delta pairInput
      simp

  by_cases hH : ∃ u v, H.Adj u v
  · obtain ⟨B, hmin, hfun, hown⟩ := hB
    have lower (C : Circuit) (hm : Monotone2 C) (hc : circuitFun n C = graphFun G ∅) :
        B.size + 1 ≤ C.size := by
      obtain ⟨D, hDm, hDf, hDs⟩ := strictRestriction n G H a b ha hab hdel hH C hm hc
      exact Nat.succ_le_of_lt ((hmin.2 D hDm (hDf.trans hfun.symm)).trans_lt hDs)
    by_cases ht : ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧
        C.size ≤ B.size + 1
    · obtain ⟨C, hm, hc, ho, hs⟩ :=
        tightExtension n G H htri hfour a b ha hab hdel hH B hmin hfun hown ht
      exact ⟨C, ⟨hm, fun D hd he => hs.trans (lower D hd (he.trans hc))⟩, hc, ho⟩
    · let C := addLeaf B a b
      have hc : circuitFun n C = graphFun G ∅ := by
        funext x
        rw [show C = addLeaf B a b from rfl, addLeafFun, hfun, leafGraphFun hab hdel]
      have hs : C.size = B.size + 2 := by delta Circuit.size; simp [C, addLeaf]
      have hs' (D : Circuit) (hm : Monotone2 D) (hf : circuitFun n D = circuitFun n C) :
          C.size ≤ D.size := by
        have hn : ¬ D.size ≤ B.size + 1 := fun h => ht ⟨D, hm, hf.trans hc, h⟩
        rw [hs]
        exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
      have hsub : H ≤ G := hdel ▸ SimpleGraph.deleteEdges_le _
      exact ⟨C, ⟨addLeafMono hmin.1 a b, hs'⟩, hc, addLeafOwners hown hsub hab⟩
  · exact singleEdgeCase hab hdel (fun u v h => hH ⟨u,v,h⟩)

end PEqualNP.Outside
