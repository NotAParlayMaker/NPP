import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- Normalize least circuits first, bound a vertex cover in top form, and compile its stars.
theorem PEqualNP.Outside.R_meta_2976_17
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C →
      ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧
        (junk G D).card = (junk G C).card ∧ TopForm G D)
    (charge : ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I]
      (G : SimpleGraph (Fin (n + m))) [DecidableRel G.Adj] (D : Circuit),
      PEqualNP.ReadTwo.Lin I → graphFun G ∅ = PEqualNP.ReadTwo.fpl n I →
      IsLeastAO G D → TopForm G D →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
        (∀ p l, I p l → p ∈ A ∨ l ∈ B) ∧
        (PEqualNP.ReadTwo.incid I).card + A.card + B.card ≤ D.size + 1)
    (stars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
      ∃ (D : Circuit) (S : Bool → Finset ℕ),
        IsAO2 (n + m) D ∧ D.size ≤ E.card + A.card + B.card - 1 ∧
        (∀ z, circuitFun (n + m) D z = decide (∃ p l, (p,l) ∈ E ∧
          z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) ∧
        let g := gateAt D
        (∀ t w, w ∈ S t → (w < n + m ∧ decide (n ≤ w) = t) ∨
          ∃ i < D.size, w = n + m + i ∧ (g i).op = GateOp.or ∧ ∀ u ∈ (g i).inputs, u ∈ S t) ∧
        ∀ i < D.size, (g i).op = GateOp.and →
          ∃ a b t, (g i).inputs = [a,b] ∧ a ∈ S t ∧ b ∈ S (!t)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x10 ∧ x16 ∈ x11 := by
  classical
  have orientPred (n : Nat) (D : Circuit) (P L : Nat → Prop)
      (strict : IsAO2 n D)
      (crosses : ∀ i < D.size, (gateAt D i).op = GateOp.and →
        ∃ a b, (gateAt D i).inputs = [a, b] ∧ ((P a ∧ L b) ∨ (L a ∧ P b))) :
      ∃ D' : Circuit, IsAO2 n D' ∧ D'.size = D.size ∧ circuitFun n D' = circuitFun n D ∧
        (∀ i < D.size, (gateAt D i).op = GateOp.or → gateAt D' i = gateAt D i) ∧
        ∀ i < D'.size, (gateAt D' i).op = GateOp.and →
          ∃ a b, (gateAt D' i).inputs = [a, b] ∧ P a ∧ L b := by
    let flip (g : Gate) : Gate :=
      if g.op = GateOp.and ∧ ¬ (P (g.inputs.getD 0 0) ∧ L (g.inputs.getD 1 0)) then
        ⟨g.op, g.inputs.reverse⟩
      else
        g
    let D' : Circuit := ⟨D.gates.map flip, D.output⟩
    have hop (g : Gate) : (flip g).op = g.op := by
      simp only [flip]
      split <;> rfl
    have hlen (g : Gate) : (flip g).inputs.length = g.inputs.length := by
      simp only [flip]
      split <;> simp
    have hmem (g : Gate) (a : Nat) : a ∈ (flip g).inputs ↔ a ∈ g.inputs := by
      simp only [flip]
      split <;> simp
    have hor (g : Gate) (h : g.op = GateOp.or) : flip g = g := by
      simp [flip, h]
    have ev (g : Gate) (f : Nat → Bool) :
        (flip g).op.eval ((flip g).inputs.map f) = g.op.eval (g.inputs.map f) := by
      simp only [flip]
      split
      · rename_i h
        rw [h.1]
        change (g.inputs.reverse.map f).all id = (g.inputs.map f).all id
        simp
      · rfl
    have hfold (gs : List Gate) (w : List Bool) :
        (gs.map flip).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons, ev, ih]
    have hgate (i : Nat) (hi : i < D.gates.length) :
        gateAt D' i = flip (gateAt D i) := by
      have hget : D.gates[i]? = some D.gates[i] := List.getElem?_eq_getElem hi
      delta gateAt
      simp [D', List.getD_eq_getElem?_getD, hget]
    have hsize : D'.size = D.size := by
      change (D.gates.map flip).length = D.gates.length
      simp only [List.length_map]
    refine ⟨D', ?_, hsize, ?_, ?_, ?_⟩
    · obtain ⟨hops, hread, hfanin⟩ := strict
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        change g ∈ D.gates.map flip at hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        simpa only [hop] using hops _ hg'
      · intro i hi a ha
        have hiD : i < D.gates.length := by simpa [D'] using hi
        rw [hgate i hiD, hmem] at ha
        exact hread i hiD a ha
      · intro g hg
        change g ∈ D.gates.map flip at hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        simpa only [hlen] using hfanin _ hg'
    · funext x
      delta circuitFun Circuit.eval Circuit.wires
      simp only [D']
      rw [hfold]
    · intro i hi hand
      rw [hgate i hi]
      exact hor _ hand
    · intro i hi hand
      have hiD : i < D.gates.length := by
        change i < (D.gates.map flip).length at hi
        simpa only [List.length_map] using hi
      have handD : (gateAt D i).op = GateOp.and := by
        simpa only [hgate i hiD, hop] using hand
      obtain ⟨a, b, hin, hcross⟩ := crosses i hiD handD
      by_cases hab : P a ∧ L b
      · exact ⟨a, b, by simp [hgate i hiD, flip, hin, hab], hab⟩
      · obtain ⟨ha, hb⟩ := hcross.resolve_left hab
        have hflip : (gateAt D i).op = GateOp.and ∧
            ¬ (P ((gateAt D i).inputs.getD 0 0) ∧ L ((gateAt D i).inputs.getD 1 0)) :=
          ⟨handD, by simpa [hin] using hab⟩
        refine ⟨b, a, ?_, hb, ha⟩
        simp only [hgate i hiD, flip, ite_eq_left hflip]
        simp [hin]
  intro n m I _ C square ao correct
  let E := PEqualNP.ReadTwo.incid I
  have mem (p : Fin n) (l : Fin m) : (p, l) ∈ E ↔ I p l := by
    change (p, l) ∈ PEqualNP.ReadTwo.incid I ↔ I p l
    delta PEqualNP.ReadTwo.incid
    simp
  have coverBudget : ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
      (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card - 1 ≤ C.size := by
    by_cases edge : E.Nonempty
    · let rel (a b : Fin (n + m)) : Prop :=
        ∃ (p : Fin n) (l : Fin m), a = Fin.castAdd m p ∧ b = Fin.natAdd n l ∧ I p l
      let G := SimpleGraph.fromRel rel
      letI : DecidableRel G.Adj := Classical.decRel _
      have apart (p : Fin n) (l : Fin m) : Fin.castAdd m p ≠ Fin.natAdd n l := by
        intro eq
        have val := congrArg Fin.val eq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at val
        have bound := p.isLt
        omega
      have edgeAdj (p : Fin n) (l : Fin m) (h : I p l) :
          G.Adj (Fin.castAdd m p) (Fin.natAdd n l) := by
        change Fin.castAdd m p ≠ Fin.natAdd n l ∧
          (rel (Fin.castAdd m p) (Fin.natAdd n l) ∨ rel (Fin.natAdd n l) (Fin.castAdd m p))
        exact ⟨apart p l, Or.inl ⟨p, l, rfl, rfl, h⟩⟩
      have edges : G.edgeFinset.Nonempty := by
        obtain ⟨⟨p, l⟩, h⟩ := edge
        refine ⟨s(Fin.castAdd m p, Fin.natAdd n l), ?_⟩
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact edgeAdj p l ((mem p l).mp h)
      have graphEval : graphFun G ∅ = PEqualNP.ReadTwo.fpl n I := by
        funext z
        delta graphFun PEqualNP.ReadTwo.fpl
        simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
        rw [decide_eq_decide]
        constructor
        · rintro ⟨a, b, hab, ha, hb⟩
          change a ≠ b ∧ (rel a b ∨ rel b a) at hab
          rcases hab.2 with ⟨p, l, rfl, rfl, h⟩ | ⟨p, l, rfl, rfl, h⟩
          · exact ⟨p, l, h, ha, hb⟩
          · exact ⟨p, l, h, hb, ha⟩
        · rintro ⟨p, l, h, hp, hl⟩
          exact ⟨_, _, edgeAdj p l h, hp, hl⟩
      have CComputes : circuitFun (n + m) C = graphFun G ∅ := by
        rw [graphEval]
        funext z
        exact correct z
      have realizable : ∃ k : ℕ, ∃ D : Circuit, IsAO2 (n + m) D ∧
          circuitFun (n + m) D = graphFun G ∅ ∧ D.size = k :=
        ⟨C.size, C, ao, CComputes, rfl⟩
      obtain ⟨least, leastAO, leastEval, leastSize⟩ := Nat.find_spec realizable
      have leastCircuit : IsLeastAO G least := by
        refine ⟨leastAO, leastEval, ?_⟩
        intro D DAllowed DEval
        rw [leastSize]
        exact Nat.find_min' realizable ⟨D, DAllowed, DEval, rfl⟩
      obtain ⟨D, DLeast, same, _, DTop⟩ := normalize (n + m) G least edges leastCircuit
      have DSize : D.size ≤ C.size := by
        rw [same]
        exact leastCircuit.2.2 C ao CComputes
      have linear : PEqualNP.ReadTwo.Lin I := by
        intro p q l s hp hl h
        exact square p q l s hp hl ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩
      obtain ⟨A, B, cover, bound⟩ := charge n m I G D linear graphEval DLeast DTop
      refine ⟨A, B, fun e he => cover e.1 e.2 ((mem e.1 e.2).mp he), ?_⟩
      change E.card + A.card + B.card ≤ D.size + 1 at bound
      omega
    · have empty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp edge
      exact ⟨∅, ∅, by simp [empty], by simp [empty]⟩
  obtain ⟨A, B, cover, budget⟩ := coverBudget
  obtain ⟨D, S, allowed, size, eval, closed, ands⟩ := stars n m E A B cover
  have crossing : ∀ i < D.size, (gateAt D i).op = GateOp.and →
      ∃ a b, (gateAt D i).inputs = [a,b] ∧
        ((a ∈ S false ∧ b ∈ S true) ∨ (a ∈ S true ∧ b ∈ S false)) := by
    intro i hi andOp
    obtain ⟨a, b, side, inputs, ha, hb⟩ := ands i hi andOp
    refine ⟨a, b, inputs, ?_⟩
    cases side
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
  obtain ⟨D', allowed', sameSize, sameEval, sameOR, ordered⟩ :=
    orientPred (n + m) D (fun a => a ∈ S false) (fun a => a ∈ S true) allowed crossing
  refine ⟨D', S false, S true, allowed', ?_, by omega, ?_, ?_, ordered⟩
  · intro z
    rw [sameEval]
    simpa only [mem] using eval z
  · intro w hw
    rcases closed false w hw with ⟨_, side⟩ | ⟨i, hi, hwEq, orOp, inputs⟩
    · exact Or.inl (by simpa using side)
    · have unchanged := sameOR i hi orOp
      refine Or.inr ⟨i, ?_, hwEq, ?_, ?_⟩
      · change i < D'.size
        rwa [sameSize]
      · rwa [unchanged]
      · simpa only [unchanged] using inputs
  · intro w hw
    rcases closed true w hw with ⟨bound, side⟩ | ⟨i, hi, hwEq, orOp, inputs⟩
    · exact Or.inl ⟨by simpa using side, bound⟩
    · have unchanged := sameOR i hi orOp
      refine Or.inr ⟨i, ?_, hwEq, ?_, ?_⟩
      · change i < D'.size
        rwa [sameSize]
      · rwa [unchanged]
      · simpa only [unchanged] using inputs
