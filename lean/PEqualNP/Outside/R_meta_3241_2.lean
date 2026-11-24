import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3241_2
    (htopAnd : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      let x6 : ℕ := x1 + x2;
      (∃ (p : Fin x1) (l : Fin x2), x3 p l) →
      (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬(x3 x7 x9 ∧ x3 x7 x10 ∧ x3 x8 x9 ∧ x3 x8 x10)) →
      PEqualNP.TopForm.IsAO2 x6 x5 →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 x6 D →
        PEqualNP.MetaComplexity.circuitFun x6 D = PEqualNP.MetaComplexity.circuitFun x6 x5 → x5.size ≤ D.size) →
      0 < x5.gates.length →
      x5.output = x6 + x5.gates.length - 1 →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.gates.length - 1)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (∀ (x9 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) →
      ∃ (x10 : List (ℕ × List ℕ)),
        (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < x6) ∨ x1 ≤ x11.1 ∧ x11.1 < x6 ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧
        (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧
        (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - 1 ≤ x5.size)
    (htopOr : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      let x6 : ℕ := x1 + x2;
      (∃ (p : Fin x1) (l : Fin x2), x3 p l) →
      (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬(x3 x7 x9 ∧ x3 x7 x10 ∧ x3 x8 x9 ∧ x3 x8 x10)) →
      PEqualNP.TopForm.IsAO2 x6 x5 →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 x6 D →
        PEqualNP.MetaComplexity.circuitFun x6 D = PEqualNP.MetaComplexity.circuitFun x6 x5 → x5.size ≤ D.size) →
      0 < x5.gates.length →
      x5.output = x6 + x5.gates.length - 1 →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.gates.length - 1)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (∀ (x9 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) →
      ∃ (x10 : List (ℕ × List ℕ)),
        (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < x6) ∨ x1 ≤ x11.1 ∧ x11.1 < x6 ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧
        (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧
        (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - 1 ≤ x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   let x6 : ℕ := x1 + x2;   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬(x3 x7 x9 ∧ x3 x7 x10 ∧ x3 x8 x9 ∧ x3 x8 x10)) → PEqualNP.TopForm.IsAO2 x6 x5 → (∀ (x9 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → ∃ (x10 : List (ℕ × List ℕ)), (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < x6) ∨ x1 ≤ x11.1 ∧ x11.1 < x6 ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧ (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧ (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - (1 : ℕ) ≤ x5.size := by
  classical
  intro x1 x2 x3 inst x5 x6 hno hao hfun
  by_cases hne : ∃ (p : Fin x1) (l : Fin x2), x3 p l
  · have hex : ∃ s : ℕ, ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 x6 D ∧
        (∀ z : Fin x6 → Bool, PEqualNP.MetaComplexity.circuitFun x6 D z = PEqualNP.MetaComplexity.circuitFun x6 x5 z) ∧
        D.size = s :=
      ⟨x5.size, x5, hao, fun _ => rfl, rfl⟩
    rcases Nat.find_spec hex with ⟨D, hDao, hDeq, hDsz⟩
    have hDle : D.size ≤ x5.size := by
      rw [hDsz]
      exact Nat.find_min' hex ⟨x5, hao, fun _ => rfl, rfl⟩
    have hDmin : ∀ D' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 x6 D' →
        PEqualNP.MetaComplexity.circuitFun x6 D' = PEqualNP.MetaComplexity.circuitFun x6 D →
        D.size ≤ D'.size := by
      intro D' h1 h2
      rw [hDsz]
      exact Nat.find_min' hex ⟨D', h1, fun z => (congrFun h2 z).trans (hDeq z), rfl⟩
    have hDfun : ∀ z : Fin x6 → Bool,
        PEqualNP.MetaComplexity.circuitFun x6 D z =
        Decidable.decide (∃ (p : Fin x1) (l : Fin x2), x3 p l ∧
          z (Fin.castAdd x2 p) = Bool.true ∧ z (Fin.natAdd x1 l) = Bool.true) :=
      fun z => (hDeq z).trans (hfun z)
    let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        (gs.foldl step w).length = w.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w; simp
      | cons g rest ih =>
        intro w
        simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
        omega
    have hfold_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
        i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
      intro gs
      induction gs with
      | nil => intro w i _; rfl
      | cons g rest ih =>
        intro w i hi
        simp only [List.foldl_cons]
        have hi' : i < (step w g).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        rw [ih (step w g) i hi']
        simp only [step, List.getD, List.getElem?_append_left hi]
    have hout_ge : x6 ≤ D.output := by
      by_contra hlt
      have hk : D.output < x6 := by omega
      let v : Fin x6 := ⟨D.output, hk⟩
      let xv : Fin x6 → Bool := fun i => Decidable.decide (i = v)
      have hev : PEqualNP.MetaComplexity.circuitFun x6 D xv = Bool.true := by
        change (D.gates.foldl step (List.ofFn xv)).getD D.output false = Bool.true
        rw [hfold_prefix D.gates (List.ofFn xv) D.output (by rw [List.length_ofFn]; exact hk)]
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn]
        simp [xv, v]
      rw [hDfun xv] at hev
      rcases of_decide_eq_true hev with ⟨p, l, _, hp, hl⟩
      have hpv : Fin.castAdd x2 p = v := of_decide_eq_true hp
      have hlv : Fin.natAdd x1 l = v := of_decide_eq_true hl
      have hpl := congrArg Fin.val (hpv.trans hlv.symm)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hpl
      omega
    have hout_lt : D.output < x6 + D.gates.length := by
      by_contra hge
      rcases hne with ⟨p0, l0, hpl0⟩
      let z0 : Fin x6 → Bool := fun _ => Bool.true
      have htrue : PEqualNP.MetaComplexity.circuitFun x6 D z0 = Bool.true := by
        rw [hDfun z0]
        exact decide_eq_true ⟨p0, l0, hpl0, rfl, rfl⟩
      have hlen : (D.wires (List.ofFn z0)).length = x6 + D.gates.length := by
        change (D.gates.foldl step (List.ofFn z0)).length = x6 + D.gates.length
        rw [hfold_len, List.length_ofFn]
      have hfalse : PEqualNP.MetaComplexity.circuitFun x6 D z0 = Bool.false := by
        change (D.wires (List.ofFn z0)).getD D.output false = Bool.false
        have hge' : (D.wires (List.ofFn z0)).length ≤ D.output := by omega
        simp only [List.getD, List.getElem?_eq_none hge', Option.getD_none]
      rw [htrue] at hfalse
      cases hfalse
    have hpos : 0 < D.gates.length := by omega
    have hout_eq : D.output = x6 + D.gates.length - 1 := by
      by_contra hneq
      let k : ℕ := D.output - x6 + 1
      have hk_lt : k < D.gates.length := by omega
      let D' : PEqualNP.CircuitLowerBounds.Circuit := { gates := D.gates.take k, output := D.output }
      have hD'len : D'.gates.length = k := List.length_take_of_le (by omega)
      have hD'ao : PEqualNP.TopForm.IsAO2 x6 D' := by
        refine ⟨fun g hg => hDao.1 g (List.mem_of_mem_take hg), ?_,
                fun g hg => hDao.2.2 g (List.mem_of_mem_take hg)⟩
        intro j hj i hi
        have hjk : j < k := by rw [hD'len] at hj; exact hj
        have hjd : j < D.gates.length := by omega
        have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt D' j =
            PEqualNP.MetaComplexity.NestedCover.gateAt D j := by
          change (D.gates.take k).getD j _ = D.gates.getD j _
          rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hjd, List.getElem_take]
        rw [hgat] at hi
        exact hDao.2.1 j hjd i hi
      have hD'fun : PEqualNP.MetaComplexity.circuitFun x6 D' = PEqualNP.MetaComplexity.circuitFun x6 D := by
        funext z
        change (D'.gates.foldl step (List.ofFn z)).getD D.output false =
               (D.gates.foldl step (List.ofFn z)).getD D.output false
        have hsplit : D.gates = D'.gates ++ D.gates.drop k := (List.take_append_drop k D.gates).symm
        conv_rhs => rw [hsplit, List.foldl_append]
        have hwlen : (D'.gates.foldl step (List.ofFn z)).length = x6 + k := by
          rw [hfold_len, List.length_ofFn, hD'len]
        rw [hfold_prefix (D.gates.drop k) _ D.output (by omega)]
      have hle' : D.size ≤ D'.size := hDmin D' hD'ao hD'fun
      change D.gates.length ≤ D'.gates.length at hle'
      omega
    have hj_lt : D.gates.length - 1 < D.gates.length := by omega
    have hg_mem : PEqualNP.MetaComplexity.NestedCover.gateAt D (D.gates.length - 1) ∈ D.gates := by
      change D.gates.getD (D.gates.length - 1) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ D.gates
      rw [List.getD_eq_getElem _ _ hj_lt]
      exact List.getElem_mem hj_lt
    have hres : ∃ (x10 : List (ℕ × List ℕ)),
        (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < x6) ∨ x1 ≤ x11.1 ∧ x11.1 < x6 ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧
        (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧
        (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - 1 ≤ D.size := by
      rcases hDao.1 _ hg_mem with hand | hor
      · exact htopAnd x1 x2 x3 D hne hno hDao hDmin hpos hout_eq hand hDfun
      · exact htopOr x1 x2 x3 D hne hno hDao hDmin hpos hout_eq hor hDfun
    rcases hres with ⟨L, hL1, hL2, hL3⟩
    exact ⟨L, hL1, hL2, hL3.trans hDle⟩
  · refine ⟨[], by simp, fun p l => ⟨fun h => absurd ⟨p, l, h⟩ hne, by simp⟩, by simp⟩
