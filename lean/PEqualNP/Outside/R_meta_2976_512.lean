import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm in
theorem PEqualNP.Outside.R_meta_2976_512
    (topFormExists : ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → IsAO2 N C → circuitFun N C = graphFun G ∅ →
      ∃ D : Circuit, IsAO2 N D ∧ circuitFun N D = graphFun G ∅ ∧ D.size ≤ C.size ∧ TopForm G D)
    (cleanExists : ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
      (S : Finset (Fin N)) (C : Circuit),
      (∀ u v, G.Adj u v → (u ∈ S ↔ v ∉ S)) → NoFourCycle G →
      IsAO2 N C → circuitFun N C = graphFun G ∅ → TopForm G C →
      ∃ D : Circuit, IsAO2 N D ∧ circuitFun N D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        TopForm G D ∧ junk G D = ∅) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x10 ∧ x16 ∈ x11 := by
  classical
  intro n m I _ C hno hC hfun
  let G : SimpleGraph (Fin (n + m)) :=
    { Adj := fun u v =>
        (∃ (p : Fin n) (l : Fin m), u = Fin.castAdd m p ∧ v = Fin.natAdd n l ∧ I p l) ∨
        (∃ (p : Fin n) (l : Fin m), v = Fin.castAdd m p ∧ u = Fin.natAdd n l ∧ I p l)
      symm := ⟨fun u v h => h.symm⟩
      loopless := ⟨fun u h => by
        rcases h with ⟨p, l, hu, hv, _⟩ | ⟨p, l, hv, hu, _⟩
        · have h1 : u.val = p.val := congrArg Fin.val hu
          have h2 : u.val = n + l.val := congrArg Fin.val hv
          have hp := p.isLt
          omega
        · have h1 : u.val = p.val := congrArg Fin.val hv
          have h2 : u.val = n + l.val := congrArg Fin.val hu
          have hp := p.isLt
          omega⟩ }
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  have hBip : ∀ u v : Fin (n + m), G.Adj u v → (u.val < n ↔ ¬ v.val < n) := by
    intro u v h
    rcases h with ⟨p, l, rfl, rfl, _⟩ | ⟨p, l, rfl, rfl, _⟩
    · simp only [Fin.val_castAdd, Fin.val_natAdd]
      have hp := p.isLt
      omega
    · simp only [Fin.val_castAdd, Fin.val_natAdd]
      have hp := p.isLt
      omega
  have hNo4 : NoFourCycle G := by
    intro u v huv
    rw [Finset.card_le_one]
    intro w1 hw1 w2 hw2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
    by_contra hne
    rcases hw1.1 with ⟨p1, l1, rfl, rfl, h1⟩ | ⟨p1, l1, rfl, rfl, h1⟩
    · rcases hw2.1 with ⟨p1', l2, hp1, rfl, h2⟩ | ⟨p1', l2, _, hcontra, _⟩
      · have hp1eq : p1 = p1' := Fin.ext (by simpa using congrArg Fin.val hp1)
        subst hp1eq
        rcases hw1.2 with ⟨p2, l1', rfl, hl1, h3⟩ | ⟨p2, l1', hcontra, _, _⟩
        · have hl1eq : l1 = l1' := Fin.ext (by
            have h := congrArg Fin.val hl1
            simp only [Fin.val_natAdd] at h
            omega)
          subst hl1eq
          rcases hw2.2 with ⟨p2', l2', hp2, hl2, h4⟩ | ⟨p2', l2', hcontra, _, _⟩
          · have hp2eq : p2 = p2' := Fin.ext (by simpa using congrArg Fin.val hp2)
            have hl2eq : l2 = l2' := Fin.ext (by
              have h := congrArg Fin.val hl2
              simp only [Fin.val_natAdd] at h
              omega)
            subst hp2eq; subst hl2eq
            have hpp : p1 ≠ p2 := fun h => huv (congrArg (Fin.castAdd m) h)
            have hll : l1 ≠ l2 := fun h => hne (congrArg (Fin.natAdd n) h)
            exact hno p1 p2 l1 l2 hpp hll ⟨h1, h2, h3, h4⟩
          · have h := congrArg Fin.val hcontra
            have hp2 := p2.isLt
            simp only [Fin.val_castAdd, Fin.val_natAdd] at h
            omega
        · have h := congrArg Fin.val hcontra
          have hp2 := p2.isLt
          simp only [Fin.val_castAdd, Fin.val_natAdd] at h
          omega
      · have h := congrArg Fin.val hcontra
        have hp1 := p1.isLt
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        omega
    · rcases hw2.1 with ⟨p2, l1', hcontra, _, _⟩ | ⟨p2, l1', rfl, hl1, h2⟩
      · have h := congrArg Fin.val hcontra
        have hp2 := p2.isLt
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        omega
      · have hl1eq : l1 = l1' := Fin.ext (by
          have h := congrArg Fin.val hl1
          simp only [Fin.val_natAdd] at h
          omega)
        subst hl1eq
        rcases hw1.2 with ⟨p1', l2, _, hcontra, _⟩ | ⟨p1', l2, hp1, rfl, h3⟩
        · have h := congrArg Fin.val hcontra
          have hp1 := p1.isLt
          simp only [Fin.val_castAdd, Fin.val_natAdd] at h
          omega
        · have hp1eq : p1 = p1' := Fin.ext (by simpa using congrArg Fin.val hp1)
          subst hp1eq
          rcases hw2.2 with ⟨p2', l2', hcontra, _, _⟩ | ⟨p2', l2', hp2, hl2, h4⟩
          · have h := congrArg Fin.val hcontra
            have hp2' := p2'.isLt
            simp only [Fin.val_castAdd, Fin.val_natAdd] at h
            omega
          · have hp2eq : p2 = p2' := Fin.ext (by simpa using congrArg Fin.val hp2)
            have hl2eq : l2 = l2' := Fin.ext (by
              have h := congrArg Fin.val hl2
              simp only [Fin.val_natAdd] at h
              omega)
            subst hp2eq; subst hl2eq
            have hpp : p1 ≠ p2 := fun h => hne (congrArg (Fin.castAdd m) h)
            have hll : l1 ≠ l2 := fun h => huv (congrArg (Fin.natAdd n) h)
            exact hno p1 p2 l1 l2 hpp hll ⟨h1, h3, h2, h4⟩
  have hGraphFun : ∀ x : Fin (n + m) → Bool,
      graphFun G ∅ x = decide (∃ (p : Fin n) (l : Fin m), I p l ∧
        x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true) := by
    intro x
    unfold graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      rcases huv with ⟨p, l, rfl, rfl, hpl⟩ | ⟨p, l, rfl, rfl, hpl⟩
      · exact ⟨p, l, hpl, hu, hv⟩
      · exact ⟨p, l, hpl, hv, hu⟩
    · rintro ⟨p, l, hpl, hp, hl⟩
      exact ⟨Fin.castAdd m p, Fin.natAdd n l, Or.inl ⟨p, l, rfl, rfl, hpl⟩, hp, hl⟩
  have hCfun : circuitFun (n + m) C = graphFun G ∅ := by
    funext x
    rw [hfun x, hGraphFun x]
  let S : Finset (Fin (n + m)) := Finset.univ.filter fun u => u.val < n
  have hS : ∀ u v, G.Adj u v → (u ∈ S ↔ v ∉ S) := by
    intro u v huv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hBip u v huv
  obtain ⟨D1, hD1, hFun1, hSize1, hTF1⟩ := topFormExists (n + m) G C hNo4 hC hCfun
  obtain ⟨D, hD, hFunD, hSizeD, hTF, hJunk⟩ := cleanExists (n + m) G S D1 hS hNo4 hD1 hFun1 hTF1
  have hNoDirty : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j := by
    intro j hj hop x hx
    by_contra hfalse
    have hgf : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hfalse
    have hmem : j ∈ junk G D := by
      unfold junk gatesWhere
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, hop, hj, x, hx, hgf⟩
    rw [hJunk] at hmem
    exact Finset.notMem_empty j hmem
  have hNoAndInAnd : ∀ i < D.gates.length, ∀ j < D.gates.length,
      (gateAt D i).op = GateOp.and → (gateAt D j).op = GateOp.and → ¬ InCone (n + m) D i j := by
    intro i hi j hj hiop hjop
    exact hTF i hi j hj hiop (hNoDirty i hi hiop) hjop
  have hConeLen : ∀ (gs : List Gate) (acc : List (List ℕ)),
      (gs.foldl (coneStep (n + m)) acc).length = acc.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g rest ih =>
      intro acc
      simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
      omega
  have hConePrefix : ∀ (gs : List Gate) (acc : List (List ℕ)) (i : ℕ),
      i < acc.length → (gs.foldl (coneStep (n + m)) acc).getD i [] = acc.getD i [] := by
    intro gs
    induction gs with
    | nil => intro acc i _; rfl
    | cons g rest ih =>
      intro acc i hi
      simp only [List.foldl_cons]
      have hlen : i < (coneStep (n + m) acc g).length := by
        simp only [coneStep, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (coneStep (n + m) acc g) i hlen]
      simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hConeAt : ∀ (j : ℕ), j < D.gates.length →
      (cones (n + m) D).getD j [] =
        (((gateAt D j).inputs.filter (fun w => decide (n + m ≤ w ∧ w < n + m + j))).flatMap
          (fun w => (w - (n + m)) :: (cones (n + m) D).getD (w - (n + m)) [])) := by
    intro j hj
    unfold cones
    have hsplit : D.gates = D.gates.take j ++ [D.gates[j]] ++ D.gates.drop (j + 1) := by
      have h1 : D.gates.take j ++ D.gates.drop j = D.gates := List.take_append_drop j D.gates
      have h2 : D.gates.drop j = D.gates[j] :: D.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
      calc D.gates = D.gates.take j ++ D.gates.drop j := h1.symm
        _ = D.gates.take j ++ (D.gates[j] :: D.gates.drop (j + 1)) := by rw [h2]
        _ = D.gates.take j ++ [D.gates[j]] ++ D.gates.drop (j + 1) := by simp
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := (D.gates.take j).foldl (coneStep (n + m)) []
    have haccLen : acc.length = j := by
      rw [hConeLen, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hjlt : j < (coneStep (n + m) acc D.gates[j]).length := by
      simp only [coneStep, List.length_append, List.length_cons, List.length_nil, haccLen]
      omega
    rw [hConePrefix (D.gates.drop (j + 1)) (coneStep (n + m) acc D.gates[j]) j hjlt]
    simp only [coneStep, haccLen, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp only [haccLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    have hgate : gateAt D j = D.gates[j] := by
      unfold gateAt
      simp [List.getD_eq_getElem?_getD, hj]
    rw [hgate]
    apply List.flatMap_congr
    intro w hw
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    have hwlt : w - (n + m) < acc.length := by omega
    congr 1
    symm
    change ((D.gates.foldl (coneStep (n + m)) []).getD (w - (n + m)) []) = acc.getD (w - (n + m)) []
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hwlt2 : w - (n + m) < (coneStep (n + m) acc D.gates[j]).length := by
      simp only [coneStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hConePrefix (D.gates.drop (j + 1)) _ _ hwlt2]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt]
  have hInConeDirect : ∀ (j i : ℕ), j < D.gates.length → i < j →
      n + m + i ∈ (gateAt D j).inputs → InCone (n + m) D i j := by
    intro j i hj hij hmem
    unfold InCone
    rw [hConeAt j hj]
    rw [List.mem_flatMap]
    refine ⟨n + m + i, ?_, ?_⟩
    · exact List.mem_filter.mpr ⟨hmem, decide_eq_true (by omega)⟩
    · simp
  have hInConeTrans : ∀ (j i k : ℕ), j < D.gates.length → i < j →
      n + m + i ∈ (gateAt D j).inputs → InCone (n + m) D k i → InCone (n + m) D k j := by
    intro j i k hj hij hmem hki
    unfold InCone at hki ⊢
    rw [hConeAt j hj]
    rw [List.mem_flatMap]
    refine ⟨n + m + i, ?_, ?_⟩
    · exact List.mem_filter.mpr ⟨hmem, decide_eq_true (by omega)⟩
    · have hsub : n + m + i - (n + m) = i := by omega
      rw [hsub]
      exact List.mem_cons_of_mem _ hki
  have hWiresLen : ∀ (gs : List Gate) (xs : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).length =
        xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons g rest ih =>
      intro xs
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega
  have hWiresPrefix : ∀ (gs : List Gate) (xs : List Bool) (w : ℕ),
      w < xs.length →
        (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) xs).getD w false =
          xs.getD w false := by
    intro gs
    induction gs with
    | nil => intro xs w _; rfl
    | cons g rest ih =>
      intro xs w hw
      simp only [List.foldl_cons]
      have hlen : w < (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]).length := by
        simp; omega
      rw [ih _ w hlen]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
  have hWireInput : ∀ (C' : Circuit) (w : ℕ) (hw : w < n + m) (x : Fin (n + m) → Bool),
      wireVal (n + m) C' w x = x ⟨w, hw⟩ := by
    intro C' w hw x
    unfold wireVal Circuit.wires
    have hlen : w < (List.ofFn x).length := by simp [hw]
    rw [hWiresPrefix C'.gates (List.ofFn x) w hlen]
    simp [List.getD_eq_getElem?_getD, hw]
  have hWireGate : ∀ (C' : Circuit) (j : ℕ) (hj : j < C'.gates.length) (x : Fin (n + m) → Bool),
      ReadsBack (n + m) C' →
      wireVal (n + m) C' (n + m + j) x =
        (gateAt C' j).op.eval ((gateAt C' j).inputs.map fun u => wireVal (n + m) C' u x) := by
    intro C' j hj x hrb
    unfold wireVal Circuit.wires
    have hsplit : C'.gates = C'.gates.take j ++ [C'.gates[j]] ++ C'.gates.drop (j + 1) := by
      have h1 : C'.gates.take j ++ C'.gates.drop j = C'.gates := List.take_append_drop j C'.gates
      have h2 : C'.gates.drop j = C'.gates[j] :: C'.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
      calc C'.gates = C'.gates.take j ++ C'.gates.drop j := h1.symm
        _ = C'.gates.take j ++ (C'.gates[j] :: C'.gates.drop (j + 1)) := by rw [h2]
        _ = C'.gates.take j ++ [C'.gates[j]] ++ C'.gates.drop (j + 1) := by simp
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := (C'.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)
    have haccLen : acc.length = n + m + j := by
      rw [hWiresLen, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hjlt : n + m + j < (acc ++ [C'.gates[j].op.eval (C'.gates[j].inputs.map fun i => acc.getD i false)]).length := by
      simp [haccLen]
    rw [hWiresPrefix (C'.gates.drop (j + 1)) _ (n + m + j) hjlt]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp only [haccLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    have hgate : gateAt C' j = C'.gates[j] := by
      unfold gateAt
      simp [List.getD_eq_getElem?_getD, hj]
    rw [hgate]
    congr 1
    apply List.map_congr_left
    intro u hu
    have hult : u < n + m + j := hrb j hj u (by rwa [hgate])
    have huacc : u < acc.length := by omega
    symm
    change ((C'.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD u false) =
      acc.getD u false
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hu2 : u < (acc ++ [C'.gates[j].op.eval (C'.gates[j].inputs.map fun i => acc.getD i false)]).length := by
      simp; omega
    rw [hWiresPrefix (C'.gates.drop (j + 1)) _ u hu2]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left huacc]
  have hPureOr : ∀ (w : ℕ), w < n + m + D.gates.length →
      (∀ i < D.gates.length, (w = n + m + i ∨ (∃ k < D.gates.length, w = n + m + k ∧ InCone (n + m) D i k)) →
        (gateAt D i).op ≠ GateOp.and) →
      ∃ R : Finset (Fin (n + m)), R.Nonempty ∧
        (∀ u ∈ R, ∀ x : Fin (n + m) → Bool, x u = true → wireVal (n + m) D w x = true) ∧
        (∀ (side : ℕ → Prop) [DecidablePred side],
          (∀ u ∈ R, side u.val) →
          ∃ T : Finset ℕ, w ∈ T ∧
            ∀ z ∈ T, (z < n + m ∧ side z) ∨
              ∃ i < D.gates.length, z = n + m + i ∧ (gateAt D i).op = GateOp.or ∧
                ∀ u ∈ (gateAt D i).inputs, u ∈ T) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hnoAnd
      by_cases hlt : w < n + m
      · refine ⟨{⟨w, hlt⟩}, Finset.singleton_nonempty _, ?_, ?_⟩
        · intro u hu x hx
          have hueq : u = ⟨w, hlt⟩ := Finset.mem_singleton.mp hu
          subst hueq
          rw [hWireInput D w hlt x]
          exact hx
        · intro side _ hside
          refine ⟨{w}, Finset.mem_singleton_self w, ?_⟩
          intro z hz
          rcases Finset.mem_singleton.mp hz with rfl
          exact Or.inl ⟨hlt, hside ⟨z, hlt⟩ (Finset.mem_singleton_self _)⟩
      · let j := w - (n + m)
        have hj : j < D.gates.length := by omega
        have hwj : w = n + m + j := by omega
        have hjnotand : (gateAt D j).op ≠ GateOp.and := hnoAnd j hj (Or.inl hwj)
        have hjmem : gateAt D j ∈ D.gates := by
          unfold gateAt
          simp [List.getD_eq_getElem?_getD, hj]
        have hjor : (gateAt D j).op = GateOp.or := by
          rcases hD.1 (gateAt D j) hjmem with h | h
          · exact False.elim (hjnotand h)
          · exact h
        have hjlen : (gateAt D j).inputs.length = 2 := hD.2.2 (gateAt D j) hjmem
        rcases List.length_eq_two.mp hjlen with ⟨a, b, hab⟩
        have ha_lt : a < w := by
          have := hD.2.1 j hj a (by rw [hab]; simp)
          omega
        have hb_lt : b < w := by
          have := hD.2.1 j hj b (by rw [hab]; simp)
          omega
        have hchildNoAnd : ∀ c, c ∈ (gateAt D j).inputs →
            ∀ i < D.gates.length,
              (c = n + m + i ∨ (∃ k < D.gates.length, c = n + m + k ∧ InCone (n + m) D i k)) →
              (gateAt D i).op ≠ GateOp.and := by
          intro c hc i hi hci
          have hclt : c < n + m + j := hD.2.1 j hj c hc
          rcases hci with rfl | ⟨k, hk, rfl, hik⟩
          · exact hnoAnd i hi (Or.inr ⟨j, hj, hwj, hInConeDirect j i hj (by omega) hc⟩)
          · exact hnoAnd i hi (Or.inr ⟨j, hj, hwj, hInConeTrans j k i hj (by omega) hc hik⟩)
        obtain ⟨Ra, hRa_ne, hRa_eval, hRa_T⟩ := ih a ha_lt (by omega) (hchildNoAnd a (by rw [hab]; simp))
        obtain ⟨Rb, hRb_ne, hRb_eval, hRb_T⟩ := ih b hb_lt (by omega) (hchildNoAnd b (by rw [hab]; simp))
        refine ⟨Ra ∪ Rb, hRa_ne.mono Finset.subset_union_left, ?_, ?_⟩
        · intro u hu x hx
          rw [hwj, hWireGate D j hj x hD.2.1, hjor, hab]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
            Bool.or_false, Bool.or_eq_true]
          rcases Finset.mem_union.mp hu with hua | hub
          · exact Or.inl (hRa_eval u hua x hx)
          · exact Or.inr (hRb_eval u hub x hx)
        · intro side _ hside
          obtain ⟨Ta, haTa, hTa⟩ := hRa_T side (fun u hu => hside u (Finset.mem_union_left Rb hu))
          obtain ⟨Tb, hbTb, hTb⟩ := hRb_T side (fun u hu => hside u (Finset.mem_union_right Ra hu))
          refine ⟨insert w (Ta ∪ Tb), Finset.mem_insert_self w _, ?_⟩
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · refine Or.inr ⟨j, hj, hwj, hjor, ?_⟩
            rw [hab]
            intro u hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · exact Finset.mem_insert_of_mem (Finset.mem_union_left Tb haTa)
            · exact Finset.mem_insert_of_mem (Finset.mem_union_right Ta hbTb)
          · rcases Finset.mem_union.mp hz' with hza | hzb
            · rcases hTa z hza with h | ⟨i, hi, hzi, hiop, hiin⟩
              · exact Or.inl h
              · exact Or.inr ⟨i, hi, hzi, hiop, fun u hu => Finset.mem_insert_of_mem (Finset.mem_union_left Tb (hiin u hu))⟩
            · rcases hTb z hzb with h | ⟨i, hi, hzi, hiop, hiin⟩
              · exact Or.inl h
              · exact Or.inr ⟨i, hi, hzi, hiop, fun u hu => Finset.mem_insert_of_mem (Finset.mem_union_right Ta (hiin u hu))⟩
  have hAndSides : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∃ a b, (gateAt D j).inputs = [a, b] ∧
        ((∃ Ta : Finset ℕ, a ∈ Ta ∧ ∀ z ∈ Ta, z < n ∨
            ∃ i < D.gates.length, z = n + m + i ∧ (gateAt D i).op = GateOp.or ∧
              ∀ u ∈ (gateAt D i).inputs, u ∈ Ta) ∧
         (∃ Tb : Finset ℕ, b ∈ Tb ∧ ∀ z ∈ Tb, (n ≤ z ∧ z < n + m) ∨
            ∃ i < D.gates.length, z = n + m + i ∧ (gateAt D i).op = GateOp.or ∧
              ∀ u ∈ (gateAt D i).inputs, u ∈ Tb) ∨
         (∃ Ta : Finset ℕ, a ∈ Ta ∧ ∀ z ∈ Ta, (n ≤ z ∧ z < n + m) ∨
            ∃ i < D.gates.length, z = n + m + i ∧ (gateAt D i).op = GateOp.or ∧
              ∀ u ∈ (gateAt D i).inputs, u ∈ Ta) ∧
         (∃ Tb : Finset ℕ, b ∈ Tb ∧ ∀ z ∈ Tb, z < n ∨
            ∃ i < D.gates.length, z = n + m + i ∧ (gateAt D i).op = GateOp.or ∧
              ∀ u ∈ (gateAt D i).inputs, u ∈ Tb)) := by
    intro j hj hjop
    have hjmem : gateAt D j ∈ D.gates := by
      unfold gateAt
      simp [List.getD_eq_getElem?_getD, hj]
    rcases List.length_eq_two.mp (hD.2.2 (gateAt D j) hjmem) with ⟨a, b, hab⟩
    have hchildNoAnd : ∀ c, c ∈ (gateAt D j).inputs →
        ∀ i < D.gates.length,
          (c = n + m + i ∨ (∃ k < D.gates.length, c = n + m + k ∧ InCone (n + m) D i k)) →
          (gateAt D i).op ≠ GateOp.and := by
      intro c hc i hi hci hiop
      have hclt : c < n + m + j := hD.2.1 j hj c hc
      rcases hci with rfl | ⟨k, hk, rfl, hik⟩
      · exact hNoAndInAnd i hi j hj hiop hjop (hInConeDirect j i hj (by omega) hc)
      · exact hNoAndInAnd i hi j hj hiop hjop (hInConeTrans j k i hj (by omega) hc hik)
    have ha_lt : a < n + m + j := hD.2.1 j hj a (by rw [hab]; simp)
    have hb_lt : b < n + m + j := hD.2.1 j hj b (by rw [hab]; simp)
    obtain ⟨Ra, ⟨u0, hu0⟩, hRa_eval, hRa_T⟩ := hPureOr a (by omega) (hchildNoAnd a (by rw [hab]; simp))
    obtain ⟨Rb, ⟨v0, hv0⟩, hRb_eval, hRb_T⟩ := hPureOr b (by omega) (hchildNoAnd b (by rw [hab]; simp))
    have hpair : ∀ u ∈ Ra, ∀ v ∈ Rb, u.val < n ↔ ¬ v.val < n := by
      intro u hu v hv
      have hgateTrue : gateVal (n + m) D j (pairInput u v) = true := by
        change wireVal (n + m) D (n + m + j) (pairInput u v) = true
        rw [hWireGate D j hj (pairInput u v) hD.2.1, hjop, hab]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true, Bool.and_eq_true]
        exact ⟨hRa_eval u hu (pairInput u v) (by simp [pairInput]),
               hRb_eval v hv (pairInput u v) (by simp [pairInput])⟩
      have hgf : graphFun G ∅ (pairInput u v) = true := hNoDirty j hj hjop (pairInput u v) hgateTrue
      unfold graphFun at hgf
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq] at hgf
      rcases hgf with ⟨w1, w2, hadj, hw1, hw2⟩
      simp only [pairInput, decide_eq_true_eq] at hw1 hw2
      rcases hw1 with rfl | rfl <;> rcases hw2 with rfl | rfl
      · exact False.elim (G.ne_of_adj hadj rfl)
      · exact hBip w1 w2 hadj
      · have h := hBip w1 w2 hadj
        tauto
      · exact False.elim (G.ne_of_adj hadj rfl)
    refine ⟨a, b, hab, ?_⟩
    by_cases hu0lt : u0.val < n
    · have hRb_ge : ∀ v ∈ Rb, n ≤ v.val ∧ v.val < n + m := by
        intro v hv
        have := (hpair u0 hu0 v hv).mp hu0lt
        exact ⟨by omega, v.isLt⟩
      have hRa_lt : ∀ u ∈ Ra, u.val < n := by
        intro u hu
        have hv0n : ¬ v0.val < n := by have := hRb_ge v0 hv0; omega
        exact (hpair u hu v0 hv0).mpr hv0n
      obtain ⟨Ta, haTa, hTa⟩ := hRa_T (fun z => z < n) hRa_lt
      obtain ⟨Tb, hbTb, hTb⟩ := hRb_T (fun z => n ≤ z ∧ z < n + m) hRb_ge
      exact Or.inl ⟨⟨Ta, haTa, fun z hz => (hTa z hz).imp (fun h => h.2) id⟩,
                    ⟨Tb, hbTb, fun z hz => (hTb z hz).imp (fun h => h.2) id⟩⟩
    · have hRb_lt : ∀ v ∈ Rb, v.val < n := by
        intro v hv
        by_contra hnv
        exact hu0lt ((hpair u0 hu0 v hv).mpr hnv)
      have hRa_ge : ∀ u ∈ Ra, n ≤ u.val ∧ u.val < n + m := by
        intro u hu
        have := hRb_lt v0 hv0
        have : ¬ u.val < n := fun h => by
          have := (hpair u hu v0 hv0).mp h
          exact this (hRb_lt v0 hv0)
        exact ⟨by omega, u.isLt⟩
      obtain ⟨Ta, haTa, hTa⟩ := hRa_T (fun z => n ≤ z ∧ z < n + m) hRa_ge
      obtain ⟨Tb, hbTb, hTb⟩ := hRb_T (fun z => z < n) hRb_lt
      exact Or.inr ⟨⟨Ta, haTa, fun z hz => (hTa z hz).imp (fun h => h.2) id⟩,
                    ⟨Tb, hbTb, fun z hz => (hTb z hz).imp (fun h => h.2) id⟩⟩
  let P : Finset ℕ := (Finset.range (n + m + D.gates.length)).filter fun w =>
    ∃ T : Finset ℕ, w ∈ T ∧ ∀ z ∈ T, z < n ∨
      ∃ i < D.gates.length, z = n + m + i ∧ (gateAt D i).op = GateOp.or ∧
        ∀ u ∈ (gateAt D i).inputs, u ∈ T
  let L : Finset ℕ := (Finset.range (n + m + D.gates.length)).filter fun w =>
    ∃ T : Finset ℕ, w ∈ T ∧ ∀ z ∈ T, (n ≤ z ∧ z < n + m) ∨
      ∃ i < D.gates.length, z = n + m + i ∧ (gateAt D i).op = GateOp.or ∧
        ∀ u ∈ (gateAt D i).inputs, u ∈ T
  have hP_closed : ∀ w ∈ P, w < n ∨ ∃ i < D.gates.length, w = n + m + i ∧
      (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ P := by
    intro w hw
    obtain ⟨_, T, hwT, hT⟩ := Finset.mem_filter.mp hw
    rcases hT w hwT with h | ⟨i, hi, rfl, hiop, hiin⟩
    · exact Or.inl h
    · refine Or.inr ⟨i, hi, rfl, hiop, ?_⟩
      intro u hu
      have hult : u < n + m + i := hD.2.1 i hi u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), T, hiin u hu, hT⟩
  have hL_closed : ∀ w ∈ L, (n ≤ w ∧ w < n + m) ∨ ∃ i < D.gates.length, w = n + m + i ∧
      (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ L := by
    intro w hw
    obtain ⟨_, T, hwT, hT⟩ := Finset.mem_filter.mp hw
    rcases hT w hwT with h | ⟨i, hi, rfl, hiop, hiin⟩
    · exact Or.inl h
    · refine Or.inr ⟨i, hi, rfl, hiop, ?_⟩
      intro u hu
      have hult : u < n + m + i := hD.2.1 i hi u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), T, hiin u hu, hT⟩
  let orientGate : Gate → Gate := fun g =>
    if g.op = GateOp.and then
      match g.inputs with
      | [a, b] => if a ∈ P ∧ b ∈ L then g else ⟨GateOp.and, [b, a]⟩
      | _ => g
    else g
  let F : Circuit := ⟨D.gates.map orientGate, D.output⟩
  have hF_len : F.gates.length = D.gates.length := List.length_map _
  have hF_gateAt : ∀ i < D.gates.length, gateAt F i = orientGate (gateAt D i) := by
    intro i hi
    unfold gateAt F
    simp [List.getD_eq_getElem?_getD, hi]
  have hF_or : ∀ i < D.gates.length, (gateAt D i).op = GateOp.or → gateAt F i = gateAt D i := by
    intro i hi hiop
    rw [hF_gateAt i hi]
    dsimp only [orientGate]
    rw [hiop]
    simp
  have hF_ao2 : IsAO2 (n + m) F := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      rcases hD.1 g0 hg0 with hop | hop
      · rcases List.length_eq_two.mp (hD.2.2 g0 hg0) with ⟨a, b, hab⟩
        dsimp only [orientGate]
        rw [hop, hab]
        simp only [↓reduceIte]
        split_ifs
        · exact Or.inl hop
        · exact Or.inl rfl
      · dsimp only [orientGate]
        rw [hop]
        simp [hop]
    · intro j hj u hu
      rw [hF_len] at hj
      rw [hF_gateAt j hj] at hu
      have hgmem : gateAt D j ∈ D.gates := by
        unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
      rcases hD.1 (gateAt D j) hgmem with hop | hop
      · rcases List.length_eq_two.mp (hD.2.2 (gateAt D j) hgmem) with ⟨a, b, hab⟩
        dsimp only [orientGate] at hu
        rw [hop, hab] at hu
        simp only [↓reduceIte] at hu
        split_ifs at hu
        · exact hD.2.1 j hj u hu
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · exact hD.2.1 j hj u (by rw [hab]; simp)
          · exact hD.2.1 j hj u (by rw [hab]; simp)
      · dsimp only [orientGate] at hu
        rw [hop] at hu
        simp only [reduceCtorEq, ↓reduceIte] at hu
        exact hD.2.1 j hj u hu
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      rcases hD.1 g0 hg0 with hop | hop
      · rcases List.length_eq_two.mp (hD.2.2 g0 hg0) with ⟨a, b, hab⟩
        dsimp only [orientGate]
        rw [hop, hab]
        simp only [↓reduceIte]
        split_ifs
        · exact hD.2.2 g0 hg0
        · rfl
      · dsimp only [orientGate]
        rw [hop]
        simp [hD.2.2 g0 hg0]
  have hF_wires : ∀ x : List Bool, F.wires x = D.wires x := by
    intro x
    unfold Circuit.wires F
    dsimp only
    suffices h : ∀ (gs : List Gate) (acc : List Bool),
        (gs.map orientGate).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc =
        gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc from
      h D.gates x
    intro gs
    induction gs with
    | nil => intro acc; rfl
    | cons g rest ih =>
      intro acc
      simp only [List.map_cons, List.foldl_cons]
      have heval : (orientGate g).op.eval ((orientGate g).inputs.map fun i => acc.getD i false) =
          g.op.eval (g.inputs.map fun i => acc.getD i false) := by
        dsimp only [orientGate]
        by_cases hgop : g.op = GateOp.and
        · simp only [hgop, ↓reduceIte]
          cases hgin : g.inputs with
          | nil => simp [hgop, hgin]
          | cons a tl =>
            cases tl with
            | nil => simp [hgop, hgin]
            | cons b tl2 =>
              cases tl2 with
              | nil =>
                dsimp only
                split_ifs
                · simp [hgop, hgin]
                · simp [GateOp.eval, Bool.and_comm]
              | cons c tl3 => simp [hgop, hgin]
        · simp only [hgop, ↓reduceIte]
      rw [heval]
      exact ih _
  have hF_fun : ∀ x : Fin (n + m) → Bool,
      circuitFun (n + m) F x = decide (∃ (p : Fin n) (l : Fin m), I p l ∧
        x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true) := by
    intro x
    have h1 : circuitFun (n + m) F x = circuitFun (n + m) D x := by
      unfold circuitFun Circuit.eval
      rw [hF_wires]
    rw [h1, hFunD, hGraphFun]
  have hF_size : F.size ≤ C.size := by
    simp only [Circuit.size] at hSize1 hSizeD ⊢
    omega
  refine ⟨F, P, L, hF_ao2, hF_fun, hF_size, ?_, ?_, ?_⟩
  · intro w hw
    rcases hP_closed w hw with h | ⟨i, hi, hwi, hiop, hiin⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, by omega, hwi, by rw [hF_or i hi hiop]; exact hiop,
        by rw [hF_or i hi hiop]; exact hiin⟩
  · intro w hw
    rcases hL_closed w hw with h | ⟨i, hi, hwi, hiop, hiin⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, by omega, hwi, by rw [hF_or i hi hiop]; exact hiop,
        by rw [hF_or i hi hiop]; exact hiin⟩
  · intro j hj hjop
    rw [hF_len] at hj
    have hDj_op : (gateAt D j).op = GateOp.and := by
      have hgmem : gateAt D j ∈ D.gates := by
        unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
      rcases hD.1 (gateAt D j) hgmem with hop | hop
      · exact hop
      · rw [hF_or j hj hop, hop] at hjop
        exact False.elim (by cases hjop)
    obtain ⟨a, b, hab, hside⟩ := hAndSides j hj hDj_op
    have halt : a < n + m + D.gates.length := by
      have := hD.2.1 j hj a (by rw [hab]; simp)
      omega
    have hblt : b < n + m + D.gates.length := by
      have := hD.2.1 j hj b (by rw [hab]; simp)
      omega
    rcases hside with ⟨hPa, hLb⟩ | ⟨hLa, hPb⟩
    · have haP : a ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr halt, hPa⟩
      have hbL : b ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hblt, hLb⟩
      refine ⟨a, b, ?_, haP, hbL⟩
      rw [hF_gateAt j hj]
      dsimp only [orientGate]
      rw [hDj_op, hab]
      simp [haP, hbL, hab]
    · have haL : a ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr halt, hLa⟩
      have hbP : b ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hblt, hPb⟩
      by_cases hboth : a ∈ P ∧ b ∈ L
      · refine ⟨a, b, ?_, hboth.1, hboth.2⟩
        rw [hF_gateAt j hj]
        dsimp only [orientGate]
        rw [hDj_op, hab]
        simp [hboth, hab]
      · refine ⟨b, a, ?_, hbP, haL⟩
        rw [hF_gateAt j hj]
        dsimp only [orientGate]
        rw [hDj_op, hab]
        simp [hboth]
