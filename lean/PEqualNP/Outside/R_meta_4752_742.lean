import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4752_742
    (h1 : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true))
    (h2 : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size = (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ)) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x3 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false ∧ PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false ∧ ¬PEqualNP.CircuitMoves.WireBelowOutput (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3)) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ)) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x3 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false ∧ PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  intro h
  rcases h with ⟨C, hsize, hshape, hfun, k, hkand, hkcone, hktrue, hkop⟩
  by_cases h26 : C.size ≤ 26
  · exact h1 ⟨C, h26, hshape, hfun⟩
  have h27 : C.size = 27 := by omega
  by_cases hdirty : ∀ b : Fin 2, ¬PEqualNP.CircuitMoves.WireBelowOutput 14 C (PEqualNP.TopForm.opnd C k b)
  · exact h2 ⟨C, h27, hshape, hfun, k, hkand, hkcone, hktrue, fun b => ⟨(hkop b).1, (hkop b).2, hdirty b⟩⟩
  push Not at hdirty
  rcases hdirty with ⟨b, hw0_below⟩
  have hgetD_append_left : ∀ {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α),
      i < l₁.length → (l₁ ++ l₂).getD i d = l₁.getD i d := by
    intro α l₁ l₂ i d hi
    induction l₁ generalizing i with
    | nil => simp at hi
    | cons a as ih =>
      cases i with
      | zero => simp
      | succ j => simpa using ih j (by simpa using hi)
  have hgetD_append_right : ∀ {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α),
      l₁.length ≤ i → (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
    intro α l₁ l₂ i d hi
    induction l₁ generalizing i with
    | nil => simp
    | cons a as ih =>
      cases i with
      | zero => simp at hi
      | succ j => simpa [Nat.succ_sub_succ] using ih j (by simpa using hi)
  have hgetD_snoc_eq : ∀ {α : Type} (l : List α) (a d : α),
      (l ++ [a]).getD l.length d = a := by
    intro α l a d
    rw [hgetD_append_right l [a] l.length d (Nat.le_refl l.length)]
    simp
  have hgetD_some : ∀ {α : Type} (l : List α) (i : ℕ) (d a : α),
      l[i]? = Option.some a → l.getD i d = a := by
    intro α l i d a ha
    induction l generalizing i with
    | nil => simp at ha
    | cons x xs ih =>
      cases i with
      | zero => simpa using ha
      | succ j => simpa using ih j (by simpa using ha)
  have hgetD_out : ∀ {α : Type} (l : List α) (i : ℕ) (d : α),
      l.length ≤ i → l.getD i d = d := by
    intro α l i d hi
    induction l generalizing i with
    | nil => simp
    | cons x xs ih =>
      cases i with
      | zero => simp at hi
      | succ j => simpa using ih j (by simpa using hi)
  have hgetElem?_snoc : ∀ {α : Type} (l : List α) (a : α) (m : ℕ),
      (l ++ [a])[m]? = if m < l.length then l[m]? else if m = l.length then Option.some a else Option.none := by
    intro α l a m
    induction l generalizing m with
    | nil =>
      cases m with
      | zero => rfl
      | succ _ => rfl
    | cons x xs ih =>
      cases m with
      | zero => simp
      | succ j => simpa [Nat.succ_lt_succ_iff, Nat.succ_eq_add_one] using ih j
  have htake_succ : ∀ {α : Type} (l : List α) (j : ℕ) (hj : j < l.length),
      l.take (j + 1) = l.take j ++ [l[j]] := by
    intro α l
    induction l with
    | nil => intro j hj; simp at hj
    | cons x xs ih =>
      intro j hj
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [List.take_succ_cons, List.cons_append, List.getElem_cons_succ]
        rw [ih j' (by simpa using hj)]
  have htake_drop : ∀ {α : Type} (l : List α) (j : ℕ), l.take j ++ l.drop j = l := by
    intro α l
    induction l with
    | nil => intro j; simp
    | cons x xs ih =>
      intro j
      cases j with
      | zero => rfl
      | succ j' => simp [ih j']
  have hand_eval : ∀ p q : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [p, q] = (p && q) := by
    intro p q; cases p <;> cases q <;> rfl
  have hor_eval : ∀ p q : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [p, q] = (p || q) := by
    intro p q; cases p <;> cases q <;> rfl
  let wireStep : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hwire_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool),
      (gs.foldl wireStep ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp
    | cons g rest ih =>
      intro ws
      have h1 := ih (wireStep ws g)
      simp only [List.foldl_cons, List.length_cons]
      have hlen : (wireStep ws g).length = ws.length + 1 := by simp [wireStep]
      omega
  have hwire_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool) (w : ℕ),
      w < ws.length → (gs.foldl wireStep ws).getD w false = ws.getD w false := by
    intro gs
    induction gs with
    | nil => intro ws w _; rfl
    | cons g rest ih =>
      intro ws w hw
      simp only [List.foldl_cons]
      have hlen : (wireStep ws g).length = ws.length + 1 := by simp [wireStep]
      rw [ih (wireStep ws g) w (by omega)]
      exact hgetD_append_left ws [g.op.eval (g.inputs.map fun i => ws.getD i false)] w false hw
  have hklt : k < C.gates.length := by
    by_contra hge
    have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C k =
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ :=
      hgetD_out C.gates k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ (Nat.le_of_not_lt hge)
    rw [hgat] at hkand
    cases hkand
  let gk : PEqualNP.CircuitLowerBounds.Gate := C.gates[k]'hklt
  have hgk_some : C.gates[k]? = Option.some gk := List.getElem?_eq_getElem hklt
  have hgk_at : PEqualNP.MetaComplexity.NestedCover.gateAt C k = gk :=
    hgetD_some C.gates k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ gk hgk_some
  have hgk_and : gk.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    rw [← hgk_at]; exact hkand
  have hgk_shape := hshape k gk hgk_some
  rcases hgk_shape.2 with ⟨ka, kb, hgk_in, _, hka_lt, hkb_lt⟩
  let w0 : ℕ := PEqualNP.TopForm.opnd C k b
  have hw0_mem : w0 = ka ∨ w0 = kb := by
    rcases b with ⟨bv, hbv⟩
    cases bv with
    | zero =>
      left
      change (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 0 0 = ka
      rw [hgk_at, hgk_in]; rfl
    | succ bv' =>
      cases bv' with
      | zero =>
        right
        change (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 1 0 = kb
        rw [hgk_at, hgk_in]; rfl
      | succ _ => omega
  have hw0_lt : w0 < 14 + k := by
    rcases hw0_mem with h | h <;> omega
  have hout_lt : C.output < 14 + C.gates.length := by
    by_contra hge
    have hx : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14))) = Bool.true := by
      apply (hfun (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14))).mpr
      refine ⟨(0 : Fin 7), (0 : Fin 7), Or.inl rfl, ?_, ?_⟩ <;> rfl
    have hlen : (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14)))).length =
        14 + C.gates.length := by
      change (C.gates.foldl wireStep (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14)))).length =
        14 + C.gates.length
      rw [hwire_len, List.length_ofFn]
    have hfalse : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14))) = Bool.false :=
      hgetD_out _ C.output false (by omega)
    rw [hfalse] at hx
    cases hx
  let initMap : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  have hinit : ∀ w < 14, initMap.getD w 0 = w := by
    intro w hw
    interval_cases w <;> rfl
  let step : (ℕ × List PEqualNP.CircuitLowerBounds.Gate × List ℕ) →
      PEqualNP.CircuitLowerBounds.Gate →
      (ℕ × List PEqualNP.CircuitLowerBounds.Gate × List ℕ) :=
    fun st g =>
      let idx := st.1
      let outG := st.2.1
      let wmap := st.2.2
      if idx = k then
        (idx + 1, outG, wmap ++ [wmap.getD w0 0])
      else
        let u' := wmap.getD (g.inputs.getD 0 0) 0
        let v' := wmap.getD (g.inputs.getD 1 0) 0
        if u' = v' then
          (idx + 1, outG, wmap ++ [u'])
        else
          (idx + 1, outG ++ [⟨g.op, [u', v']⟩], wmap ++ [14 + outG.length])
  have hmain : ∀ j : ℕ, j ≤ C.gates.length →
      let st := (C.gates.take j).foldl step (0, [], initMap)
      let outG := st.2.1
      let wmap := st.2.2
      st.1 = j ∧
      wmap.length = 14 + j ∧
      (if k < j then 1 else 0) + outG.length ≤ j ∧
      (∀ w < 14 + j, wmap.getD w 0 < 14 + outG.length) ∧
      (∀ (m : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate),
        outG[m]? = Option.some g' →
        (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a' b', g'.inputs = [a', b'] ∧ a' ≠ b' ∧ a' < 14 + m ∧ b' < 14 + m) ∧
      (∀ (x : Fin 14 → Bool) (w : ℕ), w < 14 + j →
        ((C.gates.take j).foldl wireStep (List.ofFn x)).getD w false = Bool.true →
        (outG.foldl wireStep (List.ofFn x)).getD (wmap.getD w 0) false = Bool.true) ∧
      (∀ (x : Fin 14 → Bool), C.eval (List.ofFn x) = Bool.false →
        ∀ (w : ℕ), w < 14 + j →
        (outG.foldl wireStep (List.ofFn x)).getD (wmap.getD w 0) false =
          ((C.gates.take j).foldl wireStep (List.ofFn x)).getD w false) := by
    intro j
    induction j with
    | zero =>
      intro _
      dsimp only
      rw [List.take_zero, List.foldl_nil]
      dsimp only
      refine ⟨rfl, rfl, by simp, ?_, ?_, ?_, ?_⟩
      · intro w hw
        rw [hinit w hw]; omega
      · intro m g' hm
        simp at hm
      · intro x w hw hval
        rw [hinit w hw]
        exact hval
      · intro x _ w hw
        rw [hinit w hw]
    | succ j ih =>
      intro hjle
      have hj : j < C.gates.length := by omega
      have hih := ih (by omega)
      dsimp only at hih ⊢
      set st_p := (C.gates.take j).foldl step (0, [], initMap)
      set out_p := st_p.2.1
      set map_p := st_p.2.2
      rcases hih with ⟨hidx, hmlen, hsize_p, hmbnd, hoshape, hmono, hsound⟩
      set g := C.gates[j]'hj
      have hg_some : C.gates[j]? = Option.some g := List.getElem?_eq_getElem hj
      have hg_sh := hshape j g hg_some
      have hg_op := hg_sh.1
      rcases hg_sh.2 with ⟨ga, gb, hg_in, _, hga_lt, hgb_lt⟩
      have htake_len : (C.gates.take j).length = j := by
        simp [Nat.min_eq_left (Nat.le_of_lt hj)]
      have hstep_eq : (C.gates.take (j + 1)).foldl step (0, [], initMap) = step st_p g := by
        rw [htake_succ C.gates j hj, List.foldl_append]
        rfl
      have how_succ : ∀ x : Fin 14 → Bool,
          (C.gates.take (j + 1)).foldl wireStep (List.ofFn x) =
            ((C.gates.take j).foldl wireStep (List.ofFn x)) ++
              [g.op.eval [((C.gates.take j).foldl wireStep (List.ofFn x)).getD ga false,
                          ((C.gates.take j).foldl wireStep (List.ofFn x)).getD gb false]] := by
        intro x
        rw [htake_succ C.gates j hj, List.foldl_append]
        change ((C.gates.take j).foldl wireStep (List.ofFn x)) ++
            [g.op.eval (g.inputs.map fun i => ((C.gates.take j).foldl wireStep (List.ofFn x)).getD i false)] = _
        rw [hg_in]
        rfl
      have how_len : ∀ x : Fin 14 → Bool,
          ((C.gates.take j).foldl wireStep (List.ofFn x)).length = 14 + j := by
        intro x
        rw [hwire_len, List.length_ofFn, htake_len]
      have how_at : ∀ x : Fin 14 → Bool,
          ((C.gates.take (j + 1)).foldl wireStep (List.ofFn x)).getD (14 + j) false =
            g.op.eval [((C.gates.take j).foldl wireStep (List.ofFn x)).getD ga false,
                       ((C.gates.take j).foldl wireStep (List.ofFn x)).getD gb false] := by
        intro x
        rw [how_succ x, ← how_len x, hgetD_snoc_eq]
      have hmap_at : ∀ v : ℕ, (map_p ++ [v]).getD (14 + j) 0 = v := by
        intro v
        rw [← hmlen, hgetD_snoc_eq]
      have how_eq_full : ∀ (x : Fin 14 → Bool) (w : ℕ), w < 14 + j →
          ((C.gates.take j).foldl wireStep (List.ofFn x)).getD w false =
            (C.wires (List.ofFn x)).getD w false := by
        intro x w hw
        have hsp : C.wires (List.ofFn x) =
            (C.gates.drop j).foldl wireStep ((C.gates.take j).foldl wireStep (List.ofFn x)) := by
          change C.gates.foldl wireStep (List.ofFn x) = _
          rw [← List.foldl_append, htake_drop]
        rw [hsp]
        exact (hwire_prefix (C.gates.drop j) _ w (by rw [how_len]; exact hw)).symm
      rw [hstep_eq]
      by_cases hjk : j = k
      · have hst_val : step st_p g = (j + 1, out_p, map_p ++ [map_p.getD w0 0]) := by
          dsimp only [step]
          rw [hidx]
          simp only [hjk, ite_true]
          rfl
        rw [hst_val]
        dsimp only
        have hg_eq_gk : g = gk := by
          have hs : Option.some g = Option.some gk := by
            rw [← hg_some, hjk, hgk_some]
          exact Option.some.inj hs
        have hga_eq : ga = ka := by
          have h1 : [ga, gb] = [ka, kb] := by rw [← hg_in, hg_eq_gk, hgk_in]
          exact (List.cons.inj h1).1
        have hgb_eq : gb = kb := by
          have h1 : [ga, gb] = [ka, kb] := by rw [← hg_in, hg_eq_gk, hgk_in]
          exact (List.cons.inj (List.cons.inj h1).2).1
        refine ⟨rfl, by simp [hmlen]; omega, ?_, ?_, hoshape, ?_, ?_⟩
        · split_ifs at hsize_p ⊢ <;> omega
        · intro w hw
          by_cases hwlt : w < 14 + j
          · rw [hgetD_append_left map_p _ w 0 (by omega)]
            exact hmbnd w hwlt
          · have hweq : w = 14 + j := by omega
            rw [hweq, hmap_at]
            exact hmbnd w0 (by omega)
        · intro x w hw hval
          by_cases hwlt : w < 14 + j
          · rw [how_succ x, hgetD_append_left _ _ w false (by rw [how_len]; exact hwlt)] at hval
            rw [hgetD_append_left map_p _ w 0 (by omega)]
            exact hmono x w hwlt hval
          · have hweq : w = 14 + j := by omega
            rw [hweq, how_at x] at hval
            rw [hweq, hmap_at]
            rw [hg_eq_gk, hgk_and, hand_eval] at hval
            have hw0_t : ((C.gates.take j).foldl wireStep (List.ofFn x)).getD w0 false = Bool.true := by
              rw [hga_eq, hgb_eq] at hval
              rcases hw0_mem with h | h <;> rw [h]
              · exact ((Bool.and_eq_true _ _).mp hval).1
              · exact ((Bool.and_eq_true _ _).mp hval).2
            exact hmono x w0 (by omega) hw0_t
        · intro x hx0 w hw
          by_cases hwlt : w < 14 + j
          · rw [how_succ x, hgetD_append_left _ _ w false (by rw [how_len]; exact hwlt)]
            rw [hgetD_append_left map_p _ w 0 (by omega)]
            exact hsound x hx0 w hwlt
          · have hweq : w = 14 + j := by omega
            rw [hweq, how_at x, hmap_at]
            have hw0_f : ((C.gates.take j).foldl wireStep (List.ofFn x)).getD w0 false = Bool.false := by
              rw [how_eq_full x w0 (by omega)]
              cases hv : (C.wires (List.ofFn x)).getD w0 false with
              | false => rfl
              | true =>
                have ht := hw0_below x hv
                rw [hx0] at ht
                cases ht
            rw [hsound x hx0 w0 (by omega), hw0_f, hg_eq_gk, hgk_and, hand_eval, hga_eq, hgb_eq]
            rcases hw0_mem with h | h <;> rw [← h, hw0_f] <;> simp
      · let u' := map_p.getD ga 0
        let v' := map_p.getD gb 0
        have hu'_eq : st_p.2.2.getD (g.inputs.getD 0 0) 0 = u' := by rw [hg_in]; rfl
        have hv'_eq : st_p.2.2.getD (g.inputs.getD 1 0) 0 = v' := by rw [hg_in]; rfl
        by_cases huv : u' = v'
        · have hst_val : step st_p g = (j + 1, out_p, map_p ++ [u']) := by
            dsimp only [step]
            rw [hidx]
            simp only [hjk, ite_false, hu'_eq, hv'_eq, huv, ite_true]
            rfl
          rw [hst_val]
          dsimp only
          refine ⟨rfl, by simp [hmlen]; omega, ?_, ?_, hoshape, ?_, ?_⟩
          · split_ifs at hsize_p ⊢ <;> omega
          · intro w hw
            by_cases hwlt : w < 14 + j
            · rw [hgetD_append_left map_p _ w 0 (by omega)]
              exact hmbnd w hwlt
            · have hweq : w = 14 + j := by omega
              rw [hweq, hmap_at]
              exact hmbnd ga hga_lt
          · intro x w hw hval
            by_cases hwlt : w < 14 + j
            · rw [how_succ x, hgetD_append_left _ _ w false (by rw [how_len]; exact hwlt)] at hval
              rw [hgetD_append_left map_p _ w 0 (by omega)]
              exact hmono x w hwlt hval
            · have hweq : w = 14 + j := by omega
              rw [hweq, how_at x] at hval
              rw [hweq, hmap_at]
              rcases hg_op with hop | hop
              · rw [hop, hand_eval] at hval
                exact hmono x ga hga_lt ((Bool.and_eq_true _ _).mp hval).1
              · rw [hop, hor_eval] at hval
                rcases (Bool.or_eq_true _ _).mp hval with ha | hb
                · exact hmono x ga hga_lt ha
                · rw [huv]
                  exact hmono x gb hgb_lt hb
          · intro x hx0 w hw
            by_cases hwlt : w < 14 + j
            · rw [how_succ x, hgetD_append_left _ _ w false (by rw [how_len]; exact hwlt)]
              rw [hgetD_append_left map_p _ w 0 (by omega)]
              exact hsound x hx0 w hwlt
            · have hweq : w = 14 + j := by omega
              rw [hweq, how_at x, hmap_at]
              have hsa : (out_p.foldl wireStep (List.ofFn x)).getD u' false =
                  ((C.gates.take j).foldl wireStep (List.ofFn x)).getD ga false :=
                hsound x hx0 ga hga_lt
              have hsb : (out_p.foldl wireStep (List.ofFn x)).getD v' false =
                  ((C.gates.take j).foldl wireStep (List.ofFn x)).getD gb false :=
                hsound x hx0 gb hgb_lt
              rw [← huv] at hsb
              rw [← hsa, ← hsb]
              rcases hg_op with hop | hop
              · rw [hop, hand_eval]; cases (out_p.foldl wireStep (List.ofFn x)).getD u' false <;> rfl
              · rw [hop, hor_eval]; cases (out_p.foldl wireStep (List.ofFn x)).getD u' false <;> rfl
        · let gnew : PEqualNP.CircuitLowerBounds.Gate := ⟨g.op, [u', v']⟩
          have hst_val : step st_p g = (j + 1, out_p ++ [gnew], map_p ++ [14 + out_p.length]) := by
            dsimp only [step]
            rw [hidx]
            simp only [hjk, ite_false, hu'_eq, hv'_eq, huv, ite_false]
            rfl
          rw [hst_val]
          dsimp only
          have hnw_len : ∀ x : Fin 14 → Bool,
              (out_p.foldl wireStep (List.ofFn x)).length = 14 + out_p.length := by
            intro x
            rw [hwire_len, List.length_ofFn]
          have hnw_succ : ∀ x : Fin 14 → Bool,
              (out_p ++ [gnew]).foldl wireStep (List.ofFn x) =
                (out_p.foldl wireStep (List.ofFn x)) ++
                  [g.op.eval [(out_p.foldl wireStep (List.ofFn x)).getD u' false,
                              (out_p.foldl wireStep (List.ofFn x)).getD v' false]] := by
            intro x
            rw [List.foldl_append]
            rfl
          have hnw_at : ∀ x : Fin 14 → Bool,
              ((out_p ++ [gnew]).foldl wireStep (List.ofFn x)).getD (14 + out_p.length) false =
                g.op.eval [(out_p.foldl wireStep (List.ofFn x)).getD u' false,
                           (out_p.foldl wireStep (List.ofFn x)).getD v' false] := by
            intro x
            rw [hnw_succ x, ← hnw_len x, hgetD_snoc_eq]
          refine ⟨rfl, by simp [hmlen]; omega, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            split_ifs at hsize_p ⊢ <;> omega
          · intro w hw
            simp only [List.length_append, List.length_singleton]
            by_cases hwlt : w < 14 + j
            · rw [hgetD_append_left map_p _ w 0 (by omega)]
              have := hmbnd w hwlt
              omega
            · have hweq : w = 14 + j := by omega
              rw [hweq, hmap_at]
              omega
          · intro m g' hm
            rw [hgetElem?_snoc] at hm
            by_cases hmlt : m < out_p.length
            · simp only [hmlt, ite_true] at hm
              exact hoshape m g' hm
            · simp only [hmlt, ite_false] at hm
              by_cases hmeq : m = out_p.length
              · simp only [hmeq, ite_true] at hm
                have hg'_eq : g' = gnew := (Option.some.inj hm).symm
                rw [hg'_eq]
                refine ⟨hg_op, u', v', rfl, huv, ?_, ?_⟩
                · rw [hmeq]; exact hmbnd ga hga_lt
                · rw [hmeq]; exact hmbnd gb hgb_lt
              · simp only [hmeq, ite_false] at hm
                cases hm
          · intro x w hw hval
            by_cases hwlt : w < 14 + j
            · rw [how_succ x, hgetD_append_left _ _ w false (by rw [how_len]; exact hwlt)] at hval
              rw [hnw_succ x]
              rw [hgetD_append_left map_p _ w 0 (by omega)]
              rw [hgetD_append_left _ _ (map_p.getD w 0) false (by rw [hnw_len]; exact hmbnd w hwlt)]
              exact hmono x w hwlt hval
            · have hweq : w = 14 + j := by omega
              rw [hweq, how_at x] at hval
              rw [hweq, hmap_at, hnw_at x]
              rcases hg_op with hop | hop
              · rw [hop, hand_eval] at hval ⊢
                have ha := hmono x ga hga_lt ((Bool.and_eq_true _ _).mp hval).1
                have hb := hmono x gb hgb_lt ((Bool.and_eq_true _ _).mp hval).2
                rw [ha, hb]; rfl
              · rw [hop, hor_eval] at hval ⊢
                rcases (Bool.or_eq_true _ _).mp hval with ha | hb
                · rw [hmono x ga hga_lt ha]; rfl
                · rw [hmono x gb hgb_lt hb]; simp
          · intro x hx0 w hw
            by_cases hwlt : w < 14 + j
            · rw [how_succ x, hnw_succ x]
              rw [hgetD_append_left _ _ w false (by rw [how_len]; exact hwlt)]
              rw [hgetD_append_left map_p _ w 0 (by omega)]
              rw [hgetD_append_left _ _ (map_p.getD w 0) false (by rw [hnw_len]; exact hmbnd w hwlt)]
              exact hsound x hx0 w hwlt
            · have hweq : w = 14 + j := by omega
              rw [hweq, how_at x, hmap_at, hnw_at x]
              rw [hsound x hx0 ga hga_lt, hsound x hx0 gb hgb_lt]
  have hfin := hmain C.gates.length (Nat.le_refl C.gates.length)
  have htake_all : C.gates.take C.gates.length = C.gates := List.take_length
  dsimp only at hfin
  rw [htake_all] at hfin
  set st := C.gates.foldl step (0, [], initMap)
  rcases hfin with ⟨_, _, hsz, _, hsh, hmo, hso⟩
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨st.2.1, st.2.2.getD C.output 0⟩
  have hC'_size : C'.size ≤ 26 := by
    change st.2.1.length ≤ 26
    simp only [hklt, ite_true] at hsz
    change C.gates.length = 27 at h27
    omega
  have hC'_fun : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = Bool.true ↔
      ∃ (x3 : Fin 7) (x4 : Fin 7),
        (x3 = x4 ∨ x3 = x4 + (1 : Fin 7) ∨ x3 = x4 + (3 : Fin 7)) ∧
        x (Fin.castAdd 7 x3) = Bool.true ∧ x (Fin.natAdd 7 x4) = Bool.true := by
    intro x
    rw [← hfun x]
    constructor
    · intro h'
      cases hc : C.eval (List.ofFn x) with
      | true => rfl
      | false =>
        have hEq := hso x hc C.output hout_lt
        change C'.eval (List.ofFn x) = C.eval (List.ofFn x) at hEq
        rw [hEq, hc] at h'
        cases h'
    · intro hc
      exact hmo x C.output hout_lt hc
  exact h1 ⟨C', hC'_size, hsh, hC'_fun⟩
