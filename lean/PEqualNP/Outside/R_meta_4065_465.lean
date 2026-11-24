import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4065_465
    (hSamePin : ∀ (C : Circuit) (a b : ℕ),
      have N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
      have P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
      have isA : ℕ → Prop := fun g => (gateAt C g).op = GateOp.and
      have gv : ℕ → ℕ → Bool := fun g r => gateVal 11 C g (fun i => r.testBit i.val)
      have cl : ℕ → Prop := fun g => ∀ r ∈ N, gv g r = false
      have ic : ℕ → ℕ → Prop := InCone 11 C
      have op : ℕ → Fin 2 → ℕ := opnd C
      IsAO2 11 C → C.size ≤ 21 → a < b → b < C.size → isA a → isA b →
      (∀ j < C.size, isA j → (cl j ↔ j ≠ a ∧ j ≠ b)) →
      (∀ j < C.size, isA j → cl j → ∀ k < C.size, isA k → ¬ ic j k) →
      ¬ ic a b → ¬ ic b a →
      (∃ t < C.size, isA t ∧ cl t ∧ ∃ s s' : Fin 2, s ≠ s' ∧
        OrReaches 11 C (op t s) a ∧ OrReaches 11 C (op t s) b ∧
        ∃ v ∈ orIn 11 C (op t s'), ∀ r ∈ N, r.testBit v.val = true → gv a r = false ∧ gv b r = false) →
      (∀ r ∈ P, circuitFun 11 C (fun i => r.testBit i.val) = true) →
      (∀ r ∈ N, circuitFun 11 C (fun i => r.testBit i.val) = false) →
      False)
    (hOppPure : ∀ (C : Circuit) (a b : ℕ),
      have N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
      have P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
      have isA : ℕ → Prop := fun g => (gateAt C g).op = GateOp.and
      have gv : ℕ → ℕ → Bool := fun g r => gateVal 11 C g (fun i => r.testBit i.val)
      have cl : ℕ → Prop := fun g => ∀ r ∈ N, gv g r = false
      have ic : ℕ → ℕ → Prop := InCone 11 C
      have op : ℕ → Fin 2 → ℕ := opnd C
      IsAO2 11 C → C.size ≤ 21 → a < b → b < C.size → isA a → isA b →
      (∀ j < C.size, isA j → (cl j ↔ j ≠ a ∧ j ≠ b)) →
      (∀ j < C.size, isA j → cl j → ∀ k < C.size, isA k → ¬ ic j k) →
      ¬ ic a b → ¬ ic b a →
      (∃ t < C.size, isA t ∧ cl t ∧ ∃ s s' : Fin 2, s ≠ s' ∧
        OrReaches 11 C (op t s) a ∧ OrReaches 11 C (op t s') b ∧
        orIn 11 C (op t s) = ∅ ∧ orIn 11 C (op t s') = ∅ ∧
        ∀ r : ℕ, gv t r = (gv a r && gv b r)) →
      (∀ r ∈ P, circuitFun 11 C (fun i => r.testBit i.val) = true) →
      (∀ r ∈ N, circuitFun 11 C (fun i => r.testBit i.val) = false) →
      False)
    (hOppMixed : ∀ (C : Circuit) (a b : ℕ),
      have N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
      have P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
      have isA : ℕ → Prop := fun g => (gateAt C g).op = GateOp.and
      have gv : ℕ → ℕ → Bool := fun g r => gateVal 11 C g (fun i => r.testBit i.val)
      have cl : ℕ → Prop := fun g => ∀ r ∈ N, gv g r = false
      have ic : ℕ → ℕ → Prop := InCone 11 C
      have op : ℕ → Fin 2 → ℕ := opnd C
      IsAO2 11 C → C.size ≤ 21 → a ≠ b → a < C.size → b < C.size → isA a → isA b →
      (∀ j < C.size, isA j → (cl j ↔ j ≠ a ∧ j ≠ b)) →
      (∀ j < C.size, isA j → cl j → ∀ k < C.size, isA k → ¬ ic j k) →
      ¬ ic a b → ¬ ic b a →
      (∃ t < C.size, isA t ∧ cl t ∧ ∃ s s' : Fin 2, s ≠ s' ∧
        OrReaches 11 C (op t s) a ∧ OrReaches 11 C (op t s') b ∧
        (∀ r ∈ N, gv a r = false ∨ gv b r = false) ∧
        ∃ v ∈ orIn 11 C (op t s), ∀ r ∈ N, r.testBit v.val = true → gv b r = false) →
      (∀ r ∈ P, circuitFun 11 C (fun i => r.testBit i.val) = true) →
      (∀ r ∈ N, circuitFun 11 C (fun i => r.testBit i.val) = false) →
      False) :
    have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => ∀ x6 ∈ x1, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4 x5 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false; have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 → x6.size ≤ (21 : ℕ) → x7 < x8 → x8 < x6.size → x3 x6 x7 → x3 x6 x8 → (∀ x15 < x6.size, x3 x6 x15 → (x4 x6 x15 ↔ x15 ≠ x7 ∧ x15 ≠ x8)) → (∀ x16 < x6.size, x3 x6 x16 → x4 x6 x16 → ∀ x20 < x6.size, x3 x6 x20 → ¬x5 x6 x16 x20) → ¬x5 x6 x7 x8 → ¬x5 x6 x8 x7 → (∃ x19 < x6.size, x3 x6 x19 ∧ x4 x6 x19 ∧ x5 x6 x7 x19 ∧ x5 x6 x8 x19) → (∀ x20 ∈ x2, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x22 : Fin (11 : ℕ)) => x20.testBit ↑x22) = Bool.true) → (∀ x21 ∈ x1, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x23 : Fin (11 : ℕ)) => x21.testBit ↑x23) = Bool.false) → False := by
  letI : DecidableEq GateOp := gateOpDecEq
  dsimp only
  intro C a b hAO hSize hab hb_lt ha_and hb_and hJunk hTop hNoAB hNoBA hShared hPos hNeg
  let n : ℕ := 11
  let N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
  let P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
  let gv : ℕ → ℕ → Bool := fun g r => gateVal 11 C g (fun i => r.testBit i.val)
  let cl : ℕ → Prop := fun g => ∀ r ∈ N, gv g r = false
  have ha_lt : a < C.gates.length := lt_trans hab hb_lt
  have hb_lt' : b < C.gates.length := hb_lt
  -- Section 1: Circuit evaluation helpers
  have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by
    intro b1 b2; cases b1 <;> cases b2 <;> rfl
  have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by
    intro b1 b2; cases b1 <;> cases b2 <;> rfl
  let wstep : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wstep_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl wstep w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      have hl : (wstep w g).length = w.length + 1 := by
        simp only [wstep, List.length_append, List.length_singleton]
      rw [hl, List.length_cons]; omega
  have wstep_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl wstep w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      have hi' : i < (wstep w g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [List.foldl_cons, ih (wstep w g) i hi']
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have gate_eval_raw : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl wstep w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl wstep w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro w j hj; simp at hj
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have hlt : w.length < (wstep w g).length := by
          simp only [wstep, List.length_append, List.length_singleton]; omega
        rw [Nat.add_zero, wstep_lt gs (wstep w g) w.length hlt]
        have hlast : (wstep w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [List.getElem_cons_zero, hlast]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        by_cases hi : i < w.length
        · rw [if_pos hi, wstep_lt gs (wstep w g) i (by
            simp only [wstep, List.length_append, List.length_singleton]; omega)]
          simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i),
            Option.getD_none]
      | succ j =>
        have hj' : j < gs.length := by
          simp only [List.length_cons] at hj; omega
        have key := ih (wstep w g) j hj'
        have hl : (wstep w g).length = w.length + 1 := by
          simp only [wstep, List.length_append, List.length_singleton]
        rw [hl, show w.length + 1 + j = w.length + (j + 1) by omega] at key
        rw [List.getElem_cons_succ]
        exact key
  have wire_input : ∀ (x : Fin n → Bool) (i : Fin n),
      wireVal n C i.val x = x i := by
    intro x i
    change (C.gates.foldl wstep (List.ofFn x)).getD i.val false = x i
    rw [wstep_lt C.gates (List.ofFn x) i.val (by simp only [List.length_ofFn]; exact i.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some,
      Fin.eta]
  have wire_beyond : ∀ (x : Fin n → Bool) (w : ℕ), n + C.gates.length ≤ w →
      wireVal n C w x = false := by
    intro x w hw
    change (C.gates.foldl wstep (List.ofFn x)).getD w false = false
    have hlen : (C.gates.foldl wstep (List.ofFn x)).length = n + C.gates.length := by
      rw [wstep_len, List.length_ofFn]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (C.gates.foldl wstep (List.ofFn x)).length ≤ w),
      Option.getD_none]
  have hgate : ∀ (j : ℕ) (hj : j < C.gates.length), gateAt C j = C.gates[j] := by
    intro j hj
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have gate_inputs_pair : ∀ j : ℕ, j < C.gates.length →
      (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
      opnd C j 0 < n + j ∧ opnd C j 1 < n + j ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
    intro j hj
    have hmem : gateAt C j ∈ C.gates := by
      rw [hgate j hj]; exact List.getElem_mem hj
    have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) hmem
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := hAO.1 (gateAt C j) hmem
    have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hAO.2.1 j hj
    have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
      cases h0 : (gateAt C j).inputs with
      | nil => simp [h0] at hlen
      | cons x l1 =>
        cases h1 : l1 with
        | nil => simp [h0, h1] at hlen
        | cons y l2 =>
          cases h2 : l2 with
          | nil =>
            have h01 : opnd C j 0 = x := by
              change ((gateAt C j).inputs).getD 0 0 = x
              rw [h0]; rfl
            have h11 : opnd C j 1 = y := by
              change ((gateAt C j).inputs).getD 1 0 = y
              rw [h0, h1]; rfl
            rw [h01, h11]
          | cons c l3 => simp [h0, h1, h2] at hlen
    refine ⟨hin, hrb _ ?_, hrb _ ?_, hop⟩
    · rw [hin]; exact List.mem_cons_self
    · rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have gateVal_eval_pair : ∀ (j : ℕ), j < C.gates.length → ∀ (x : Fin n → Bool),
      gateVal n C j x = (gateAt C j).op.eval [wireVal n C (opnd C j 0) x, wireVal n C (opnd C j 1) x] := by
    intro j hj x
    change (C.gates.foldl wstep (List.ofFn x)).getD (n + j) false = _
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    have hraw := gate_eval_raw C.gates (List.ofFn x) j hj
    rw [hlen] at hraw
    rw [hraw, ← hgate j hj]
    obtain ⟨hin, h0, h1, _⟩ := gate_inputs_pair j hj
    rw [hin]
    simp only [List.map_cons, List.map_nil, if_pos h0, if_pos h1]
    rfl
  have gateVal_and : ∀ (j : ℕ), j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ x : Fin n → Bool,
      gateVal n C j x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
    intro j hj hop x
    rw [gateVal_eval_pair j hj x, hop, eval_and]
  have gateVal_or : ∀ (j : ℕ), j < C.gates.length → (gateAt C j).op = GateOp.or →
      ∀ x : Fin n → Bool,
      gateVal n C j x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
    intro j hj hop x
    rw [gateVal_eval_pair j hj x, hop, eval_or]
  -- Section 2: orSets, cones, OrReaches, InCone, orIn
  have orStep_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; rfl
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      have hl : (orStep n cs g).length = cs.length + 1 := by
        dsimp only [orStep]
        simp only [List.length_append, List.length_singleton]
      rw [hl, List.length_cons]; omega
  have orStep_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (i : ℕ), i < cs.length →
      (gs.foldl (orStep n) cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      have hi' : i < (orStep n cs g).length := by
        dsimp only [orStep]
        simp only [List.length_append, List.length_singleton]; omega
      rw [List.foldl_cons, ih (orStep n cs g) i hi']
      dsimp only [orStep]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have orSets_raw : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < gs.length),
      (gs.foldl (orStep n) cs).getD (cs.length + j) [] =
        (cs.length + j) :: (if gs[j].op = GateOp.or then
          (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cs.length + j)))).flatMap
            (fun w => (gs.foldl (orStep n) cs).getD (w - n) []) else []) := by
    intro gs
    induction gs with
    | nil => intro cs j hj; simp at hj
    | cons g gs ih =>
      intro cs j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have hlt : cs.length < (orStep n cs g).length := by
          dsimp only [orStep]
          simp only [List.length_append, List.length_singleton]; omega
        rw [Nat.add_zero, orStep_lt gs (orStep n cs g) cs.length hlt]
        have hlast : (orStep n cs g).getD cs.length [] =
            cs.length :: (if g.op = GateOp.or then
              (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
                (fun w => cs.getD (w - n) []) else []) := by
          dsimp only [orStep]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [List.getElem_cons_zero, hlast]
        congr 1
        by_cases hor : g.op = GateOp.or
        · rw [if_pos hor, if_pos hor]
          refine List.flatMap_congr fun w hw => ?_
          rw [List.mem_filter] at hw
          have hwn : w - n < cs.length := by
            have := of_decide_eq_true hw.2; omega
          have hwn' : w - n < (orStep n cs g).length := by
            dsimp only [orStep]
            simp only [List.length_append, List.length_singleton]; omega
          rw [orStep_lt gs (orStep n cs g) (w - n) hwn']
          dsimp only [orStep]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
        · rw [if_neg hor, if_neg hor]
      | succ j =>
        have hj' : j < gs.length := by simp only [List.length_cons] at hj; omega
        have key := ih (orStep n cs g) j hj'
        have hl : (orStep n cs g).length = cs.length + 1 := by
          dsimp only [orStep]
          simp only [List.length_append, List.length_singleton]
        rw [hl, show cs.length + 1 + j = cs.length + (j + 1) by omega] at key
        rw [List.getElem_cons_succ]
        exact key
  have orSets_len : (orSets n C).length = C.gates.length := by
    change (C.gates.foldl (orStep n) []).length = C.gates.length
    rw [orStep_len, List.length_nil, Nat.zero_add]
  have orSets_getD : ∀ j : ℕ, j < C.gates.length →
      (orSets n C).getD j [] =
        j :: (if (gateAt C j).op = GateOp.or then
          ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
            (fun w => (orSets n C).getD (w - n) []) else []) := by
    intro j hj
    change (C.gates.foldl (orStep n) []).getD j [] = _
    have hraw := orSets_raw C.gates [] j hj
    rw [List.length_nil, Nat.zero_add, ← hgate j hj] at hraw
    exact hraw
  have coneStep_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; rfl
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      have hl : (coneStep n cs g).length = cs.length + 1 := by
        dsimp only [coneStep]
        simp only [List.length_append, List.length_singleton]
      rw [hl, List.length_cons]; omega
  have coneStep_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (i : ℕ), i < cs.length →
      (gs.foldl (coneStep n) cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      have hi' : i < (coneStep n cs g).length := by
        dsimp only [coneStep]
        simp only [List.length_append, List.length_singleton]; omega
      rw [List.foldl_cons, ih (coneStep n cs g) i hi']
      dsimp only [coneStep]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have cones_raw : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < gs.length),
      (gs.foldl (coneStep n) cs).getD (cs.length + j) [] =
        (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cs.length + j)))).flatMap
          (fun w => (w - n) :: (gs.foldl (coneStep n) cs).getD (w - n) []) := by
    intro gs
    induction gs with
    | nil => intro cs j hj; simp at hj
    | cons g gs ih =>
      intro cs j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have hlt : cs.length < (coneStep n cs g).length := by
          dsimp only [coneStep]
          simp only [List.length_append, List.length_singleton]; omega
        rw [Nat.add_zero, coneStep_lt gs (coneStep n cs g) cs.length hlt]
        have hlast : (coneStep n cs g).getD cs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
              (fun w => (w - n) :: cs.getD (w - n) []) := by
          dsimp only [coneStep]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [List.getElem_cons_zero, hlast]
        refine List.flatMap_congr fun w hw => ?_
        rw [List.mem_filter] at hw
        have hwn : w - n < cs.length := by
          have := of_decide_eq_true hw.2; omega
        have hwn' : w - n < (coneStep n cs g).length := by
          dsimp only [coneStep]
          simp only [List.length_append, List.length_singleton]; omega
        rw [coneStep_lt gs (coneStep n cs g) (w - n) hwn']
        dsimp only [coneStep]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
      | succ j =>
        have hj' : j < gs.length := by simp only [List.length_cons] at hj; omega
        have key := ih (coneStep n cs g) j hj'
        have hl : (coneStep n cs g).length = cs.length + 1 := by
          dsimp only [coneStep]
          simp only [List.length_append, List.length_singleton]
        rw [hl, show cs.length + 1 + j = cs.length + (j + 1) by omega] at key
        rw [List.getElem_cons_succ]
        exact key
  have cones_getD : ∀ j : ℕ, j < C.gates.length →
      (cones n C).getD j [] =
        ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
          (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
    intro j hj
    change (C.gates.foldl (coneStep n) []).getD j [] = _
    have hraw := cones_raw C.gates [] j hj
    rw [List.length_nil, Nat.zero_add, ← hgate j hj] at hraw
    exact hraw
  have orReaches_lt : ∀ w g : ℕ, OrReaches n C w g →
      w < n + C.gates.length ∧ g < C.gates.length ∧ g ≤ w - n := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro g hrec
      obtain ⟨hnw, hmem⟩ := hrec
      by_cases hlt : w - n < C.gates.length
      · have hwj : w = n + (w - n) := by omega
        rw [orSets_getD (w - n) hlt, List.mem_cons] at hmem
        rcases hmem with rfl | hmem'
        · exact ⟨by omega, hlt, le_rfl⟩
        · split_ifs at hmem' with hor
          · rw [List.mem_flatMap] at hmem'
            obtain ⟨w', hw'f, hw'm⟩ := hmem'
            rw [List.mem_filter] at hw'f
            have hw'_b := of_decide_eq_true hw'f.2
            have hrec' : OrReaches n C w' g := ⟨hw'_b.1, hw'm⟩
            have hsub := ih w' (by omega) g hrec'
            omega
          · simp at hmem'
      · exfalso
        have hlen : (orSets n C).length ≤ w - n := by rw [orSets_len]; omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, Option.getD_none,
          List.not_mem_nil] at hmem
  have orReaches_self : ∀ j : ℕ, j < C.gates.length → OrReaches n C (n + j) j := by
    intro j hj
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left, orSets_getD j hj]
    exact List.mem_cons_self
  have orReaches_step_or : ∀ (j : ℕ), j < C.gates.length → (gateAt C j).op = GateOp.or →
      ∀ (b : Fin 2) (g : ℕ), OrReaches n C (opnd C j b) g → OrReaches n C (n + j) g := by
    intro j hj hor b g hrec
    have hlt := (orReaches_lt (opnd C j b) g hrec).1
    obtain ⟨hin, h0, h1, _⟩ := gate_inputs_pair j hj
    have hmem_in : opnd C j b ∈ (gateAt C j).inputs := by
      rw [hin]; fin_cases b
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    have hlt_j : opnd C j b < n + j := by
      fin_cases b <;> assumption
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left, orSets_getD j hj, List.mem_cons]
    right
    rw [if_pos hor, List.mem_flatMap]
    refine ⟨opnd C j b, List.mem_filter.mpr ⟨hmem_in, decide_eq_true ⟨hrec.1, hlt_j⟩⟩, hrec.2⟩
  have orReaches_cases : ∀ (j : ℕ), j < C.gates.length → ∀ g : ℕ,
      OrReaches n C (n + j) g →
      g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ b : Fin 2, OrReaches n C (opnd C j b) g) := by
    intro j hj g hrec
    obtain ⟨_, hmem⟩ := hrec
    rw [Nat.add_sub_cancel_left, orSets_getD j hj, List.mem_cons] at hmem
    rcases hmem with rfl | hmem'
    · exact Or.inl rfl
    · split_ifs at hmem' with hor
      · right
        refine ⟨hor, ?_⟩
        rw [List.mem_flatMap] at hmem'
        obtain ⟨w', hw'f, hw'm⟩ := hmem'
        rw [List.mem_filter] at hw'f
        have hw'_b := of_decide_eq_true hw'f.2
        obtain ⟨hin, _, _, _⟩ := gate_inputs_pair j hj
        rw [hin, List.mem_cons, List.mem_singleton] at hw'f
        rcases hw'f.1 with rfl | rfl
        · exact ⟨0, hw'_b.1, hw'm⟩
        · exact ⟨1, hw'_b.1, hw'm⟩
      · simp at hmem'
  have orReaches_val : ∀ (w g : ℕ) (x : Fin n → Bool),
      OrReaches n C w g → gateVal n C g x = true → wireVal n C w x = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro g x hrec hgx
      have hwlt := (orReaches_lt w g hrec).1
      have hwn : n ≤ w := hrec.1
      let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      rw [hwj] at hrec ⊢
      rcases orReaches_cases j hj g hrec with rfl | ⟨hor, b, hrec'⟩
      · exact hgx
      · change gateVal n C j x = true
        rw [gateVal_or j hj hor x, Bool.or_eq_true]
        have hlt_b : opnd C j b < w := by
          obtain ⟨_, h0, h1, _⟩ := gate_inputs_pair j hj
          fin_cases b
          · change opnd C j 0 < w; omega
          · change opnd C j 1 < w; omega
        have hvb := ih (opnd C j b) hlt_b g x hrec' hgx
        fin_cases b
        · exact Or.inl hvb
        · exact Or.inr hvb
  have orReaches_inCone_aux : ∀ (w g : ℕ), OrReaches n C w g →
      w < n + C.gates.length ∧ (g = w - n ∨ InCone n C g (w - n)) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro g hrec
      have hwlt := (orReaches_lt w g hrec).1
      have hwn : n ≤ w := hrec.1
      let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      refine ⟨hwlt, ?_⟩
      change g = j ∨ InCone n C g j
      rw [hwj] at hrec
      rcases orReaches_cases j hj g hrec with rfl | ⟨hor, b, hrec'⟩
      · exact Or.inl rfl
      · right
        obtain ⟨hin, h0, h1, _⟩ := gate_inputs_pair j hj
        have hlt_b : opnd C j b < n + j := by
          fin_cases b <;> assumption
        have ihb := ih (opnd C j b) (by omega) g hrec'
        have hbn : n ≤ opnd C j b := hrec'.1
        have hmem_in : opnd C j b ∈ (gateAt C j).inputs := by
          rw [hin]; fin_cases b
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ List.mem_cons_self
        change g ∈ (cones n C).getD j []
        rw [cones_getD j hj, List.mem_flatMap]
        refine ⟨opnd C j b, List.mem_filter.mpr ⟨hmem_in, decide_eq_true ⟨hbn, hlt_b⟩⟩, ?_⟩
        rw [List.mem_cons]
        rcases ihb.2 with rfl | hc
        · exact Or.inl rfl
        · exact Or.inr hc
  have orReaches_inCone : ∀ (c : ℕ), c < C.gates.length → ∀ (b : Fin 2) (g : ℕ),
      OrReaches n C (opnd C c b) g → InCone n C g c := by
    intro c hc b g hrec
    obtain ⟨hin, h0, h1, _⟩ := gate_inputs_pair c hc
    have hbn : n ≤ opnd C c b := hrec.1
    have hba : opnd C c b < n + c := by fin_cases b <;> assumption
    have hmem_in : opnd C c b ∈ (gateAt C c).inputs := by
      rw [hin]; fin_cases b
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    have hsub := (orReaches_inCone_aux (opnd C c b) g hrec).2
    change g ∈ (cones n C).getD c []
    rw [cones_getD c hc, List.mem_flatMap]
    refine ⟨opnd C c b, List.mem_filter.mpr ⟨hmem_in, decide_eq_true ⟨hbn, hba⟩⟩, ?_⟩
    rw [List.mem_cons]
    exact hsub
  have orIn_val : ∀ (w : ℕ) (i : Fin n) (x : Fin n → Bool),
      i ∈ orIn n C w → x i = true → wireVal n C w x = true := by
    intro w i x hi hx
    dsimp only [orIn] at hi
    rw [Finset.mem_filter] at hi
    rcases hi.2 with heq | ⟨k, hk, hrec, _, hkin⟩
    · rw [← heq, wire_input x i]; exact hx
    · refine orReaches_val w k x hrec ?_
      obtain ⟨_, _, _, hop⟩ := gate_inputs_pair k hk
      obtain ⟨hin, _, _, _⟩ := gate_inputs_pair k hk
      rw [gateVal_or k hk (by assumption), Bool.or_eq_true]
      rw [hin, List.mem_cons, List.mem_singleton] at hkin
      rcases hkin with heq0 | heq1
      · left; rw [← heq0, wire_input x i]; exact hx
      · right; rw [← heq1, wire_input x i]; exact hx
  have orIn_input : ∀ i : Fin n, orIn n C i.val = {i} := by
    intro i
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · dsimp only [orIn]; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ i, Or.inl rfl⟩
    · intro j hj
      dsimp only [orIn] at hj
      rw [Finset.mem_filter] at hj
      rcases hj.2 with hji | ⟨k, _, hrec, _, _⟩
      · exact Fin.ext hji
      · exfalso; have := hrec.1; omega
  have orIn_or_eq : ∀ j : ℕ, j < C.gates.length → (gateAt C j).op = GateOp.or →
      orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
    intro j hj hor
    ext i
    dsimp only [orIn]
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨_, hij | ⟨k, hk, hrec, hkor, hkin⟩⟩
      · have := i.isLt; omega
      · rcases orReaches_cases j hj k hrec with hkj | ⟨_, s, hrec'⟩
        · rw [hkj] at hkin
          obtain ⟨hin, _, _, _⟩ := gate_inputs_pair j hj
          rw [hin, List.mem_cons, List.mem_singleton] at hkin
          rcases hkin with h0 | h1
          · exact Or.inl ⟨Finset.mem_univ i, Or.inl h0⟩
          · exact Or.inr ⟨Finset.mem_univ i, Or.inl h1⟩
        · fin_cases s
          · exact Or.inl ⟨Finset.mem_univ i, Or.inr ⟨k, hk, hrec', hkor, hkin⟩⟩
          · exact Or.inr ⟨Finset.mem_univ i, Or.inr ⟨k, hk, hrec', hkor, hkin⟩⟩
    · rintro (⟨_, h0 | ⟨k, hk, hrec, hkor, hkin⟩⟩ | ⟨_, h1 | ⟨k, hk, hrec, hkor, hkin⟩⟩)
      · refine ⟨Finset.mem_univ i, Or.inr ⟨j, hj, orReaches_self j hj, hor, ?_⟩⟩
        obtain ⟨hin, _, _, _⟩ := gate_inputs_pair j hj
        rw [hin, h0]; exact List.mem_cons_self
      · exact ⟨Finset.mem_univ i, Or.inr ⟨k, hk, orReaches_step_or j hj hor 0 k hrec, hkor, hkin⟩⟩
      · refine ⟨Finset.mem_univ i, Or.inr ⟨j, hj, orReaches_self j hj, hor, ?_⟩⟩
        obtain ⟨hin, _, _, _⟩ := gate_inputs_pair j hj
        rw [hin, h1]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact ⟨Finset.mem_univ i, Or.inr ⟨k, hk, orReaches_step_or j hj hor 1 k hrec, hkor, hkin⟩⟩
  have extract_and_from_wire : ∀ (w : ℕ), w < n + C.gates.length → ∀ x : Fin n → Bool,
      wireVal n C w x = true → (∀ i ∈ orIn n C w, x i = false) →
      ∃ g < C.gates.length, OrReaches n C w g ∧ (gateAt C g).op = GateOp.and ∧
        gateVal n C g x = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw x hwx hor_false
      by_cases hwn : w < n
      · exfalso
        let i : Fin n := ⟨w, hwn⟩
        have him : i ∈ orIn n C w := by
          rw [show w = i.val from rfl, orIn_input i]; exact Finset.mem_singleton_self i
        have hxi := hor_false i him
        rw [show w = i.val from rfl, wire_input x i] at hwx
        rw [hwx] at hxi; cases hxi
      · let j := w - n
        have hj : j < C.gates.length := by omega
        have hwj : w = n + j := by omega
        obtain ⟨_, h0, h1, hop⟩ := gate_inputs_pair j hj
        rcases hop with hand | hor
        · refine ⟨j, hj, ?_, hand, ?_⟩
          · rw [hwj]; exact orReaches_self j hj
          · change wireVal n C (n + j) x = true; rw [← hwj]; exact hwx
        · have hgx : gateVal n C j x = true := by
            change wireVal n C (n + j) x = true; rw [← hwj]; exact hwx
          rw [gateVal_or j hj hor x, Bool.or_eq_true] at hgx
          have hsub : orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) :=
            orIn_or_eq j hj hor
          rw [← hwj] at hsub
          rcases hgx with hb0 | hb1
          · obtain ⟨g, hg, hrec, hga, hgv⟩ := ih (opnd C j 0) (by omega) (by omega) x hb0 (fun i hi => by
              apply hor_false i
              rw [hsub]; exact Finset.mem_union_left _ hi)
            exact ⟨g, hg, by rw [hwj]; exact orReaches_step_or j hj hor 0 g hrec, hga, hgv⟩
          · obtain ⟨g, hg, hrec, hga, hgv⟩ := ih (opnd C j 1) (by omega) (by omega) x hb1 (fun i hi => by
              apply hor_false i
              rw [hsub]; exact Finset.mem_union_right _ hi)
            exact ⟨g, hg, by rw [hwj]; exact orReaches_step_or j hj hor 1 g hrec, hga, hgv⟩
  -- Section 3: Cone, wire decomposition, and gate reduction
  have inCone_lt : ∀ j : ℕ, j < C.gates.length → ∀ k : ℕ, InCone n C k j →
      k < j ∧ k < C.gates.length := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj k hkj
      change k ∈ (cones n C).getD j [] at hkj
      rw [cones_getD j hj, List.mem_flatMap] at hkj
      obtain ⟨w, hwf, hwm⟩ := hkj
      rw [List.mem_filter] at hwf
      have hwb := of_decide_eq_true hwf.2
      rw [List.mem_cons] at hwm
      rcases hwm with rfl | hrec
      · exact ⟨by omega, by omega⟩
      · have hsub := ih (w - n) (by omega) (by omega) k hrec
        exact ⟨by omega, hsub.2⟩
  have inCone_trans : ∀ j : ℕ, j < C.gates.length → ∀ m k : ℕ,
      InCone n C k m → InCone n C m j → InCone n C k j := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj m k hkm hmj
      change m ∈ (cones n C).getD j [] at hmj
      rw [cones_getD j hj, List.mem_flatMap] at hmj
      obtain ⟨w, hwf, hwm⟩ := hmj
      have hwf' := hwf
      rw [List.mem_filter] at hwf'
      have hwb := of_decide_eq_true hwf'.2
      rw [List.mem_cons] at hwm
      have hkw : InCone n C k (w - n) := by
        rcases hwm with rfl | hrec
        · exact hkm
        · exact ih (w - n) (by omega) (by omega) m k hkm hrec
      change k ∈ (cones n C).getD j []
      rw [cones_getD j hj, List.mem_flatMap]
      refine ⟨w, hwf, List.mem_cons.mpr (Or.inr hkw)⟩
  obtain ⟨t, ht_lt, ht_and, ht_cl, hat, hbt⟩ := hShared
  have only_ab_in_t : ∀ k : ℕ, InCone n C k t → (gateAt C k).op = GateOp.and →
      k = a ∨ k = b := by
    intro k hkt hk_and
    have hk_lt : k < C.gates.length := (inCone_lt t ht_lt k hkt).2
    by_contra hnot
    have hne : k ≠ a ∧ k ≠ b := ⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩
    have hcl_k : cl k := (hJunk k hk_lt hk_and).mpr hne
    exact hTop k hk_lt hk_and hcl_k t ht_lt ht_and hkt
  have inCone_to_orReaches_wire : ∀ w : ℕ, w < n + C.gates.length → ∀ g : ℕ, (g = a ∨ g = b) →
      ∀ j : ℕ, w = n + j → InCone n C j t → (g = j ∨ InCone n C g j) → OrReaches n C w g := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw g hg j hwj hjt hgj
      have hj : j < C.gates.length := by omega
      rcases hgj with rfl | hgj_cone
      · rw [hwj]; exact orReaches_self g hj
      · have hj_not_and : (gateAt C j).op ≠ GateOp.and := by
          intro hj_and
          rcases only_ab_in_t j hjt hj_and with rfl | rfl <;> rcases hg with rfl | rfl
          · exact Nat.lt_irrefl g (inCone_lt g hj g hgj_cone).1
          · exact hNoBA hgj_cone
          · exact hNoAB hgj_cone
          · exact Nat.lt_irrefl g (inCone_lt g hj g hgj_cone).1
        obtain ⟨hin, h0, h1, hj_op⟩ := gate_inputs_pair j hj
        have hj_or : (gateAt C j).op = GateOp.or := hj_op.resolve_left hj_not_and
        have hcone := hgj_cone
        change g ∈ (cones n C).getD j [] at hcone
        rw [cones_getD j hj, List.mem_flatMap] at hcone
        obtain ⟨w', hw'f, hw'm⟩ := hcone
        rw [List.mem_filter] at hw'f
        have hw'_b := of_decide_eq_true hw'f.2
        have hw'lt_w : w' < w := by omega
        have hw'lt : w' < n + C.gates.length := by omega
        have hw'_in_j : InCone n C (w' - n) j := by
          change (w' - n) ∈ (cones n C).getD j []
          rw [cones_getD j hj, List.mem_flatMap]
          refine ⟨w', List.mem_filter.mpr hw'f, List.mem_cons_self⟩
        have hw'_in_t : InCone n C (w' - n) t := inCone_trans t ht_lt j (w' - n) hw'_in_j hjt
        have hgw' : g = w' - n ∨ InCone n C g (w' - n) := List.mem_cons.mp hw'm
        have hrec_w' : OrReaches n C w' g :=
          ih w' hw'lt_w hw'lt g hg (w' - n) (by omega) hw'_in_t hgw'
        rw [hin, List.mem_cons, List.mem_singleton] at hw'f
        rw [hwj]
        rcases hw'f.1 with rfl | rfl
        · exact orReaches_step_or j hj hj_or 0 g hrec_w'
        · exact orReaches_step_or j hj hj_or 1 g hrec_w'
  have inCone_to_orReaches_t : ∀ g : ℕ, (g = a ∨ g = b) → InCone n C g t →
      ∃ s : Fin 2, OrReaches n C (opnd C t s) g := by
    intro g hg hgt
    have hcone := hgt
    change g ∈ (cones n C).getD t [] at hcone
    rw [cones_getD t ht_lt, List.mem_flatMap] at hcone
    obtain ⟨w, hwf, hwm⟩ := hcone
    have hwf' := hwf
    rw [List.mem_filter] at hwf'
    have hwb := of_decide_eq_true hwf'.2
    have hw_in_t : InCone n C (w - n) t := by
      change (w - n) ∈ (cones n C).getD t []
      rw [cones_getD t ht_lt, List.mem_flatMap]
      refine ⟨w, hwf, List.mem_cons_self⟩
    have ht_len : t < C.gates.length := ht_lt
    have hgw : g = w - n ∨ InCone n C g (w - n) := List.mem_cons.mp hwm
    have hw_lt : w < n + C.gates.length :=
      lt_trans hwb.2 (Nat.add_lt_add_left ht_len n)
    have hrec := inCone_to_orReaches_wire w hw_lt g hg (w - n) (by omega) hw_in_t hgw
    obtain ⟨hin, _, _, _⟩ := gate_inputs_pair t ht_lt
    rw [hin, List.mem_cons, List.mem_singleton] at hwf'
    rcases hwf'.1 with rfl | rfl
    · exact ⟨0, hrec⟩
    · exact ⟨1, hrec⟩
  have wireVal_iff_orIn_or_and : ∀ w : ℕ, w < n + C.gates.length → ∀ x : Fin n → Bool,
      wireVal n C w x = true ↔ (∃ v ∈ orIn n C w, x v = true) ∨
        (∃ k < C.gates.length, OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
          gateVal n C k x = true) := by
    intro w hw x
    constructor
    · intro hwx
      by_cases hor : ∃ v ∈ orIn n C w, x v = true
      · exact Or.inl hor
      · right
        refine extract_and_from_wire w hw x hwx (fun v hv => ?_)
        cases hxv : x v
        · rfl
        · exact False.elim (hor ⟨v, hv, hxv⟩)
    · rintro (⟨v, hv, hxv⟩ | ⟨k, _, hrec, _, hkv⟩)
      · exact orIn_val w v x hv hxv
      · exact orReaches_val w k x hrec hkv
  have orIn_nonempty_of_no_and : ∀ w : ℕ, w < n + C.gates.length →
      (∀ k < C.gates.length, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and) →
      (orIn n C w).Nonempty := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hno
      by_cases hwn : w < n
      · let i : Fin n := ⟨w, hwn⟩
        rw [show w = i.val from rfl, orIn_input i]
        exact ⟨i, Finset.mem_singleton_self i⟩
      · let j := w - n
        have hj : j < C.gates.length := by omega
        have hwj : w = n + j := by omega
        have hj_not_and : (gateAt C j).op ≠ GateOp.and :=
          hno j hj (by rw [hwj]; exact orReaches_self j hj)
        obtain ⟨_, h0, _, hj_op⟩ := gate_inputs_pair j hj
        have hj_or : (gateAt C j).op = GateOp.or := hj_op.resolve_left hj_not_and
        have hno0 : ∀ k < C.gates.length, OrReaches n C (opnd C j 0) k →
            (gateAt C k).op ≠ GateOp.and := fun k hk hrec =>
          hno k hk (by rw [hwj]; exact orReaches_step_or j hj hj_or 0 k hrec)
        obtain ⟨v, hv⟩ := ih (opnd C j 0) (by omega) (by omega) hno0
        refine ⟨v, ?_⟩
        rw [hwj, orIn_or_eq j hj hj_or]
        exact Finset.mem_union_left _ hv
  -- Section 4: Pin analysis and split into the 3 structural children
  have ha_dirty : ∃ r ∈ N, gv a r = true := by
    by_contra hnot
    have hcl_a : cl a := fun r hr =>
      Bool.eq_false_of_not_eq_true (fun ht => hnot ⟨r, hr, ht⟩)
    exact ((hJunk a ha_lt ha_and).mp hcl_a).1 rfl
  have hb_dirty : ∃ r ∈ N, gv b r = true := by
    by_contra hnot
    have hcl_b : cl b := fun r hr =>
      Bool.eq_false_of_not_eq_true (fun ht => hnot ⟨r, hr, ht⟩)
    exact ((hJunk b hb_lt' hb_and).mp hcl_b).2 rfl
  have ht_contradict : ∀ s1 s2 : Fin 2, s1 ≠ s2 → ∀ r ∈ N,
      wireVal n C (opnd C t s1) (fun i => r.testBit i.val) = true →
      wireVal n C (opnd C t s2) (fun i => r.testBit i.val) = true → False := by
    intro s1 s2 hne r hr hw1 hw2
    have h01 : wireVal n C (opnd C t 0) (fun i => r.testBit i.val) = true ∧
        wireVal n C (opnd C t 1) (fun i => r.testBit i.val) = true := by
      fin_cases s1 <;> fin_cases s2
      · exact absurd rfl hne
      · exact ⟨hw1, hw2⟩
      · exact ⟨hw2, hw1⟩
      · exact absurd rfl hne
    have ht_true : gateVal 11 C t (fun i => r.testBit i.val) = true := by
      rw [gateVal_and t ht_lt ht_and, Bool.and_eq_true]
      exact h01
    have ht_false := ht_cl r hr
    rw [ht_true] at ht_false
    cases ht_false
  have not_both_pins : ∀ g : ℕ, (g = a ∨ g = b) →
      ¬ (OrReaches n C (opnd C t 0) g ∧ OrReaches n C (opnd C t 1) g) := by
    intro g hg hboth
    have hg_dirty : ∃ r ∈ N, gv g r = true := by
      rcases hg with rfl | rfl
      · exact ha_dirty
      · exact hb_dirty
    obtain ⟨r, hr, hgr⟩ := hg_dirty
    have hw0 := orReaches_val (opnd C t 0) g (fun i => r.testBit i.val) hboth.1 hgr
    have hw1 := orReaches_val (opnd C t 1) g (fun i => r.testBit i.val) hboth.2 hgr
    exact ht_contradict 0 1 Fin.zero_ne_one r hr hw0 hw1
  obtain ⟨sa, hsa⟩ := inCone_to_orReaches_t a (Or.inl rfl) hat
  obtain ⟨sb, hsb⟩ := inCone_to_orReaches_t b (Or.inr rfl) hbt
  obtain ⟨_, ht0, ht1, _⟩ := gate_inputs_pair t ht_lt
  have ht_opnd_lt : ∀ c : Fin 2, opnd C t c < n + C.gates.length := by
    have ht_len : t < C.gates.length := ht_lt
    intro c
    fin_cases c
    · change opnd C t 0 < n + C.gates.length; omega
    · change opnd C t 1 < n + C.gates.length; omega
  by_cases hpin : sa = sb
  · have hss' : sa ≠ 1 - sa := by
      fin_cases sa
      · exact Fin.zero_ne_one
      · exact Fin.zero_ne_one.symm
    have hsb_sa : OrReaches n C (opnd C t sa) b := by rw [← hpin] at hsb; exact hsb
    have hs'_no_and : ∀ k < C.gates.length, OrReaches n C (opnd C t (1 - sa)) k →
        (gateAt C k).op ≠ GateOp.and := by
      intro k hk hrec hk_and
      rcases only_ab_in_t k (orReaches_inCone t ht_lt (1 - sa) k hrec) hk_and with hka | hkb
      · rw [hka] at hrec
        exact not_both_pins a (Or.inl rfl) (by
          fin_cases sa
          · exact ⟨hsa, hrec⟩
          · exact ⟨hrec, hsa⟩)
      · rw [hkb] at hrec
        exact not_both_pins b (Or.inr rfl) (by
          fin_cases sa
          · exact ⟨hsb_sa, hrec⟩
          · exact ⟨hrec, hsb_sa⟩)
    obtain ⟨v, hv⟩ := orIn_nonempty_of_no_and (opnd C t (1 - sa)) (ht_opnd_lt (1 - sa)) hs'_no_and
    refine hSamePin C a b hAO hSize hab hb_lt ha_and hb_and hJunk hTop hNoAB hNoBA ?_ hPos hNeg
    refine ⟨t, ht_lt, ht_and, ht_cl, sa, 1 - sa, hss', hsa, hsb_sa, v, hv, fun r hr hrv => ?_⟩
    have hvs' : wireVal n C (opnd C t (1 - sa)) (fun i => r.testBit i.val) = true :=
      orIn_val (opnd C t (1 - sa)) v (fun i => r.testBit i.val) hv hrv
    constructor
    · cases hga : gateVal 11 C a (fun i => r.testBit i.val)
      · change gateVal 11 C a (fun i => r.testBit i.val) = false; exact hga
      · exfalso
        have hva : wireVal n C (opnd C t sa) (fun i => r.testBit i.val) = true :=
          orReaches_val (opnd C t sa) a (fun i => r.testBit i.val) hsa hga
        exact ht_contradict sa (1 - sa) hss' r hr hva hvs'
    · cases hgb : gateVal 11 C b (fun i => r.testBit i.val)
      · change gateVal 11 C b (fun i => r.testBit i.val) = false; exact hgb
      · exfalso
        have hvb : wireVal n C (opnd C t sa) (fun i => r.testBit i.val) = true :=
          orReaches_val (opnd C t sa) b (fun i => r.testBit i.val) hsb_sa hgb
        exact ht_contradict sa (1 - sa) hss' r hr hvb hvs'
  · have hdisj_neg : ∀ r ∈ N, gv a r = false ∨ gv b r = false := by
      intro r hr
      cases hga : gateVal 11 C a (fun i => r.testBit i.val)
      · left; exact hga
      · right
        cases hgb : gateVal 11 C b (fun i => r.testBit i.val)
        · exact hgb
        · exfalso
          have hva := orReaches_val (opnd C t sa) a (fun i => r.testBit i.val) hsa hga
          have hvb := orReaches_val (opnd C t sb) b (fun i => r.testBit i.val) hsb hgb
          exact ht_contradict sa sb hpin r hr hva hvb
    by_cases hsa_ne : (orIn n C (opnd C t sa)).Nonempty
    · obtain ⟨v, hv⟩ := hsa_ne
      refine hOppMixed C a b hAO hSize (Nat.ne_of_lt hab) ha_lt hb_lt ha_and hb_and hJunk hTop hNoAB hNoBA ?_ hPos hNeg
      refine ⟨t, ht_lt, ht_and, ht_cl, sa, sb, hpin, hsa, hsb, hdisj_neg, v, hv, fun r hr hrv => ?_⟩
      have hva : wireVal n C (opnd C t sa) (fun i => r.testBit i.val) = true :=
        orIn_val (opnd C t sa) v (fun i => r.testBit i.val) hv hrv
      cases hgb : gateVal 11 C b (fun i => r.testBit i.val)
      · change gateVal 11 C b (fun i => r.testBit i.val) = false; exact hgb
      · exfalso
        have hvb := orReaches_val (opnd C t sb) b (fun i => r.testBit i.val) hsb hgb
        exact ht_contradict sa sb hpin r hr hva hvb
    · by_cases hsb_ne : (orIn n C (opnd C t sb)).Nonempty
      · obtain ⟨v, hv⟩ := hsb_ne
        have hJunk' : ∀ j < C.size, (gateAt C j).op = GateOp.and → (cl j ↔ j ≠ b ∧ j ≠ a) := fun j hj hand =>
          (hJunk j hj hand).trans ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
        have hdisj_neg' : ∀ r ∈ N, gv b r = false ∨ gv a r = false := fun r hr =>
          (hdisj_neg r hr).symm
        refine hOppMixed C b a hAO hSize (Nat.ne_of_lt hab).symm hb_lt ha_lt hb_and ha_and hJunk' hTop hNoBA hNoAB ?_ hPos hNeg
        refine ⟨t, ht_lt, ht_and, ht_cl, sb, sa, fun h => hpin h.symm, hsb, hsa, hdisj_neg', v, hv, fun r hr hrv => ?_⟩
        have hvb : wireVal n C (opnd C t sb) (fun i => r.testBit i.val) = true :=
          orIn_val (opnd C t sb) v (fun i => r.testBit i.val) hv hrv
        cases hga : gateVal 11 C a (fun i => r.testBit i.val)
        · change gateVal 11 C a (fun i => r.testBit i.val) = false; exact hga
        · exfalso
          have hva := orReaches_val (opnd C t sa) a (fun i => r.testBit i.val) hsa hga
          exact ht_contradict sa sb hpin r hr hva hvb
      · have hsa_empty : orIn n C (opnd C t sa) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hsa_ne
        have hsb_empty : orIn n C (opnd C t sb) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hsb_ne
        refine hOppPure C a b hAO hSize hab hb_lt ha_and hb_and hJunk hTop hNoAB hNoBA ?_ hPos hNeg
        refine ⟨t, ht_lt, ht_and, ht_cl, sa, sb, hpin, hsa, hsb, hsa_empty, hsb_empty, fun r => ?_⟩
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro htr
          have htr' := htr
          change gateVal n C t (fun i => r.testBit i.val) = true at htr'
          rw [gateVal_and t ht_lt ht_and, Bool.and_eq_true] at htr'
          have hw_a : wireVal n C (opnd C t sa) (fun i => r.testBit i.val) = true := by
            fin_cases sa
            · exact htr'.1
            · exact htr'.2
          have hw_b : wireVal n C (opnd C t sb) (fun i => r.testBit i.val) = true := by
            fin_cases sb
            · exact htr'.1
            · exact htr'.2
          have hka := (wireVal_iff_orIn_or_and (opnd C t sa) (ht_opnd_lt sa) (fun i => r.testBit i.val)).mp hw_a
          have hkb := (wireVal_iff_orIn_or_and (opnd C t sb) (ht_opnd_lt sb) (fun i => r.testBit i.val)).mp hw_b
          have hga_t : gv a r = true := by
            rcases hka with ⟨v, hv, _⟩ | ⟨k, _, hrec, hk_and, hkv⟩
            · rw [hsa_empty] at hv; cases hv
            · rcases only_ab_in_t k (orReaches_inCone t ht_lt sa k hrec) hk_and with hka' | hkb'
              · rw [hka'] at hkv; exact hkv
              · exfalso
                rw [hkb'] at hrec
                exact not_both_pins b (Or.inr rfl) (by
                  fin_cases sa <;> fin_cases sb
                  · exact absurd rfl hpin
                  · exact ⟨hrec, hsb⟩
                  · exact ⟨hsb, hrec⟩
                  · exact absurd rfl hpin)
          have hgb_t : gv b r = true := by
            rcases hkb with ⟨v, hv, _⟩ | ⟨k, _, hrec, hk_and, hkv⟩
            · rw [hsb_empty] at hv; cases hv
            · rcases only_ab_in_t k (orReaches_inCone t ht_lt sb k hrec) hk_and with hka' | hkb'
              · exfalso
                rw [hka'] at hrec
                exact not_both_pins a (Or.inl rfl) (by
                  fin_cases sa <;> fin_cases sb
                  · exact absurd rfl hpin
                  · exact ⟨hsa, hrec⟩
                  · exact ⟨hrec, hsa⟩
                  · exact absurd rfl hpin)
              · rw [hkb'] at hkv; exact hkv
          rw [Bool.and_eq_true]; exact ⟨hga_t, hgb_t⟩
        · intro hab_t
          rw [Bool.and_eq_true] at hab_t
          have hva := orReaches_val (opnd C t sa) a (fun i => r.testBit i.val) hsa hab_t.1
          have hvb := orReaches_val (opnd C t sb) b (fun i => r.testBit i.val) hsb hab_t.2
          change gateVal n C t (fun i => r.testBit i.val) = true
          rw [gateVal_and t ht_lt ht_and, Bool.and_eq_true]
          fin_cases sa <;> fin_cases sb
          · exact absurd rfl hpin
          · exact ⟨hva, hvb⟩
          · exact ⟨hvb, hva⟩
          · exact absurd rfl hpin
