import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_5206_506
    (hFormula66 :
      have D : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}
      ∀ (f : DMFormula (26 : ℕ)),
        (DMFormula.rec (motive := fun _ : DMFormula (26 : ℕ) => Prop)
          (fun _ s => s = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b)) f →
        (∀ x : Fin (26 : ℕ) → Bool, f.eval x = true ↔
          ∃ u t : Fin (13 : ℕ), u - t ∈ D ∧
            x (Fin.castAdd (13 : ℕ) u) = true ∧ x (Fin.natAdd (13 : ℕ) t) = true) →
        have reads : Fin (26 : ℕ) → DMFormula (26 : ℕ) → ℕ := fun v ψ =>
          DMFormula.rec (motive := fun _ : DMFormula (26 : ℕ) => ℕ)
            (fun w _ => if w = v then 1 else 0) (fun _ _ a b => a + b) (fun _ _ a b => a + b) ψ
        2 ≤ reads (0 : Fin (26 : ℕ)) f → 2 ≤ reads (13 : Fin (26 : ℕ)) f → 66 ≤ f.leaves)
    (hSharedDiamond :
      ¬∃ (C : Circuit),
        have D : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}
        have isA : ℕ → Prop := fun k => (gateAt C k).op = GateOp.and
        have wv : ℕ → (Fin (26 : ℕ) → Bool) → Bool := wireVal (26 : ℕ) C
        have reach : ℕ → ℕ → Prop := fun m w => (26 : ℕ) ≤ w ∧ ((26 : ℕ) + m = w ∨ InCone (26 : ℕ) C m (w - (26 : ℕ)))
        C.size ≤ (64 : ℕ) ∧
        (66 : ℕ) ≤ (C.gates.foldl (fun (ws : List ℕ) (g : Gate) => ws ++ [(g.inputs.map fun i => ws.getD i (0 : ℕ)).sum]) (List.replicate (26 : ℕ) (1 : ℕ))).getD C.output (0 : ℕ) ∧
        IsAO2 (26 : ℕ) C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        (∀ x : Fin (26 : ℕ) → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u t : Fin (13 : ℕ), u - t ∈ D ∧
            x (Fin.castAdd (13 : ℕ) u) = true ∧ x (Fin.natAdd (13 : ℕ) t) = true) ∧
        (∃ d < C.gates.length, isA d ∧ ∃ x : Fin (26 : ℕ) → Bool, gateVal (26 : ℕ) C d x = true ∧ C.eval (List.ofFn x) = false) ∧
        ∃ k < C.gates.length, isA k ∧ reach k C.output ∧
          gateVal (26 : ℕ) C k (pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = true ∧
          (∀ b : Fin (2 : ℕ), wv (opnd C k b) (pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = false ∧
            wv (opnd C k b) (pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = false) ∧
          ∃ m < C.gates.length, ∀ b : Fin (2 : ℕ), reach m (opnd C k b))
    (hSharedDisjoint :
      ¬∃ (C : Circuit),
        have D : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}
        have isA : ℕ → Prop := fun k => (gateAt C k).op = GateOp.and
        have wv : ℕ → (Fin (26 : ℕ) → Bool) → Bool := wireVal (26 : ℕ) C
        have reach : ℕ → ℕ → Prop := fun m w => (26 : ℕ) ≤ w ∧ ((26 : ℕ) + m = w ∨ InCone (26 : ℕ) C m (w - (26 : ℕ)))
        C.size ≤ (64 : ℕ) ∧
        (66 : ℕ) ≤ (C.gates.foldl (fun (ws : List ℕ) (g : Gate) => ws ++ [(g.inputs.map fun i => ws.getD i (0 : ℕ)).sum]) (List.replicate (26 : ℕ) (1 : ℕ))).getD C.output (0 : ℕ) ∧
        IsAO2 (26 : ℕ) C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        (∀ x : Fin (26 : ℕ) → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u t : Fin (13 : ℕ), u - t ∈ D ∧
            x (Fin.castAdd (13 : ℕ) u) = true ∧ x (Fin.natAdd (13 : ℕ) t) = true) ∧
        (∃ d < C.gates.length, isA d ∧ ∃ x : Fin (26 : ℕ) → Bool, gateVal (26 : ℕ) C d x = true ∧ C.eval (List.ofFn x) = false) ∧
        ∃ k < C.gates.length, isA k ∧ reach k C.output ∧
          gateVal (26 : ℕ) C k (pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = true ∧
          (∀ b : Fin (2 : ℕ), wv (opnd C k b) (pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = false ∧
            wv (opnd C k b) (pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = false) ∧
          ∀ m < C.gates.length, ¬ (reach m (opnd C k (0 : Fin (2 : ℕ))) ∧ reach m (opnd C k (1 : Fin (2 : ℕ))))) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = x3;     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     x1.size ≤ (64 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, x6 x10 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x4 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ), x6 x10 ∧ ((26 : ℕ) + x10 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 x10 (x1.output - (26 : ℕ))) ∧ x4 x10 x9 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), x5 (PEqualNP.TopForm.opnd x1 x10 x11) x7 = Bool.false ∧ x5 (PEqualNP.TopForm.opnd x1 x10 x11) x8 = Bool.false := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro hEx
  obtain ⟨C, hC⟩ := hEx
  dsimp only at hC
  obtain ⟨hSize, hGates, hEval, hDirty, k, hkA, hkLive, hkT, hkF⟩ := hC
  let n : ℕ := 26
  have hAO : IsAO2 26 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
      exact (hGates i C.gates[i] (List.getElem?_eq_getElem hi)).1
    · intro j hj
      obtain ⟨_, a, b, hin, _, ha, hb⟩ := hGates j C.gates[j] (List.getElem?_eq_getElem hj)
      change ∀ w ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, w < 26 + j
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hin,
        List.mem_cons]
      intro w hw
      rcases hw with rfl | rfl | hmem
      · exact ha
      · exact hb
      · exact False.elim (List.not_mem_nil hmem)
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨_, a, b, hin, _⟩ := hGates i C.gates[i] (List.getElem?_eq_getElem hi)
      rw [hin]; rfl
  have hNodup : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨_, a, b, hin, hne, _⟩ := hGates i C.gates[i] (List.getElem?_eq_getElem hi)
    rw [hin]
    simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    exact hne
  -- Section 1: Circuit evaluation and cone helpers
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
  have inCone_lt : ∀ j : ℕ, j < C.gates.length → ∀ m : ℕ, InCone n C m j →
      m < j ∧ m < C.gates.length := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj m hmj
      change m ∈ (cones n C).getD j [] at hmj
      rw [cones_getD j hj, List.mem_flatMap] at hmj
      obtain ⟨w, hwf, hwm⟩ := hmj
      rw [List.mem_filter] at hwf
      have hwb := of_decide_eq_true hwf.2
      rw [List.mem_cons] at hwm
      rcases hwm with rfl | hrec
      · exact ⟨by omega, by omega⟩
      · have hsub := ih (w - n) (by omega) (by omega) m hrec
        exact ⟨by omega, hsub.2⟩
  -- Section 2: Output wire bounds and gate index bound
  have hOut_lt : C.output < n + C.gates.length := by
    by_contra hnot
    let x0 := pairInput (0 : Fin 26) (13 : Fin 26)
    have hfalse : C.eval (List.ofFn x0) = false := by
      change wireVal n C C.output x0 = false
      exact wire_beyond x0 C.output (by omega)
    have htrue : C.eval (List.ofFn x0) = true := (hEval x0).mpr ⟨0, 0, by decide, by decide, by decide⟩
    rw [htrue] at hfalse
    cases hfalse
  have hOut_ge : n ≤ C.output := by
    by_contra hnot
    let i : Fin 26 := ⟨C.output, by omega⟩
    let x1 := pairInput i i
    have hx1 : C.eval (List.ofFn x1) = true := by
      change wireVal n C i.val x1 = true
      rw [wire_input x1 i]
      change decide (i = i ∨ i = i) = true
      exact decide_eq_true (Or.inl rfl)
    obtain ⟨u, t, _, hu, ht⟩ := (hEval x1).mp hx1
    have hu' : Fin.castAdd 13 u = i := (of_decide_eq_true hu).elim id id
    have ht' : Fin.natAdd 13 t = i := (of_decide_eq_true ht).elim id id
    have hv : (Fin.castAdd 13 u).val = (Fin.natAdd 13 t).val := congrArg Fin.val (hu'.trans ht'.symm)
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hv
    omega
  have hk_lt : k < C.gates.length := by
    rcases hkLive with heq | hcone
    · omega
    · exact (inCone_lt (C.output - 26) (by omega) k hcone).2
  -- Section 3: Formula unfolding and wire weights
  let d0 : DMFormula 26 := DMFormula.lit 0 true
  let isPos : DMFormula 26 → Prop :=
    DMFormula.rec (motive := fun _ : DMFormula 26 => Prop)
      (fun _ s => s = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b)
  let reads : Fin 26 → DMFormula 26 → ℕ := fun v =>
    DMFormula.rec (motive := fun _ : DMFormula 26 => ℕ)
      (fun w _ => if w = v then 1 else 0) (fun _ _ a b => a + b) (fun _ _ a b => a + b)
  let fstep : List (DMFormula 26) → Gate → List (DMFormula 26) := fun fs g =>
    let a := fs.getD (g.inputs.getD 0 0) d0
    let b := fs.getD (g.inputs.getD 1 0) d0
    fs ++ [if g.op = GateOp.and then DMFormula.and a b else DMFormula.or a b]
  let wtstep : List ℕ → Gate → List ℕ := fun ws g =>
    ws ++ [(g.inputs.map fun i => ws.getD i 0).sum]
  let fseed : List (DMFormula 26) := List.ofFn (fun i : Fin 26 => DMFormula.lit i true)
  let wtseed : List ℕ := List.replicate 26 1
  let unfold := C.gates.foldl fstep fseed
  let weights := C.gates.foldl wtstep wtseed
  have fstep_len : ∀ (gs : List Gate) (fs : List (DMFormula 26)),
      (gs.foldl fstep fs).length = fs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro fs; rfl
    | cons g gs ih =>
      intro fs
      rw [List.foldl_cons, ih]
      have hl : (fstep fs g).length = fs.length + 1 := by
        simp only [fstep, List.length_append, List.length_singleton]
      rw [hl, List.length_cons]; omega
  have fstep_lt : ∀ (gs : List Gate) (fs : List (DMFormula 26)) (i : ℕ), i < fs.length →
      (gs.foldl fstep fs).getD i d0 = fs.getD i d0 := by
    intro gs
    induction gs with
    | nil => intro fs i _; rfl
    | cons g gs ih =>
      intro fs i hi
      have hi' : i < (fstep fs g).length := by
        simp only [fstep, List.length_append, List.length_singleton]; omega
      rw [List.foldl_cons, ih (fstep fs g) i hi']
      simp only [fstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have unfold_raw : ∀ (gs : List Gate) (fs : List (DMFormula 26)) (j : ℕ) (hj : j < gs.length),
      (gs.foldl fstep fs).getD (fs.length + j) d0 =
        let a := if gs[j].inputs.getD 0 0 < fs.length + j then (gs.foldl fstep fs).getD (gs[j].inputs.getD 0 0) d0 else d0
        let b := if gs[j].inputs.getD 1 0 < fs.length + j then (gs.foldl fstep fs).getD (gs[j].inputs.getD 1 0) d0 else d0
        if gs[j].op = GateOp.and then DMFormula.and a b else DMFormula.or a b := by
    intro gs
    induction gs with
    | nil => intro fs j hj; simp at hj
    | cons g gs ih =>
      intro fs j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have hlt : fs.length < (fstep fs g).length := by
          simp only [fstep, List.length_append, List.length_singleton]; omega
        rw [Nat.add_zero, fstep_lt gs (fstep fs g) fs.length hlt]
        have hlast : (fstep fs g).getD fs.length d0 =
            if g.op = GateOp.and then
              DMFormula.and (fs.getD (g.inputs.getD 0 0) d0) (fs.getD (g.inputs.getD 1 0) d0)
            else
              DMFormula.or (fs.getD (g.inputs.getD 0 0) d0) (fs.getD (g.inputs.getD 1 0) d0) := by
          simp only [fstep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [List.getElem_cons_zero, hlast]
        have heq_idx : ∀ k : ℕ, k < fs.length →
            (gs.foldl fstep (fstep fs g)).getD k d0 = fs.getD k d0 := fun k hk => by
          have hk' : k < (fstep fs g).length := by
            simp only [fstep, List.length_append, List.length_singleton]; omega
          rw [fstep_lt gs (fstep fs g) k hk']
          simp only [fstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
        have heq_dflt : ∀ k : ℕ, fs.length ≤ k → fs.getD k d0 = d0 := fun k hk => by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk, Option.getD_none]
        by_cases h0 : g.inputs.getD 0 0 < fs.length <;> by_cases h1 : g.inputs.getD 1 0 < fs.length
        · rw [if_pos h0, if_pos h1, heq_idx (g.inputs.getD 0 0) h0, heq_idx (g.inputs.getD 1 0) h1]
        · rw [if_pos h0, if_neg h1, heq_idx (g.inputs.getD 0 0) h0, heq_dflt (g.inputs.getD 1 0) (by omega)]
        · rw [if_neg h0, if_pos h1, heq_dflt (g.inputs.getD 0 0) (by omega), heq_idx (g.inputs.getD 1 0) h1]
        · rw [if_neg h0, if_neg h1, heq_dflt (g.inputs.getD 0 0) (by omega), heq_dflt (g.inputs.getD 1 0) (by omega)]
      | succ j =>
        have hj' : j < gs.length := by simp only [List.length_cons] at hj; omega
        have key := ih (fstep fs g) j hj'
        have hl : (fstep fs g).length = fs.length + 1 := by
          simp only [fstep, List.length_append, List.length_singleton]
        rw [hl, show fs.length + 1 + j = fs.length + (j + 1) by omega] at key
        rw [List.getElem_cons_succ]
        exact key
  have unfold_gate : ∀ j : ℕ, j < C.gates.length →
      unfold.getD (n + j) d0 =
        if (gateAt C j).op = GateOp.and then
          DMFormula.and (unfold.getD (opnd C j 0) d0) (unfold.getD (opnd C j 1) d0)
        else
          DMFormula.or (unfold.getD (opnd C j 0) d0) (unfold.getD (opnd C j 1) d0) := by
    intro j hj
    change (C.gates.foldl fstep fseed).getD (n + j) d0 = _
    have hlen : fseed.length = n := List.length_ofFn
    have hraw := unfold_raw C.gates fseed j hj
    rw [hlen] at hraw
    obtain ⟨hin, h0, h1, _⟩ := gate_inputs_pair j hj
    have hg0 : C.gates[j].inputs.getD 0 0 = opnd C j 0 := by
      rw [← hgate j hj, hin]; rfl
    have hg1 : C.gates[j].inputs.getD 1 0 = opnd C j 1 := by
      rw [← hgate j hj, hin]; rfl
    rw [hg0, hg1, ← hgate j hj] at hraw
    dsimp only at hraw
    rw [if_pos h0, if_pos h1] at hraw
    exact hraw
  have unfold_input : ∀ i : Fin n, unfold.getD i.val d0 = DMFormula.lit i true := by
    intro i
    change (C.gates.foldl fstep fseed).getD i.val d0 = DMFormula.lit i true
    rw [fstep_lt C.gates fseed i.val (by rw [List.length_ofFn]; exact i.isLt)]
    simp only [fseed, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    rw [dif_pos (show i.val < 26 from i.isLt)]
    rfl
  have wtstep_len : ∀ (gs : List Gate) (ws : List ℕ),
      (gs.foldl wtstep ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; rfl
    | cons g gs ih =>
      intro ws
      rw [List.foldl_cons, ih]
      have hl : (wtstep ws g).length = ws.length + 1 := by
        simp only [wtstep, List.length_append, List.length_singleton]
      rw [hl, List.length_cons]; omega
  have wtstep_lt : ∀ (gs : List Gate) (ws : List ℕ) (i : ℕ), i < ws.length →
      (gs.foldl wtstep ws).getD i 0 = ws.getD i 0 := by
    intro gs
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      have hi' : i < (wtstep ws g).length := by
        simp only [wtstep, List.length_append, List.length_singleton]; omega
      rw [List.foldl_cons, ih (wtstep ws g) i hi']
      simp only [wtstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have weights_raw : ∀ (gs : List Gate) (ws : List ℕ) (j : ℕ) (hj : j < gs.length),
      (gs.foldl wtstep ws).getD (ws.length + j) 0 =
        (gs[j].inputs.map fun i => if i < ws.length + j then (gs.foldl wtstep ws).getD i 0 else 0).sum := by
    intro gs
    induction gs with
    | nil => intro ws j hj; simp at hj
    | cons g gs ih =>
      intro ws j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have hlt : ws.length < (wtstep ws g).length := by
          simp only [wtstep, List.length_append, List.length_singleton]; omega
        rw [Nat.add_zero, wtstep_lt gs (wtstep ws g) ws.length hlt]
        have hlast : (wtstep ws g).getD ws.length 0 =
            (g.inputs.map fun i => ws.getD i 0).sum := by
          simp only [wtstep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [List.getElem_cons_zero, hlast]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        by_cases hi : i < ws.length
        · rw [if_pos hi, wtstep_lt gs (wtstep ws g) i (by
            simp only [wtstep, List.length_append, List.length_singleton]; omega)]
          simp only [wtstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ws.length ≤ i),
            Option.getD_none]
      | succ j =>
        have hj' : j < gs.length := by simp only [List.length_cons] at hj; omega
        have key := ih (wtstep ws g) j hj'
        have hl : (wtstep ws g).length = ws.length + 1 := by
          simp only [wtstep, List.length_append, List.length_singleton]
        rw [hl, show ws.length + 1 + j = ws.length + (j + 1) by omega] at key
        rw [List.getElem_cons_succ]
        exact key
  have weights_gate : ∀ j : ℕ, j < C.gates.length →
      weights.getD (n + j) 0 = weights.getD (opnd C j 0) 0 + weights.getD (opnd C j 1) 0 := by
    intro j hj
    change (C.gates.foldl wtstep wtseed).getD (n + j) 0 = _
    have hlen : wtseed.length = n := List.length_replicate
    have hraw := weights_raw C.gates wtseed j hj
    rw [hlen] at hraw
    obtain ⟨hin, h0, h1, _⟩ := gate_inputs_pair j hj
    rw [← hgate j hj, hin] at hraw
    simp only [List.map_cons, List.map_nil, if_pos h0, if_pos h1, List.sum_cons, List.sum_nil,
      Nat.add_zero] at hraw
    exact hraw
  have weights_input : ∀ i : Fin n, weights.getD i.val 0 = 1 := by
    intro i
    change (C.gates.foldl wtstep wtseed).getD i.val 0 = 1
    rw [wtstep_lt C.gates wtseed i.val (by rw [List.length_replicate]; exact i.isLt)]
    simp only [wtseed, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    rw [if_pos (show i.val < 26 from i.isLt)]
    rfl
  have unfold_props : ∀ w : ℕ, w < n + C.gates.length →
      isPos (unfold.getD w d0) ∧
      (∀ x : Fin n → Bool, (unfold.getD w d0).eval x = wireVal n C w x) ∧
      (unfold.getD w d0).leaves = weights.getD w 0 := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hwn : w < n
      · let i : Fin n := ⟨w, hwn⟩
        rw [show w = i.val from rfl, unfold_input i, weights_input i]
        refine ⟨rfl, fun x => ?_, rfl⟩
        rw [wire_input x i]
        dsimp only [DMFormula.eval]
        rfl
      · let j := w - n
        have hj : j < C.gates.length := by omega
        have hwj : w = n + j := by omega
        obtain ⟨_, h0, h1, hop⟩ := gate_inputs_pair j hj
        have ih0 := ih (opnd C j 0) (by omega) (by omega)
        have ih1 := ih (opnd C j 1) (by omega) (by omega)
        rw [hwj, unfold_gate j hj, weights_gate j hj]
        rcases hop with hand | hor
        · rw [if_pos hand]
          refine ⟨⟨ih0.1, ih1.1⟩, fun x => ?_, ?_⟩
          · dsimp only [DMFormula.eval]
            rw [ih0.2.1 x, ih1.2.1 x]
            change _ = gateVal n C j x
            rw [gateVal_and j hj hand x]
          · dsimp only [DMFormula.leaves]
            rw [ih0.2.2, ih1.2.2]
        · have hne : (gateAt C j).op ≠ GateOp.and := by rw [hor]; intro h; cases h
          rw [if_neg hne]
          refine ⟨⟨ih0.1, ih1.1⟩, fun x => ?_, ?_⟩
          · dsimp only [DMFormula.eval]
            rw [ih0.2.1 x, ih1.2.1 x]
            change _ = gateVal n C j x
            rw [gateVal_or j hj hor x]
          · dsimp only [DMFormula.leaves]
            rw [ih0.2.2, ih1.2.2]
  have reads_gate_le : ∀ j : ℕ, j < C.gates.length → ∀ b : Fin 2, ∀ v : Fin 26,
      reads v (unfold.getD (opnd C j b) d0) ≤ reads v (unfold.getD (n + j) d0) := by
    intro j hj b v
    rw [unfold_gate j hj]
    by_cases hand : (gateAt C j).op = GateOp.and
    · rw [if_pos hand]
      fin_cases b
      · change reads v (unfold.getD (opnd C j 0) d0) ≤
          reads v (unfold.getD (opnd C j 0) d0) + reads v (unfold.getD (opnd C j 1) d0)
        omega
      · change reads v (unfold.getD (opnd C j 1) d0) ≤
          reads v (unfold.getD (opnd C j 0) d0) + reads v (unfold.getD (opnd C j 1) d0)
        omega
    · rw [if_neg hand]
      fin_cases b
      · change reads v (unfold.getD (opnd C j 0) d0) ≤
          reads v (unfold.getD (opnd C j 0) d0) + reads v (unfold.getD (opnd C j 1) d0)
        omega
      · change reads v (unfold.getD (opnd C j 1) d0) ≤
          reads v (unfold.getD (opnd C j 0) d0) + reads v (unfold.getD (opnd C j 1) d0)
        omega
  have reads_mono_inCone : ∀ j : ℕ, j < C.gates.length → ∀ m : ℕ, InCone n C m j →
      ∀ v : Fin 26, reads v (unfold.getD (n + m) d0) ≤ reads v (unfold.getD (n + j) d0) := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj m hmj v
      change m ∈ (cones n C).getD j [] at hmj
      rw [cones_getD j hj, List.mem_flatMap] at hmj
      obtain ⟨w, hwf, hwm⟩ := hmj
      rw [List.mem_filter] at hwf
      have hwb := of_decide_eq_true hwf.2
      obtain ⟨hin, _, _, _⟩ := gate_inputs_pair j hj
      rw [hin, List.mem_cons, List.mem_singleton] at hwf
      have hw_le : reads v (unfold.getD w d0) ≤ reads v (unfold.getD (n + j) d0) := by
        rcases hwf.1 with rfl | rfl
        · exact reads_gate_le j hj 0 v
        · exact reads_gate_le j hj 1 v
      rw [List.mem_cons] at hwm
      rcases hwm with rfl | hrec
      · rw [show n + (w - n) = w by omega]; exact hw_le
      · have hsub := ih (w - n) (by omega) (by omega) m hrec v
        rw [show n + (w - n) = w by omega] at hsub
        exact le_trans hsub hw_le
  have eval_eq_of_reads_zero : ∀ (φ : DMFormula 26) (v : Fin 26) (x y : Fin 26 → Bool),
      (∀ i : Fin 26, i ≠ v → x i = y i) → reads v φ = 0 → φ.eval x = φ.eval y := by
    intro φ
    induction φ with
    | lit w s =>
      intro v x y hxy hzr
      dsimp only [reads] at hzr
      dsimp only [DMFormula.eval]
      have hne : w ≠ v := by
        intro heq
        rw [if_pos heq] at hzr
        omega
      rw [hxy w hne]
    | and a b iha ihb =>
      intro v x y hxy hzr
      change reads v a + reads v b = 0 at hzr
      dsimp only [DMFormula.eval]
      rw [iha v x y hxy (by omega), ihb v x y hxy (by omega)]
    | or a b iha ihb =>
      intro v x y hxy hzr
      change reads v a + reads v b = 0 at hzr
      dsimp only [DMFormula.eval]
      rw [iha v x y hxy (by omega), ihb v x y hxy (by omega)]
  -- Section 4: Double re-read lower bound and diamond vs disjoint split
  have hk_reads : ∀ b : Fin 2,
      1 ≤ reads (0 : Fin 26) (unfold.getD (opnd C k b) d0) ∧
      1 ≤ reads (13 : Fin 26) (unfold.getD (opnd C k b) d0) := by
    intro b
    obtain ⟨_, hk0, hk1, _⟩ := gate_inputs_pair k hk_lt
    have hkb_lt : opnd C k b < n + C.gates.length := by
      fin_cases b
      · change opnd C k 0 < n + C.gates.length; omega
      · change opnd C k 1 < n + C.gates.length; omega
    have hkt' : gateVal 26 C k (pairInput (0 : Fin 26) 13) = true := hkT
    rw [gateVal_and k hk_lt hkA] at hkt'
    rw [Bool.and_eq_true] at hkt'
    have hkb_true : wireVal 26 C (opnd C k b) (pairInput (0 : Fin 26) 13) = true := by
      fin_cases b
      · exact hkt'.1
      · exact hkt'.2
    have heval := (unfold_props (opnd C k b) hkb_lt).2.1
    constructor
    · by_contra hzero
      have hz : reads (0 : Fin 26) (unfold.getD (opnd C k b) d0) = 0 := by omega
      have hxy : ∀ i : Fin 26, i ≠ 0 →
          pairInput (0 : Fin 26) 13 i = pairInput (13 : Fin 26) 13 i := by
        intro i hi0
        change decide (i = 0 ∨ i = 13) = decide (i = 13 ∨ i = 13)
        by_cases hi13 : i = 13
        · rw [hi13]; rfl
        · rw [decide_eq_false (fun h => h.elim hi0 hi13),
              decide_eq_false (fun h => h.elim hi13 hi13)]
      have heq := eval_eq_of_reads_zero _ 0 _ _ hxy hz
      rw [heval _, heval _] at heq
      rw [hkb_true, (hkF b).2] at heq
      cases heq
    · by_contra hzero
      have hz : reads (13 : Fin 26) (unfold.getD (opnd C k b) d0) = 0 := by omega
      have hxy : ∀ i : Fin 26, i ≠ 13 →
          pairInput (0 : Fin 26) 13 i = pairInput (0 : Fin 26) 0 i := by
        intro i hi13
        change decide (i = 0 ∨ i = 13) = decide (i = 0 ∨ i = 0)
        by_cases hi0 : i = 0
        · rw [hi0]; rfl
        · rw [decide_eq_false (fun h => h.elim hi0 hi13),
              decide_eq_false (fun h => h.elim hi0 hi0)]
      have heq := eval_eq_of_reads_zero _ 13 _ _ hxy hz
      rw [heval _, heval _] at heq
      rw [hkb_true, (hkF b).1] at heq
      cases heq
  have hk_reads2 : 2 ≤ reads (0 : Fin 26) (unfold.getD (n + k) d0) ∧
      2 ≤ reads (13 : Fin 26) (unfold.getD (n + k) d0) := by
    rw [unfold_gate k hk_lt, if_pos hkA]
    have r0 := hk_reads 0
    have r1 := hk_reads 1
    constructor
    · change 2 ≤ reads 0 (unfold.getD (opnd C k 0) d0) + reads 0 (unfold.getD (opnd C k 1) d0)
      omega
    · change 2 ≤ reads 13 (unfold.getD (opnd C k 0) d0) + reads 13 (unfold.getD (opnd C k 1) d0)
      omega
  have hout_reads2 : 2 ≤ reads (0 : Fin 26) (unfold.getD C.output d0) ∧
      2 ≤ reads (13 : Fin 26) (unfold.getD C.output d0) := by
    rcases hkLive with heq | hcone
    · rw [← heq]; exact hk_reads2
    · have m0 := reads_mono_inCone (C.output - 26) (by omega) k hcone 0
      have m13 := reads_mono_inCone (C.output - 26) (by omega) k hcone 13
      rw [show n + (C.output - 26) = C.output by omega] at m0 m13
      exact ⟨le_trans hk_reads2.1 m0, le_trans hk_reads2.2 m13⟩
  have hOutProps := unfold_props C.output hOut_lt
  have hWt66 : 66 ≤ weights.getD C.output 0 := by
    rw [← hOutProps.2.2]
    refine hFormula66 (unfold.getD C.output d0) hOutProps.1 (fun x => ?_) hout_reads2.1 hout_reads2.2
    rw [hOutProps.2.1 x]
    exact hEval x
  have hReachK : (26 : ℕ) ≤ C.output ∧ ((26 : ℕ) + k = C.output ∨ InCone (26 : ℕ) C k (C.output - (26 : ℕ))) :=
    ⟨hOut_ge, hkLive⟩
  by_cases hdiam : ∃ m < C.gates.length, ∀ b : Fin 2,
      (26 : ℕ) ≤ opnd C k b ∧ ((26 : ℕ) + m = opnd C k b ∨ InCone (26 : ℕ) C m (opnd C k b - (26 : ℕ)))
  · exact hSharedDiamond ⟨C, hSize, hWt66, hAO, hNodup, hEval, hDirty, k, hk_lt, hkA, hReachK, hkT, hkF, hdiam⟩
  · refine hSharedDisjoint ⟨C, hSize, hWt66, hAO, hNodup, hEval, hDirty, k, hk_lt, hkA, hReachK, hkT, hkF, ?_⟩
    intro m hm hboth
    apply hdiam
    refine ⟨m, hm, fun b => ?_⟩
    fin_cases b
    · exact hboth.1
    · exact hboth.2
