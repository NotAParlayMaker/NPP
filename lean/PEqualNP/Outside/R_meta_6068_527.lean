import PEqualNP.Defs

-- Reduces the two remaining premises of the reduction proposed in PR 22517.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.ReadK PEqualNP.HeptadCover

-- Trace the singleton-true collision to a later AND where that singleton stops.
-- The singleton-dead collision has an earlier AND combining opposite singleton
-- types. Both additional witnesses are on the same selected proof.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.R_meta_6068_527
    (polarity : let ok := (fun C : Circuit => 63 ≤ C.size ∧ C.size ≤ 64 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
    circuitFun 26 C = fpl 13 (fun p l => p ∈ singerLines3 l) ∧
    ∀ a ∈ ([0,13] : List ℕ), lineSingle C 26 (fun i => decide (i=a)) (13-a) a = false)
    let Q := (fun (C : Circuit) (a b : ℕ) => let V := fun (S : Finset ℕ) => wval C (indW 26 S); let P := Relation.ReflTransGen (fun u w : ℕ => ∃ j < C.size, w = 26+j ∧ (if (gateAt C j).op.eval [] then u ∈ (gateAt C j).inputs else u = if V {0,13} (in0 C j) then in0 C j else in1 C j)); let K := fun (z j : ℕ) => P (26+j) C.output ∧ isAnd C j ∧ ∀ t ∈ (gateAt C j).inputs, V {z} t = false; ∃ i j, K a i ∧ K b j ∧ V {b} (26+i)=true ∧ V {a} (26+j)=false)
    ∀ C, ok C → Q C 13 0 → ∃ D, ok D ∧ Q D 0 13)
    (bound : ∀ (C : Circuit), 63 ≤ C.size → C.size ≤ 64 → IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
    circuitFun 26 C = fpl 13 (fun p l => p ∈ singerLines3 l) →
    (∀ a ∈ ([0,13] : List ℕ), lineSingle C 26 (fun i => decide (i=a)) (13-a) a = false) →
    let V := fun (S : Finset ℕ) => wval C (indW 26 S)
    let P := Relation.ReflTransGen (fun u w : ℕ => ∃ j < C.size, w = 26+j ∧
     (if (gateAt C j).op.eval [] then u ∈ (gateAt C j).inputs
      else u = if V {0,13} (in0 C j) then in0 C j else in1 C j))
    let K := fun (z j : ℕ) => P (26+j) C.output ∧ isAnd C j ∧
       ∀ t ∈ (gateAt C j).inputs, V {z} t = false
    let pinL := in0 C
    let pinR := in1 C
    let pointVal := V {0}
    let lineVal := V {13}
    ∀ j k, K 0 j → K 13 k → lineVal (26+j) = true → pointVal (26+k) = false → (∃ s d : ℕ, s < k ∧ j < d ∧ isAnd C s ∧ isAnd C d ∧
      P (26+s) (26+k) ∧ P (26+j) (26+d) ∧ P (26+d) C.output ∧
      lineVal (pinL d) ≠ lineVal (pinR d) ∧
      pointVal (pinL s) ≠ pointVal (pinR s) ∧ lineVal (pinL s) ≠ lineVal (pinR s) ∧
      pointVal (pinL s) ≠ lineVal (pinL s)) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →               PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →                 have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);                 have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ) (x15 : ℕ), x1.gates[x12]? = Option.some x13 ∧ x11 = (26 : ℕ) + x12 ∧ x13.inputs = [x14, x15] ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x10 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x15) ∧ x9 {(0 : ℕ), (13 : ℕ)} x10 = Bool.true ∧ x9 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true;                 have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => Relation.ReflTransGen x10 ((26 : ℕ) + x12) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x12 ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs, x9 {(0 : ℕ), (13 : ℕ)} x13 = Bool.true ∧ x9 {x11} x13 = Bool.false;                 (∃ (x12 : ℕ) (x13 : ℕ), x12 ≠ x13 ∧ x11 (0 : ℕ) x12 ∧ x11 (13 : ℕ) x13 ∧ x9 {(13 : ℕ)} ((26 : ℕ) + x12) ≠ x9 {(0 : ℕ)} ((26 : ℕ) + x13)) → False := by
  have trace : ∀ (C : Circuit), IsAO2 26 C →
    let V := fun (S : Finset ℕ) => wval C (indW 26 S)
    let P := Relation.ReflTransGen (fun u w : ℕ => ∃ j < C.size, w = 26+j ∧
     (if (gateAt C j).op.eval [] then u ∈ (gateAt C j).inputs
      else u = if V {0,13} (in0 C j) then in0 C j else in1 C j))
    let K := fun (z j : ℕ) => P (26+j) C.output ∧ isAnd C j ∧
       ∀ t ∈ (gateAt C j).inputs, V {z} t = false
    ∀ (a b j k : ℕ), (a=0 ∧ b=13 ∨ a=13 ∧ b=0) → K a j → K b k →
    V {b} (26+j) = true → V {a} (26+k) = false →
    V {0,13} C.output = true → V {b} C.output = false → ∃ s d : ℕ, s < k ∧ j < d ∧ isAnd C s ∧ isAnd C d ∧
      P (26+s) (26+k) ∧ P (26+j) (26+d) ∧ P (26+d) C.output ∧
      V {b} (in0 C d) ≠ V {b} (in1 C d) ∧
      V {a} (in0 C s) ≠ V {a} (in1 C s) ∧ V {b} (in0 C s) ≠ V {b} (in1 C s) ∧
      V {a} (in0 C s) ≠ V {b} (in0 C s) := by

    let W (C : Circuit) (S : Finset ℕ) (i : ℕ) : Bool :=
      wval C (indW 26 S) i

    let Selected (C : Circuit) (i j : ℕ) : Prop :=
      ∃ (k : ℕ) (g : Gate) (a b : ℕ),
        C.gates[k]? = some g ∧ j = 26 + k ∧ g.inputs = [a, b] ∧
          (g.op = .and ∧ (i = a ∨ i = b) ∨
            g.op = .or ∧ i = if W C {0, 13} a = true then a else b) ∧
          W C {0, 13} i = true ∧ W C {0, 13} j = true

    let Terminal (C : Circuit) (s k : ℕ) : Prop :=
      Relation.ReflTransGen (Selected C) (26 + k) C.output ∧
        isAnd C k ∧ ∀ i ∈ (gateAt C k).inputs, W C {0, 13} i = true ∧ W C {s} i = false

    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

    have fold_prefix (gs : List Gate) (w : List Bool) (i : ℕ)
        (hi : i < w.length) : (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

    have fold_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
        (gs.foldl step w).getD (w.length + k) false =
          (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
            if i < w.length + k then (gs.foldl step w).getD i false else false) := by
      induction gs generalizing w k with
      | nil => simp at hk
      | cons g gs ih =>
        rw [List.foldl_cons]
        cases k with
        | zero =>
          rw [Nat.add_zero, fold_prefix gs (step w g) w.length (by simp [step])]
          have hlast : (step w g).getD w.length false =
              g.op.eval (g.inputs.map fun i => w.getD i false) := by
            simp [step, List.getD_eq_getElem?_getD]
          rw [List.getElem_cons_zero, hlast]
          congr 1
          refine List.map_congr_left fun i _ => ?_
          by_cases hi : i < w.length
          · rw [if_pos hi, fold_prefix gs (step w g) i (by simp [step]; omega)]
            simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
          · rw [if_neg hi]
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)]
        | succ k =>
          have h := ih (step w g) k (by simpa using hk)
          have hlen : (step w g).length = w.length + 1 := by simp [step]
          rw [hlen] at h
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using h

    have lookup {C : Circuit} {k : ℕ} {g : Gate} (hg : C.gates[k]? = some g) :
        gateAt C k = g := by
      obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hg
      change C.gates.getD k _ = g
      rw [List.getD_eq_getElem _ _ hk]
      exact heq

    have gate_equation {C : Circuit} (hAO : IsAO2 26 C)
        (S : Finset ℕ) {k a b : ℕ} {g : Gate} (hg : C.gates[k]? = some g)
        (hin : g.inputs = [a, b]) :
        W C S (26 + k) = g.op.eval [W C S a, W C S b] := by
      obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hg
      have hab := hAO.2.1 k hk
      rw [lookup hg, hin] at hab
      have ha : a < 26 + k := hab a (by simp)
      have hb : b < 26 + k := hab b (by simp)
      let w := List.ofFn (indW 26 S)
      have hlen : w.length = 26 := by simp [w]
      have hw := fold_gate C.gates w k hk
      rw [hlen, heq, hin] at hw
      change (C.gates.foldl step w).getD (26 + k) false =
        g.op.eval [(C.gates.foldl step w).getD a false, (C.gates.foldl step w).getD b false]
      simpa only [List.map_cons, List.map_nil, if_pos ha, if_pos hb] using hw

    have crosses {R : ℕ → ℕ → Prop} (val : ℕ → Bool) (before : Bool)
        {a b : ℕ} (path : Relation.ReflTransGen R a b) :
        val a = before → val b = !before →
          ∃ i j, Relation.ReflTransGen R a i ∧ R i j ∧
            Relation.ReflTransGen R j b ∧ val i = before ∧ val j = !before := by
      induction path with
      | refl =>
        intro ha hb
        have h : before = !before := ha.symm.trans hb
        cases before <;> cases h
      | @tail u v hinit last ih =>
        intro ha hb
        by_cases hm : val u = before
        · exact ⟨u, v, hinit, last, .refl, hm, hb⟩
        · have hm' : val u = !before := by
            cases before <;> cases hx : val u <;> simp_all
          obtain ⟨i, j, left, middle, right, hsa, hsb⟩ := ih ha hm'
          exact ⟨i, j, left, middle, right.tail last, hsa, hsb⟩

    have and_eval (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
      cases a <;> cases b <;> rfl

    have or_eval (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
      cases a <;> cases b <;> rfl

    have selected_path_changes {C : Circuit} (hAO : IsAO2 26 C)
        {S : Finset ℕ} {a b : ℕ} {before : Bool}
        (path : Relation.ReflTransGen (Selected C) a b)
        (ha : W C S a = before) (hb : W C S b = !before) :
        ∃ (i k : ℕ) (g : Gate), Relation.ReflTransGen (Selected C) a i ∧
          Selected C i (26 + k) ∧ Relation.ReflTransGen (Selected C) (26 + k) b ∧
          C.gates[k]? = some g ∧ g.op = (if before = true then .and else .or) ∧
          W C S i = before ∧ W C S (26 + k) = !before := by
      obtain ⟨i, j, left, edge, right, hpre, hpost⟩ := crosses (W C S) before path ha hb
      have edge' := edge
      obtain ⟨k, g, r, s, hg, rfl, hin, choice, _, _⟩ := edge
      have mem : i = r ∨ i = s := by
        rcases choice with ⟨_, h⟩ | ⟨_, h⟩
        · exact h
        · split at h
          · exact Or.inl h
          · exact Or.inr h
      have hv := gate_equation hAO S hg hin
      refine ⟨i, k, g, left, edge', right, hg, ?_, hpre, hpost⟩
      cases before with
      | false =>
        rcases choice with ⟨hop, _⟩ | ⟨hop, _⟩
        · rw [hop, and_eval] at hv
          have hz : W C S (26 + k) = false := by
            rcases mem with h | h
            · simpa [← h, hpre] using hv
            · simpa [← h, hpre] using hv
          rw [hz] at hpost
          cases hpost
        · simpa using hop
      | true =>
        rcases choice with ⟨hop, _⟩ | ⟨hop, _⟩
        · simpa using hop
        · rw [hop, or_eval] at hv
          have ho : W C S (26 + k) = true := by
            rcases mem with h | h
            · simpa [← h, hpre] using hv
            · simpa [← h, hpre] using hv
          rw [ho] at hpost
          cases hpost

    have singleton_terminal_drop {C : Circuit} (hAO : IsAO2 26 C) {s t k : ℕ}
        (hterm : Terminal C s k)
        (hon : W C {t} (26 + k) = true) (hoff : W C {t} C.output = false) :
        ∃ (i j : ℕ) (g : Gate), Relation.ReflTransGen (Selected C) (26 + k) i ∧
          Selected C i (26 + j) ∧
          Relation.ReflTransGen (Selected C) (26 + j) C.output ∧
          C.gates[j]? = some g ∧ g.op = .and ∧
          W C {t} i = true ∧ W C {t} (26 + j) = false := by
      simpa using selected_path_changes hAO (S := {t}) (before := true) hterm.1 hon hoff

    have terminal_off {C : Circuit} (hAO : IsAO2 26 C) {s k : ℕ}
        (hterm : Terminal C s k) : W C {s} (26 + k) = false := by
      obtain ⟨hk, hop⟩ := hterm.2.1
      have heq : gateAt C k = C.gates[k] := by
        simp [gateAt, List.getD_eq_getElem?_getD, hk]
      have hmem : gateAt C k ∈ C.gates := by rw [heq]; exact List.getElem_mem hk
      have hg : C.gates[k]? = some (gateAt C k) :=
        List.getElem?_eq_some_iff.mpr ⟨hk, heq.symm⟩
      obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ hmem)
      have hgate := gate_equation hAO {s} hg hin
      have ha := (hterm.2.2 a (by simp [hin])).2
      have hb := (hterm.2.2 b (by simp [hin])).2
      rw [hop, and_eval, ha, hb] at hgate
      exact hgate

    let ThinStep (C : Circuit) (u w : ℕ) : Prop :=
      ∃ j < C.size, w = 26 + j ∧
        if (gateAt C j).op.eval [] then u ∈ (gateAt C j).inputs
        else u = if W C {0, 13} (in0 C j) then in0 C j else in1 C j

    have selectedOfThinStep {C : Circuit} (model : IsAO2 26 C) {u w : ℕ}
        (step : ThinStep C u w) (active : W C {0, 13} w = true) : Selected C u w := by
      obtain ⟨j, hj, index, choice⟩ := step
      have get : C.gates[j]? = some (gateAt C j) := by
        unfold gateAt
        rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
      have mem : gateAt C j ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem _
      obtain ⟨a, b, ins⟩ := List.length_eq_two.mp (model.2.2 _ mem)
      have eval := gate_equation model {0, 13} get ins
      rw [← index] at eval
      have value := eval.symm.trans active
      rcases model.1 _ mem with isAnd | isOr
      · have chosen : u = a ∨ u = b := by
          simpa [isAnd, GateOp.eval, ins] using choice
        rw [isAnd, and_eval, Bool.and_eq_true] at value
        have required : W C {0, 13} u = true := by
          rcases chosen with rfl | rfl
          · exact value.1
          · exact value.2
        exact ⟨j, gateAt C j, a, b, get, index, ins, Or.inl ⟨isAnd, chosen⟩, required, active⟩
      · have chosen : u = if W C {0, 13} a = true then a else b := by
          simpa [isOr, GateOp.eval, in0, in1, ins] using choice
        rw [isOr, or_eval, Bool.or_eq_true] at value
        have required : W C {0, 13} u = true := by
          by_cases hot : W C {0, 13} a = true
          · simpa only [chosen, if_pos hot] using hot
          · simpa only [chosen, if_neg hot] using value.resolve_left hot
        exact ⟨j, gateAt C j, a, b, get, index, ins, Or.inr ⟨isOr, chosen⟩, required, active⟩

    have thinStepOfSelected {C : Circuit} {u w : ℕ} (step : Selected C u w) : ThinStep C u w := by
      obtain ⟨j, g, a, b, get, index, ins, choice, _, _⟩ := step
      refine ⟨j, (List.getElem?_eq_some_iff.mp get).1, index, ?_⟩
      have read := lookup get
      rcases choice with ⟨isAnd, branch⟩ | ⟨isOr, branch⟩
      · simpa [read, isAnd, ins, GateOp.eval] using branch
      · simpa [in0, in1, read, isOr, ins, GateOp.eval] using branch

    have selectedPathOfThin {C : Circuit} (model : IsAO2 26 C) {u w : ℕ}
        (path : Relation.ReflTransGen (ThinStep C) u w) (active : W C {0, 13} w = true) :
        Relation.ReflTransGen (Selected C) u w ∧ W C {0, 13} u = true := by
      induction path with
      | refl => exact ⟨.refl, active⟩
      | @tail mid dest earlier edge ih =>
        have selected := selectedOfThinStep model edge active
        have midOn : W C {0, 13} mid = true := by
          obtain ⟨_, _, _, _, _, _, _, _, on, _⟩ := selected
          exact on
        obtain ⟨built, sourceOn⟩ := ih midOn
        exact ⟨built.tail selected, sourceOn⟩

    have thinPathOfSelected {C : Circuit} {u w : ℕ}
        (path : Relation.ReflTransGen (Selected C) u w) :
        Relation.ReflTransGen (ThinStep C) u w := by
      induction path with
      | refl => exact .refl
      | tail _ edge ih => exact ih.tail (thinStepOfSelected edge)

    have terminalOfThin {C : Circuit} (model : IsAO2 26 C) {s j : ℕ}
        (path : Relation.ReflTransGen (ThinStep C) (26 + j) C.output)
        (andGate : isAnd C j) (outputOn : W C {0, 13} C.output = true)
        (stops : ∀ w ∈ (gateAt C j).inputs, W C {s} w = false) : Terminal C s j := by
      obtain ⟨trace, on⟩ := selectedPathOfThin model path outputOn
      refine ⟨trace, andGate, ?_⟩
      have get : C.gates[j]? = some (gateAt C j) := by
        unfold gateAt
        rw [List.getElem?_eq_getElem andGate.1, List.getD_eq_getElem _ _ andGate.1]
      have mem : gateAt C j ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ andGate.1]
        exact List.getElem_mem _
      obtain ⟨a, b, ins⟩ := List.length_eq_two.mp (model.2.2 _ mem)
      have good := (gate_equation model {0, 13} get ins).symm.trans on
      rw [andGate.2, and_eval, Bool.and_eq_true] at good
      intro u hu
      refine ⟨?_, stops u hu⟩
      rw [ins] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact good.1
      · exact good.2

    let Cold (C : Circuit) (w : ℕ) : Prop :=
      W C {0, 13} w = true ∧ W C {0} w = false ∧ W C {13} w = false

    let SplitAnd (C : Circuit) (k : ℕ) : Prop :=
      ∃ (g : Gate) (a b : ℕ), C.gates[k]? = some g ∧ g.op = .and ∧ g.inputs = [a, b] ∧
        W C {0, 13} a = true ∧ W C {0, 13} b = true ∧
        ((W C {0} a = true ∧ W C {13} a = false ∧
           W C {0} b = false ∧ W C {13} b = true) ∨
         (W C {0} a = false ∧ W C {13} a = true ∧
           W C {0} b = true ∧ W C {13} b = false))

    have wire_input (C : Circuit) (S : Finset ℕ) (i : ℕ) (hi : i < 26) :
        W C S i = decide (i ∈ S) := by
      change (C.gates.foldl step (List.ofFn (indW 26 S))).getD i false = _
      rw [fold_prefix C.gates (List.ofFn (indW 26 S)) i (by simpa using hi)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true,
        Option.getD_some, indW]

    have input_not_cold {C : Circuit} {i : ℕ} (hi : i < 26) : ¬ Cold C i := by
      rintro ⟨hp, h0, h13⟩
      rw [wire_input C {0, 13} i hi, decide_eq_true_eq] at hp
      have hm : i = 0 ∨ i = 13 := by simpa using hp
      rcases hm with rfl | rfl
      · have h : W C {0} 0 = true := by simpa using wire_input C {0} 0 (by decide)
        rw [h] at h0
        cases h0
      · have h : W C {13} 13 = true := by simpa using wire_input C {13} 13 (by decide)
        rw [h] at h13
        cases h13

    have operands_at {C : Circuit} (hAO : IsAO2 26 C) {k : ℕ}
        (hk : k < C.gates.length) :
        ∃ (g : Gate) (a b : ℕ), C.gates[k]? = some g ∧ g.inputs = [a, b] ∧
          a < 26 + k ∧ b < 26 + k ∧ (g.op = .and ∨ g.op = .or) := by
      let g := C.gates[k]
      have hg : C.gates[k]? = some g := List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩
      have hm : g ∈ C.gates := List.getElem_mem hk
      obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hAO.2.2 g hm)
      have hback := hAO.2.1 k hk
      rw [lookup hg, hin] at hback
      exact ⟨g, a, b, hg, hin, hback a (by simp), hback b (by simp), hAO.1 g hm⟩

    have opposite_singletons (x0 x13 y0 y13 : Bool)
        (hx : x0 = true ∨ x13 = true) (hy : y0 = true ∨ y13 = true)
        (h0 : (x0 && y0) = false) (h13 : (x13 && y13) = false) :
        (x0 = true ∧ x13 = false ∧ y0 = false ∧ y13 = true) ∨
        (x0 = false ∧ x13 = true ∧ y0 = true ∧ y13 = false) := by
      cases x0 <;> cases x13 <;> cases y0 <;> cases y13 <;> simp_all

    have active_singleton {C : Circuit} {i : ℕ}
        (hp : W C {0, 13} i = true) (hnc : ¬ Cold C i) :
        W C {0} i = true ∨ W C {13} i = true := by
      by_cases h0 : W C {0} i = true
      · exact Or.inl h0
      · right
        cases h13 : W C {13} i with
        | true => rfl
        | false =>
          have h0' : W C {0} i = false := by
            cases hz : W C {0} i <;> simp_all
          exact (hnc ⟨hp, h0', h13⟩).elim

    have cold_reaches_split_and {C : Circuit} (hAO : IsAO2 26 C) (w : ℕ) :
        w < 26 + C.gates.length → Cold C w →
        ∃ k, 26 + k ≤ w ∧ SplitAnd C k ∧
          Relation.ReflTransGen (Selected C) (26 + k) w := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hCold
        have hlo : 26 ≤ w := by
          by_contra! hlt
          exact input_not_cold hlt hCold
        obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
        obtain ⟨hp, h0, h13⟩ := hCold
        obtain ⟨g, a, b, hg, hin, ha, hb, hop⟩ := operands_at hAO (by omega : k < C.gates.length)
        have hpGate := gate_equation hAO {0, 13} hg hin
        have h0Gate := gate_equation hAO {0} hg hin
        have h13Gate := gate_equation hAO {13} hg hin
        rcases hop with hop | hop
        · rw [hop, and_eval] at hpGate h0Gate h13Gate
          have hab : W C {0, 13} a = true ∧ W C {0, 13} b = true := by
            simpa only [Bool.and_eq_true] using hpGate.symm.trans hp
          by_cases hca : Cold C a
          · obtain ⟨j, hle, hsplit, hpath⟩ := ih a ha (ha.trans hw) hca
            exact ⟨j, hle.trans ha.le, hsplit,
              hpath.tail ⟨k, g, a, b, hg, rfl, hin, Or.inl ⟨hop, Or.inl rfl⟩, hca.1, hp⟩⟩
          by_cases hcb : Cold C b
          · obtain ⟨j, hle, hsplit, hpath⟩ := ih b hb (hb.trans hw) hcb
            exact ⟨j, hle.trans hb.le, hsplit,
              hpath.tail ⟨k, g, a, b, hg, rfl, hin, Or.inl ⟨hop, Or.inr rfl⟩, hcb.1, hp⟩⟩
          refine ⟨k, le_rfl, ⟨g, a, b, hg, hop, hin, hab.1, hab.2, ?_⟩, .refl⟩
          exact opposite_singletons _ _ _ _ (active_singleton hab.1 hca)
            (active_singleton hab.2 hcb) (h0Gate.symm.trans h0) (h13Gate.symm.trans h13)
        · rw [hop, or_eval] at hpGate h0Gate h13Gate
          have h0ab : W C {0} a = false ∧ W C {0} b = false := by
            simpa only [Bool.or_eq_false_iff] using h0Gate.symm.trans h0
          have h13ab : W C {13} a = false ∧ W C {13} b = false := by
            simpa only [Bool.or_eq_false_iff] using h13Gate.symm.trans h13
          by_cases hpa : W C {0, 13} a = true
          · obtain ⟨j, hle, hsplit, hpath⟩ := ih a ha (ha.trans hw) ⟨hpa, h0ab.1, h13ab.1⟩
            exact ⟨j, hle.trans ha.le, hsplit, hpath.tail
              ⟨k, g, a, b, hg, rfl, hin, Or.inr ⟨hop, by simp [hpa]⟩, hpa, hp⟩⟩
          have hfa : W C {0, 13} a = false := by
            cases hz : W C {0, 13} a <;> simp_all
          have hpb : W C {0, 13} b = true := by simpa [hfa] using hpGate.symm.trans hp
          obtain ⟨j, hle, hsplit, hpath⟩ := ih b hb (hb.trans hw) ⟨hpb, h0ab.2, h13ab.2⟩
          exact ⟨j, hle.trans hb.le, hsplit, hpath.tail
            ⟨k, g, a, b, hg, rfl, hin, Or.inr ⟨hop, by simp [hpa]⟩, hpb, hp⟩⟩

    have factor_false {x y : Bool} (h : (x && y) = false) :
        x = false ∨ y = false := by
      cases x <;> cases y <;> simp_all

    have cold_terminal_has_earlier_split_and {C : Circuit} (hAO : IsAO2 26 C) {k : ℕ}
        (hand : isAnd C k) (hCold : Cold C (26 + k))
        (hall : (∀ i ∈ (gateAt C k).inputs, W C {0} i = false) ∨
                (∀ i ∈ (gateAt C k).inputs, W C {13} i = false)) :
        ∃ j, j < k ∧ SplitAnd C j ∧
          Relation.ReflTransGen (Selected C) (26 + j) (26 + k) := by
      obtain ⟨hk, hop⟩ := hand
      obtain ⟨hp, h0, h13⟩ := hCold
      obtain ⟨g, a, b, hg, hin, ha, hb, _⟩ := operands_at hAO hk
      have ga : gateAt C k = g := lookup hg
      have hop' : g.op = .and := by simpa only [ga] using hop
      have hmA : a ∈ (gateAt C k).inputs := by simp [ga, hin]
      have hmB : b ∈ (gateAt C k).inputs := by simp [ga, hin]
      have hpGate := gate_equation hAO {0, 13} hg hin
      rw [hop', and_eval] at hpGate
      have hab : W C {0, 13} a = true ∧ W C {0, 13} b = true := by
        simpa only [Bool.and_eq_true] using hpGate.symm.trans hp
      have hchild : Cold C a ∨ Cold C b := by
        rcases hall with hall | hall
        · have hgate := gate_equation hAO {13} hg hin
          rw [hop', and_eval] at hgate
          rcases factor_false (hgate.symm.trans h13) with h13a | h13b
          · exact Or.inl ⟨hab.1, hall a hmA, h13a⟩
          · exact Or.inr ⟨hab.2, hall b hmB, h13b⟩
        · have hgate := gate_equation hAO {0} hg hin
          rw [hop', and_eval] at hgate
          rcases factor_false (hgate.symm.trans h0) with h0a | h0b
          · exact Or.inl ⟨hab.1, h0a, hall a hmA⟩
          · exact Or.inr ⟨hab.2, h0b, hall b hmB⟩
      rcases hchild with hca | hcb
      · obtain ⟨j, hle, hsplit, hpath⟩ :=
          cold_reaches_split_and hAO a (by omega) hca
        exact ⟨j, by omega, hsplit,
          hpath.tail ⟨k, g, a, b, hg, rfl, hin, Or.inl ⟨hop', Or.inl rfl⟩, hca.1, hp⟩⟩
      · obtain ⟨j, hle, hsplit, hpath⟩ :=
          cold_reaches_split_and hAO b (by omega) hcb
        exact ⟨j, by omega, hsplit,
          hpath.tail ⟨k, g, a, b, hg, rfl, hin, Or.inl ⟨hop', Or.inr rfl⟩, hcb.1, hp⟩⟩

    have earlier_trace_inequalities {C : Circuit} (hAO : IsAO2 26 C) {a b k : ℕ}
        (roles : (a = 0 ∧ b = 13) ∨ (a = 13 ∧ b = 0))
        (hterm : Terminal C b k) (ha : W C {a} (26 + k) = false) :
        ∃ s, s < k ∧ isAnd C s ∧ Relation.ReflTransGen (Selected C) (26 + s) (26 + k) ∧
          W C {a} (in0 C s) ≠ W C {a} (in1 C s) ∧
          W C {b} (in0 C s) ≠ W C {b} (in1 C s) ∧
          W C {a} (in0 C s) ≠ W C {b} (in0 C s) := by
      obtain ⟨g, r, t, hg, hin, _, _, _⟩ := operands_at hAO hterm.2.1.1
      have hgate := lookup hg
      have hop : g.op = .and := by simpa only [hgate] using hterm.2.1.2
      have hpr := (hterm.2.2 r (by simp [hgate, hin])).1
      have hpt := (hterm.2.2 t (by simp [hgate, hin])).1
      have hp : W C {0, 13} (26 + k) = true := by
        simpa only [hop, and_eval, hpr, hpt, Bool.and_true] using gate_equation hAO {0, 13} hg hin
      have hb := terminal_off hAO hterm
      have hc : Cold C (26 + k) := by
        rcases roles with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hp, ha, hb⟩
        · exact ⟨hp, hb, ha⟩
      have hall : (∀ i ∈ (gateAt C k).inputs, W C {0} i = false) ∨
          (∀ i ∈ (gateAt C k).inputs, W C {13} i = false) := by
        rcases roles with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (fun i hi => (hterm.2.2 i hi).2)
        · exact Or.inl (fun i hi => (hterm.2.2 i hi).2)
      obtain ⟨s, hlt, hsplit, hpath⟩ := cold_terminal_has_earlier_split_and hAO hterm.2.1 hc hall
      obtain ⟨d, x, y, hd, hAnd, hInputs, _, _, hOpp⟩ := hsplit
      obtain ⟨hReal, _⟩ := List.getElem?_eq_some_iff.mp hd
      have hLookup : gateAt C s = d := lookup hd
      have hx : in0 C s = x := by simp [in0, hLookup, hInputs]
      have hy : in1 C s = y := by simp [in1, hLookup, hInputs]
      refine ⟨s, hlt, ⟨hReal, by simpa only [hLookup] using hAnd⟩, hpath, ?_⟩
      rw [hx, hy]
      rcases roles with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hOpp with ⟨h0x, h13x, h0y, h13y⟩ | ⟨h0x, h13x, h0y, h13y⟩ <;>
        simp [h0x, h13x, h0y, h13y]

    have selectedFromOperand {C : Circuit} {u w : ℕ} (step : Selected C u w) :
        ∃ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]? = some g ∧ w = 26 + k ∧
          g.inputs = [a, b] ∧ (u = a ∨ u = b) := by
      obtain ⟨k, g, a, b, get, index, inputs, choice, _, _⟩ := step
      refine ⟨k, g, a, b, get, index, inputs, ?_⟩
      rcases choice with h | ⟨_, h⟩
      · exact h.2
      · split at h
        · exact Or.inl h
        · exact Or.inr h

    have selectedGoesForward {C : Circuit} (model : IsAO2 26 C) {u w : ℕ}
        (step : Selected C u w) : u < w := by
      obtain ⟨k, g, a, b, get, index, inputs, fromInput⟩ := selectedFromOperand step
      have earlier := model.2.1 k (List.getElem?_eq_some_iff.mp get).1 u
      rw [lookup get, inputs] at earlier
      have order := earlier (by simp [fromInput])
      omega

    have selectedPathGoesForward {C : Circuit} (model : IsAO2 26 C) {u w : ℕ}
        (path : Relation.ReflTransGen (Selected C) u w) : u ≤ w := by
      induction path with
      | refl => exact le_rfl
      | tail _ edge ih => exact ih.trans (selectedGoesForward model edge).le

    have andDropHasDifferentOperands {C : Circuit} (model : IsAO2 26 C)
        {u k t : ℕ} (step : Selected C u (26 + k)) (isAndGate : isAnd C k)
        (arrival : W C {t} u = true) (departure : W C {t} (26 + k) = false) :
        W C {t} (in0 C k) ≠ W C {t} (in1 C k) := by
      obtain ⟨j, g, a, b, get, index, inputs, source⟩ := selectedFromOperand step
      have equalIndex : j = k := by omega
      subst j
      have op : g.op = .and := (congrArg Gate.op (lookup get)).symm.trans isAndGate.2
      have eval := gate_equation model {t} get inputs
      rw [op, and_eval, departure] at eval
      intro equal
      have operands : W C {t} a = W C {t} b := by
        simpa [in0, in1, lookup get, inputs] using equal
      have bothA : W C {t} a = true := by
        rcases source with rfl | rfl
        · exact arrival
        · exact operands.trans arrival
      have bothB := operands.symm.trans bothA
      simp [bothA, bothB] at eval

    let ThinTerminal (C : Circuit) (a j : ℕ) : Prop :=
      Relation.ReflTransGen (ThinStep C) (26 + j) C.output ∧ isAnd C j ∧
        ∀ t ∈ (gateAt C j).inputs, W C {a} t = false

    have reductionTrace (C : Circuit) (model : IsAO2 26 C) (a b j k : ℕ)
        (roles : (a = 0 ∧ b = 13) ∨ (a = 13 ∧ b = 0))
        (hot : ThinTerminal C a j) (cold : ThinTerminal C b k)
        (hotOn : W C {b} (26 + j) = true) (coldOff : W C {a} (26 + k) = false)
        (outputOn : W C {0, 13} C.output = true) (outputOff : W C {b} C.output = false) :
        ∃ s d : ℕ, s < k ∧ j < d ∧ isAnd C s ∧ isAnd C d ∧
          Relation.ReflTransGen (ThinStep C) (26 + s) (26 + k) ∧
          Relation.ReflTransGen (ThinStep C) (26 + j) (26 + d) ∧
          Relation.ReflTransGen (ThinStep C) (26 + d) C.output ∧
          W C {b} (in0 C d) ≠ W C {b} (in1 C d) ∧
          W C {a} (in0 C s) ≠ W C {a} (in1 C s) ∧
          W C {b} (in0 C s) ≠ W C {b} (in1 C s) ∧
          W C {a} (in0 C s) ≠ W C {b} (in0 C s) := by
      have hotTerm := terminalOfThin model hot.1 hot.2.1 outputOn hot.2.2
      have coldTerm := terminalOfThin model cold.1 cold.2.1 outputOn cold.2.2
      obtain ⟨s, sk, andS, toCold, splitA, splitB, splitAB⟩ :=
        earlier_trace_inequalities model roles coldTerm coldOff
      obtain ⟨i, d, gate, toInput, enter, leave, get, op, inputOn, gateOff⟩ :=
        singleton_terminal_drop model hotTerm hotOn outputOff
      have andD : isAnd C d := ⟨(List.getElem?_eq_some_iff.mp get).1,
        (congrArg Gate.op (lookup get)).trans op⟩
      have jd : j < d := by
        have left := selectedPathGoesForward model toInput
        have right := selectedGoesForward model enter
        omega
      exact ⟨s, d, sk, jd, andS, andD, thinPathOfSelected toCold,
        thinPathOfSelected (toInput.tail enter), thinPathOfSelected leave,
        andDropHasDifferentOperands model enter andD inputOn gateOff, splitA, splitB, splitAB⟩

    exact reductionTrace
  intro C lo hi ao distinct ev noL noP
  dsimp only
  intro witness
  obtain ⟨i,j,_,wa,wb,mixed⟩ := witness
  let V := fun (S : Finset ℕ) => wval C (indW 26 S)
  let T := fun u w : ℕ => ∃ j < C.size, w = 26+j ∧
     (if (gateAt C j).op.eval [] then u ∈ (gateAt C j).inputs
      else u = if V {0,13} (in0 C j) then in0 C j else in1 C j)
  let P := Relation.ReflTransGen T
  let K := fun (z j : ℕ) => P (26+j) C.output ∧ isAnd C j ∧
       ∀ t ∈ (gateAt C j).inputs, V {z} t = false
  have rawStep {u w : ℕ} (h : ∃ (j : ℕ) (g : Gate) (l r : ℕ), C.gates[j]? = some g ∧
      w = 26+j ∧ g.inputs = [l,r] ∧
      (g.op = GateOp.and ∧ (u=l ∨ u=r) ∨ g.op = GateOp.or ∧ u=if V {0,13} l then l else r) ∧
      V {0,13} u = true ∧ V {0,13} w = true) : T u w := by
    obtain ⟨j,g,l,r,hj,rfl,ins,op,_⟩ := h
    obtain ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp hj
    have hit : gateAt C j = g := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ bound,eq]
    refine ⟨j,bound,rfl,?_⟩
    rcases op with ⟨hand,tmp⟩|⟨hor,tmp⟩
    · have h : (gateAt C j).op.eval [] = true := by rw [hit,hand]; rfl
      rw [h,if_pos rfl,hit,ins]; simpa using tmp
    · have h : (gateAt C j).op.eval [] = false := by rw [hit,hor]; rfl
      rw [h,if_neg Bool.false_ne_true]
      change u = if V {0,13} ((gateAt C j).inputs.getD 0 0) then (gateAt C j).inputs.getD 0 0 else (gateAt C j).inputs.getD 1 0
      rw [hit,ins]
      exact tmp
  have ci : K 0 i := ⟨Relation.ReflTransGen.mono (fun _ _ h => rawStep h) _ _ wa.1, wa.2.1, fun u hu => (wa.2.2 u hu).2⟩
  have cj : K 13 j := ⟨Relation.ReflTransGen.mono (fun _ _ h => rawStep h) _ _ wb.1, wb.2.1, fun u hu => (wb.2.2 u hu).2⟩
  let f := fpl 13 (fun p l => p ∈ singerLines3 l)
  have full : circuitFun 26 C = f := by
    funext x
    rw [Bool.eq_iff_iff]
    change C.eval _ = true ↔ decide (∃ p l : Fin 13, p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) = true
    rw [decide_eq_true_iff,ev x]
    have plane (p l : Fin 13) : (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ↔ p ∈ singerLines3 l :=
      (by decide +kernel : ∀ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ↔ p ∈ singerLines3 l) p l
    simp only [plane]
  have val (S) : V S C.output = f (indW 26 S) := congrFun full _
  have pair : V {0,13} C.output = true := (val _).trans (by decide +kernel)
  have off0 : V {0} C.output = false := (val _).trans (by decide +kernel)
  have off13 : V {13} C.output = false := (val _).trans (by decide +kernel)
  have ns : ∀ a ∈ ([0,13] : List ℕ), lineSingle C 26 (fun u => decide (u=a)) (13-a) a = false := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl
    · exact noP
    · exact noL
  let ok := (fun C : Circuit => 63 ≤ C.size ∧ C.size ≤ 64 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
    circuitFun 26 C = fpl 13 (fun p l => p ∈ singerLines3 l) ∧
    ∀ a ∈ ([0,13] : List ℕ), lineSingle C 26 (fun i => decide (i=a)) (13-a) a = false)
  let Q := (fun (C : Circuit) (a b : ℕ) => let V := fun (S : Finset ℕ) => wval C (indW 26 S); let P := Relation.ReflTransGen (fun u w : ℕ => ∃ j < C.size, w = 26+j ∧ (if (gateAt C j).op.eval [] then u ∈ (gateAt C j).inputs else u = if V {0,13} (in0 C j) then in0 C j else in1 C j)); let K := fun (z j : ℕ) => P (26+j) C.output ∧ isAnd C j ∧ ∀ t ∈ (gateAt C j).inputs, V {z} t = false; ∃ i j, K a i ∧ K b j ∧ V {b} (26+i)=true ∧ V {a} (26+j)=false)
  have fits : ok C := ⟨lo,hi,ao,distinct,full,ns⟩
  have run (A : Circuit) (fitsA : ok A) (hit : Q A 0 13) : False := by
    obtain ⟨loA,hiA,aoA,distinctA,fullA,nsA⟩ := fitsA
    obtain ⟨j,k,cj,ck,hot,cold⟩ := hit
    have atPair : wval A (indW 26 {0,13}) A.output = true :=
      (congrFun fullA _).trans (by decide +kernel)
    have atLine : wval A (indW 26 {13}) A.output = false :=
      (congrFun fullA _).trans (by decide +kernel)
    exact bound A loA hiA aoA distinctA fullA nsA j k cj ck hot cold
      (trace A aoA 0 13 j k (Or.inl ⟨rfl,rfl⟩) cj ck hot cold atPair atLine)
  change V {13} (26+i) ≠ V {0} (26+j) at mixed
  by_cases h : V {13} (26+i) = true
  · have cold : V {0} (26+j) = false := Bool.eq_false_iff.mpr (fun e => mixed (h.trans e.symm))
    exact run C fits ⟨i,j,ci,cj,h,cold⟩
  · have h0 : V {13} (26+i) = false := Bool.eq_false_iff.mpr h
    have hot : V {0} (26+j) = true := by
      cases e : V {0} (26+j) <;> first | rfl | exact False.elim (mixed (h0.trans e.symm))
    obtain ⟨D,okD,marked⟩ := polarity C fits ⟨j,i,cj,ci,hot,h0⟩
    exact run D okD marked
