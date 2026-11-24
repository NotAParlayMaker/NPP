import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.CircuitMoves

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_1749_312
    (hSingle : let S := singerLines3
      let rows := fun (s : Bool) (x : List Bool) => if s then
        ∃ p l : Fin 13, p ∈ S l ∧ x = (List.ofFn fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))
        else ∃ Q ∈ quadrangles S, x = (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ List.ofFn (fun v : Fin 13 => decide (v ∈ missLines S Q))
      let Pass := fun C : Circuit => ∀ s x, rows s x → C.eval x = s
      ∀ C : Circuit, IsAO2 26 C → Pass C →
        (andPairs 26 C = 1) →
        (∀ j < C.size, ∀ s, ∃ x, rows s x ∧ (C.wires x).getD (26+j) false = s) →
        (∀ j < C.size, ∀ a ∈ (gateAt C j).inputs, ¬ Pass (eraseGate 26 C j a)) → 64 ≤ C.size)
    (hMany : let S := singerLines3
      let rows := fun (s : Bool) (x : List Bool) => if s then
        ∃ p l : Fin 13, p ∈ S l ∧ x = (List.ofFn fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))
        else ∃ Q ∈ quadrangles S, x = (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ List.ofFn (fun v : Fin 13 => decide (v ∈ missLines S Q))
      let Pass := fun C : Circuit => ∀ s x, rows s x → C.eval x = s
      ∀ C : Circuit, IsAO2 26 C → Pass C →
        (2 ≤ andPairs 26 C) →
        (∀ j < C.size, ∀ s, ∃ x, rows s x ∧ (C.wires x).getD (26+j) false = s) →
        (∀ j < C.size, ∀ a ∈ (gateAt C j).inputs, ¬ Pass (eraseGate 26 C j a)) → 64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x10 ∧ x2 x10 ∧ x10.size < x4.size := by
  classical
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl

  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp (config := {congrConsts := false})
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp (config := {congrConsts := false}) [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp (config := {congrConsts := false}) only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp (config := {congrConsts := false}) at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp (config := {congrConsts := false}) only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp (config := {congrConsts := false}) [stepWire]; omega)]
          simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa (config := {congrConsts := false}) using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp (config := {congrConsts := false}) [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp (config := {congrConsts := false}) only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  let OpMono (R : Bool → Bool → Prop) : Prop :=
    ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
      (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

  have opMono_eq : OpMono Eq := by
    intro op _ l f g h
    rw [List.map_congr_left h]

  have opMono_imp : OpMono (fun a b => a = true → b = true) := by
    intro op hop l f g h
    rcases hop with rfl | rfl
    · simp (config := {congrConsts := false}) only [evalAnd, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro h1 i hi; exact h i hi (h1 i hi)
    · simp (config := {congrConsts := false}) only [evalOr, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp (config := {congrConsts := false}) only [evalOr, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

  have val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
      val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp (config := {congrConsts := false}) only [evalAnd, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
      · rw [ite_eq_right hlt] at h'; cases h'
    · intro h i hi
      rw [ite_eq_left (h i hi).1]; exact (h i hi).2

  have val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
      (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
      (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu
      by_cases hun : u < n
      · rw [val_input hx hun, val_input hx hun]
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < m := by omega
        rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < n + k
        · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
        · rw [ite_eq_right hi, ite_eq_right hi]

  let aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

  let aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

  let bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
    ⟨(List.range (C.gates.length - 1)).map (fun k =>
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
      aliasWire (n + r) i C.output⟩

  have bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).gates.length = C.gates.length - 1 := by simp (config := {congrConsts := false}) [bypass]

  have bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

  have gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
      gateAt (bypass n C r i) k =
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
    have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
    rw [gateAt_eq hk']
    simp (config := {congrConsts := false}) [bypass]

  have bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
      (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
    apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
    intro k hk
    rw [gateAt_bypass (by omega), ite_eq_left hk]

  have aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp (config := {congrConsts := false}) [aliasWire]

  have aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

  have aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

  have bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : (∃ k, k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
        R (val C x (n + r)) (val C x i)) :
      ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hne
      by_cases hlt : u < n + r
      · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
      · rw [aliasWire_gt_self (by omega)]
        by_cases hge : n + C.gates.length ≤ u
        · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
        · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
          have hk1 : k + 1 < C.gates.length := by omega
          have hkr : ¬ k < r := by omega
          have e : n + (k + 1) - 1 = n + k := by omega
          rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
            gateAt_bypass (by omega), ite_eq_right hkr]
          simp (config := {congrConsts := false}) only [aliasGate, List.map_map]
          refine hmono _ (hAO _ hk1) _ _ _ ?_
          intro i' hi'
          simp (config := {congrConsts := false}) only [Function.comp_apply]
          by_cases h1 : i' = n + r
          · subst h1
            rw [aliasWire_self, ite_eq_left (by omega)]
            have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
              rcases hi with hi | hi
              · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
              · rw [ite_eq_right (by omega), val_ge hx hi]
            rw [hgi]
            exact hR ⟨k + 1, hk1, hi'⟩
          · by_cases h2 : i' < n + r
            · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
                bypass_val_lt hx hr i' h2]
              exact hrefl _
            · by_cases h3 : i' < n + (k + 1)
              · have key := ih i' h3 h1
                rw [aliasWire_gt_self (by omega)] at key
                rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
                exact key
              · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
                exact hrefl _

  have bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : R (val C x (n + r)) (val C x i)) :
      R (C.eval x) ((bypass n C r i).eval x) := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    by_cases h : C.output = n + r
    · have hgi : val (bypass n C r i) x i = val C x i := by
        rcases hi with hi | hi
        · exact bypass_val_lt hx hr i hi
        · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
      rw [h, aliasWire_self, hgi]; exact hR
    · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

  have bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : val C x (n + r) = val C x i) :
      (bypass n C r i).eval x = C.eval x :=
    (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

  have bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hout : C.output ≠ n + r)
      (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
      (bypass n C r i).eval x = C.eval x := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
      (fun h => h.elim fun k hk => absurd hk.2 (hno k hk.1)) _ hout).symm

  have bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
      ∀ k < (bypass n C r i).gates.length,
        (gateAt (bypass n C r i) k).op = GateOp.and ∨
          (gateAt (bypass n C r i) k).op = GateOp.or := by
    intro k hk
    rw [bypass_length] at hk
    rw [gateAt_bypass hk]
    split_ifs with h
    · exact hAO k (by omega)
    · exact hAO (k + 1) (by omega)

  have bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
      ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
        g.inputs.length = g'.inputs.length := by
    intro g hg
    simp (config := {congrConsts := false}) only [bypass, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    split_ifs with h
    · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
    · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp (config := {congrConsts := false}) [aliasGate]⟩

  have aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
      aliasWire w i u < m := by
    unfold aliasWire; split_ifs <;> omega

  have bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
      (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
      ∀ k < (bypass n C r i).gates.length,
        ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
    intro k hk u hu
    rw [bypass_length] at hk
    rw [gateAt_bypass hk] at hu
    split_ifs at hu with h
    · exact hRB k (by omega) u hu
    · simp (config := {congrConsts := false}) only [aliasGate, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      have := hRB (k + 1) (by omega) u' hu'
      exact aliasWire_lt hi (by omega) (by omega)

  intro D OK Nested C hMono hBack hC hSize hNested
  let S := singerLines3
  let pos := fun p l : Fin 13 => (List.ofFn fun u : Fin 13 => decide (u = p)) ++
    List.ofFn (fun v : Fin 13 => decide (v = l))
  let neg := fun Q : Finset (Fin 13) => (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (v ∈ missLines S Q))
  let Pass := fun A : Circuit => (∀ p l, p ∈ S l → A.eval (pos p l) = true) ∧
    (∀ Q ∈ quadrangles S, A.eval (neg Q) = false)
  have hInc : ∀ p l : Fin 13, p - l ∈ D ↔ p ∈ S l := by decide
  have hGeom (Q : Finset (Fin 13)) : Q ∈ quadrangles S ↔
      Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2 := by
    have heq (k : Fin 13) : Q ∩ S k = Q.filter (fun u => u - k ∈ D) := by
      ext u
      simp (config := {congrConsts := false}) [hInc u k]
    change Q ∈ ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter
      (fun A => ∀ l : Fin 13, (A ∩ S l).card ≤ 2) ↔ _
    simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and, heq]
  have hNeg (Q : Finset (Fin 13)) : neg Q = (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++
      List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D)) := by
    have tail : (List.ofFn (fun v : Fin 13 => decide (v ∈ missLines S Q))) =
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D)) := by
      apply congrArg List.ofFn
      funext v
      apply decide_eq_decide.mpr
      change (v ∈ (Finset.univ : Finset (Fin 13)).filter (fun l => Disjoint (S l) Q)) ↔ _
      simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, ← hInc]
      exact ⟨fun h r hr hi => h hi hr, fun h r hi hr => h r hr hi⟩
    exact congrArg (fun xs => (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ xs) tail
  have hPass (A : Circuit) : Pass A ↔ OK A := by
    constructor
    · rintro ⟨hp, hq⟩
      exact ⟨fun p l h => hp p l ((hInc p l).mp h), fun Q h1 h2 => by
        simpa (config := {congrConsts := false}) only [hNeg] using hq Q ((hGeom Q).mpr ⟨h1, h2⟩)⟩
    · rintro ⟨hp, hq⟩
      exact ⟨fun p l h => hp p l ((hInc p l).mpr h), fun Q h => by
        rw [hNeg]; exact hq Q ((hGeom Q).mp h).1 ((hGeom Q).mp h).2⟩
  let Row := fun (s : Bool) (x : List Bool) => if s then
    ∃ p l, p ∈ S l ∧ x = pos p l else ∃ Q ∈ quadrangles S, x = neg Q
  have rowLen (s : Bool) (x : List Bool) (hx : Row s x) : x.length = 26 := by
    cases s
    · obtain ⟨Q, _, rfl⟩ := hx
      simp (config := {congrConsts := false}) [neg]
    · obtain ⟨p, l, _, rfl⟩ := hx
      simp (config := {congrConsts := false}) [pos]
  have someRow (s : Bool) : ∃ x, Row s x := by
    cases s
    · refine ⟨neg {0,1,2,5}, {0,1,2,5}, ?_, rfl⟩
      apply (hGeom _).mpr
      decide
    · exact ⟨pos 0 0, 0, 0, by decide, rfl⟩
  have rowPass (A : Circuit) : Pass A ↔ ∀ s x, Row s x → A.eval x = s := by
    constructor
    · intro h s x hx
      cases s
      · obtain ⟨Q, hh, rfl⟩ := hx
        exact h.2 Q hh
      · obtain ⟨p, l, hh, rfl⟩ := hx
        exact h.1 p l hh
    · intro h
      exact ⟨fun p l hp => h true _ ⟨p,l,hp,rfl⟩, fun Q hQ => h false _ ⟨Q,hQ,rfl⟩⟩
  have initial := (rowPass C).mp ((hPass C).mpr hC)
  have hOps : ∀ j < C.gates.length,
      (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    intro j hj
    simpa (config := {congrConsts := false}) only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hMono _ (gateAt_mem hj)).1
  have hValues {s : Bool} {x : List Bool} (hx : Row s x) {j : ℕ} (hj : j < C.gates.length) :
      val C x (26+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (val C x)) := by
    rw [val_gate (rowLen s x hx) hj]
    congr 1
    exact List.map_congr_left fun i hi => ite_eq_left (hBack j hj i hi)
  by_contra noSmaller
  have noBypass (j a : ℕ) (hj : j < C.gates.length) (ha : a < 26+j) :
      ¬ Pass (bypass 26 C j a) := by
    intro h
    apply noSmaller
    refine ⟨bypass 26 C j a, ?_, bypass_readsBack ha hBack, (hPass _).mp h, ?_⟩
    · intro g hg
      obtain ⟨g', hg', ho, hl⟩ := bypass_mem g hg
      simpa (config := {congrConsts := false}) only [ho, hl] using hMono g' hg'
    · change (bypass 26 C j a).gates.length < C.gates.length
      rw [bypass_length]
      omega
  have constFree (b : Bool) : ∀ j < C.gates.length, ∃ x, Row (!b) x ∧ val C x (26+j) ≠ b := by
    let bad := fun j => ∀ x, Row (!b) x → val C x (26+j) = b
    intro j hj
    by_contra noWitness
    have hBad : bad j := by
      intro x hx
      by_contra hn
      exact noWitness ⟨x,hx,hn⟩
    let badGates := (Finset.range C.gates.length).filter bad
    have hNonempty : badGates.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hBad⟩⟩
    let k := badGates.max' hNonempty
    obtain ⟨hk, hK⟩ := Finset.mem_filter.mp (Finset.max'_mem badGates hNonempty)
    have hki : k < C.gates.length := Finset.mem_range.mp hk
    have notBad (t : ℕ) (ht : t < C.gates.length) (hkt : k < t) : ¬ bad t := by
      intro h
      have hb : t ∈ badGates := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht,h⟩
      exact (Nat.not_le_of_lt hkt) (Finset.le_max' badGates t hb)
    have hout : C.output ≠ 26+k := by
      intro he
      obtain ⟨x,hx⟩ := someRow (!b)
      have e := initial (!b) x hx
      rw [eval_eq_val, he, hK x hx] at e
      cases b <;> cases e
    by_cases unread : ∀ t < C.gates.length, 26+k ∉ (gateAt C t).inputs
    · apply noBypass k 0 hki (by omega)
      apply (rowPass _).mpr
      intro s x hx
      rw [bypass_eval_unread (rowLen s x hx) hOps hki (Or.inl (by omega)) hout unread]
      exact initial s x hx
    push Not at unread
    obtain ⟨t,ht,hread⟩ := unread
    have hkt : k < t := by have := hBack t ht _ hread; omega
    have hn := notBad t ht hkt
    have hop : (gateAt C t).op = (if b then GateOp.and else GateOp.or) := by
      rcases hOps t ht with h | h
      · cases b
        · exfalso
          apply hn
          intro x hx
          apply Bool.eq_false_iff.mpr
          intro hy
          have he := (val_and (rowLen _ _ hx) ht h).mp hy _ hread
          rw [hK x hx] at he
          exact Bool.noConfusion he.2
        · exact h
      · cases b
        · exact h
        · exfalso
          apply hn
          intro x hx
          exact (val_or (rowLen _ _ hx) ht h).mpr ⟨_, hread, hBack t ht _ hread, hK x hx⟩
    have hTwo := (hMono _ (gateAt_mem ht)).2
    cases hList : (gateAt C t).inputs with
    | nil => simp (config := {congrConsts := false}) [hList] at hread
    | cons a tail =>
      cases tail with
      | nil =>
        have ha : a = 26+k := by simpa (config := {congrConsts := false}) [hList, eq_comm] using hread
        apply hn
        intro x hx
        rw [hValues hx ht, hop, hList, ha, List.map_cons, hK x hx]
        cases b <;> rfl
      | cons c tail =>
        have ht0 : tail = [] := by
          apply List.length_eq_zero_iff.mp
          rw [hList] at hTwo
          simp (config := {congrConsts := false}) only [List.length_cons] at hTwo
          omega
        subst tail
        have hread' : 26+k = a ∨ 26+k = c := by simpa (config := {congrConsts := false}) [hList] using hread
        have partner : ∃ u ∈ (gateAt C t).inputs, ∀ x, Row (!b) x →
            val C x (26+t) = val C x u := by
          rcases hread' with h | h
          · refine ⟨c, by simp (config := {congrConsts := false}) [hList], ?_⟩
            intro x hx
            rw [hValues hx ht, hop, hList, ← h, List.map_cons, List.map_cons, hK x hx]
            cases b <;> cases val C x c <;> rfl
          · refine ⟨a, by simp (config := {congrConsts := false}) [hList], ?_⟩
            intro x hx
            rw [hValues hx ht, hop, hList, ← h, List.map_cons, List.map_cons, hK x hx]
            cases b <;> cases val C x a <;> rfl
        obtain ⟨u,hu,he⟩ := partner
        have hul := hBack t ht u hu
        apply noBypass t u ht hul
        apply (rowPass _).mpr
        intro s x hx
        have hxlen := rowLen s x hx
        by_cases hs : s = !b
        · subst s
          rw [bypass_eval_eq hxlen hOps ht (Or.inl hul) (he x hx)]
          exact initial _ _ hx
        · have hs' : s = b := by cases b <;> cases s <;> first | rfl | exact (hs rfl).elim
          subst s
          cases b
          · have hh : val C x u = true → val C x (26+t) = true := fun h =>
              (val_or hxlen ht hop).mpr ⟨u, hu, hul, h⟩
            have hRel := bypass_eval_rel (R := fun a b => b = true → a = true)
              (fun _ h => h) (fun o ho l f g h => opMono_imp o ho l g f h)
              hxlen hOps ht (Or.inl hul) hh
            exact Bool.eq_false_iff.mpr fun h => Bool.noConfusion ((initial false x hx).symm.trans (hRel h))
          · have hh : val C x (26+t) = true → val C x u = true := fun h =>
              ((val_and hxlen ht hop).mp h u hu).2
            exact (bypass_eval_rel (R := fun a b => a = true → b = true)
              (fun _ h => h) opMono_imp hxlen hOps ht (Or.inl hul) hh) (initial true x hx)
  have hAll : ∀ j < C.size, ∀ s, ∃ x, Row s x ∧ val C x (26+j) = s := by
    intro j hj s
    cases s
    · obtain ⟨x,hx,hv⟩ := constFree true j hj
      exact ⟨x,hx,Bool.eq_false_iff.mpr hv⟩
    · obtain ⟨x,hx,hv⟩ := constFree false j hj
      exact ⟨x,hx,by cases he : val C x (26+j) <;> first | rfl | exact (hv he).elim⟩
  have hStrict : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 := by
    intro j hj
    have hLen := (hMono _ (gateAt_mem hj)).2
    have unary (a : ℕ) (hh : (gateAt C j).inputs = [a]) : False := by
      have ha : a ∈ (gateAt C j).inputs := by simp (config := {congrConsts := false}) [hh]
      have hal := hBack j hj a ha
      apply noBypass j a hj hal
      apply (rowPass _).mpr
      intro s x hx
      have he : val C x (26+j) = val C x a := by
        rw [hValues hx hj]
        rcases hOps j hj with ho | ho <;> rw [ho,hh,List.map_cons] <;> cases val C x a <;> rfl
      rw [bypass_eval_eq (rowLen _ _ hx) hOps hj (Or.inl hal) he]
      exact initial s x hx
    cases hList : (gateAt C j).inputs with
    | nil =>
      rcases hOps j hj with h | h
      · obtain ⟨x,hx,hF⟩ := hAll j hj false
        rw [hValues hx hj, h, hList] at hF
        cases hF
      · obtain ⟨x,hx,hT⟩ := hAll j hj true
        rw [hValues hx hj, h, hList] at hT
        cases hT
    | cons a rest =>
      cases rest with
      | nil => exact (unary a hList).elim
      | cons b rest =>
        have he : rest = [] := by
          apply List.length_eq_zero_iff.mp
          rw [hList] at hLen
          simp (config := {congrConsts := false}) only [List.length_cons] at hLen
          omega
        subst rest
        rfl
  have strictMem : ∀ g ∈ C.gates, g.inputs.length = 2 := by
    intro g hg
    obtain ⟨j,hj,hg'⟩ := List.mem_iff_getElem.mp hg
    simpa (config := {congrConsts := false}) only [gateAt_eq hj, hg'] using hStrict j hj
  have erase_eq (j a : ℕ) (hj : j < C.gates.length) : eraseGate 26 C j a = bypass 26 C j a := by
    dsimp only [eraseGate]
    rw [ite_eq_left hj]
    change Circuit.mk _ _ = Circuit.mk _ _
    congr 1
    apply List.ext_getElem
    · simp (config := {congrConsts := false}) [bypass]; omega
    · intro k hk hd
      have hp : (C.gates.take j).length = j := by simp (config := {congrConsts := false}); omega
      have hd' : k < C.gates.length - 1 := by simpa (config := {congrConsts := false}) only [List.length_map,List.length_range] using hd
      simp (config := {congrConsts := false}) only [List.getElem_map, List.getElem_range]
      by_cases hkj : k < j
      · rw [List.getElem_append_left (by omega), ite_eq_left hkj, gateAt_eq (by omega)]
        simp (config := {congrConsts := false})
      · rw [List.getElem_append_right (by omega), ite_eq_right hkj, gateAt_eq (by omega)]
        have hindex : j + 1 + (k - (C.gates.take j).length) = k + 1 := by omega
        simp (config := {congrConsts := false}) only [List.getElem_map, List.getElem_drop, hindex]
        rfl
  have irreducible : ∀ j < C.size, ∀ a ∈ (gateAt C j).inputs, ¬ Pass (eraseGate 26 C j a) := by
    intro j hj a ha
    rw [erase_eq j a hj]
    exact noBypass j a hj (hBack j hj a ha)
  have shape : IsAO2 26 C := by
    exact ⟨fun g hg => by simpa (config := {congrConsts := false}) only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hMono g hg).1,
      hBack, strictMem⟩
  have hSome : 0 < andPairs 26 C := by
    letI := gateOpDecEq
    obtain ⟨i,j,hi,hj,hc⟩ := hNested
    have inside (k : ℕ) (hk : (gateAt C k).op = GateOp.and) : k < C.gates.length := by
      by_contra h
      dsimp only [gateAt] at hk
      rw [List.getD_eq_default _ _ (by omega)] at hk
      cases hk
    have member : (i,j) ∈
        ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter fun p =>
          (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 26 C p.1 p.2) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (inside i hi),
        Finset.mem_range.mpr (inside j hj)⟩, hi,hj,hc⟩
    exact Finset.card_pos.mpr ⟨_,member⟩
  have hLarge : 64 ≤ C.size := by
    by_cases hcount : andPairs 26 C ≤ 1
    · exact hSingle C shape initial (by omega) hAll
        (fun j hj a ha h => irreducible j hj a ha ((rowPass _).mpr h))
    · exact hMany C shape initial (by omega) hAll
        (fun j hj a ha h => irreducible j hj a ha ((rowPass _).mpr h))
  omega
