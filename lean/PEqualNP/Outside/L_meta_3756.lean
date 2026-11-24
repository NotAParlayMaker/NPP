import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3756

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core

private def Goal (n : ℕ) (C : Circuit) (u v : Fin n) : Prop :=
  (∃ X < C.gates.length, ∃ Y < C.gates.length, ∃ (A Q P N : ℕ) (z w : Fin n),
    InOutputCone n C X ∧ (gateAt C X).op = GateOp.and ∧
    ((gateAt C X).inputs = [A, Q] ∨ (gateAt C X).inputs = [Q, A]) ∧
    (gateAt C Y).op = GateOp.and ∧
    ((gateAt C Y).inputs = [P, N] ∨ (gateAt C Y).inputs = [N, P]) ∧
    OrReaches n C Q Y ∧ ((z = u ∧ w = v) ∨ (z = v ∧ w = u)) ∧
    z ∈ orIn n C A ∧ z ∈ orIn n C P ∧ w ∈ orIn n C N) ∨
  (∃ W < C.gates.length, ∃ L M : ℕ,
    InOutputCone n C W ∧ (gateAt C W).op = GateOp.and ∧
    (gateAt C W).inputs = [L, M] ∧ gateVal n C W (pairInput u v) = true ∧
    u ∉ orIn n C L ∧ v ∉ orIn n C L ∧ u ∉ orIn n C M ∧ v ∉ orIn n C M)

private def wval (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private def rv (C : Circuit) (n : ℕ) (u v : Fin n) (w : ℕ) : List (List ℕ) :=
  (readVectors C n [u.val, v.val] 1).getD w []

private def OneHotOff (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
    ∀ t : Fin n, gateVal n C k (fun r => decide (r = t)) = false

private lemma flatMap_congr_left {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

private lemma getD_eq_getElem_of_lt {α : Type} {l : List α} {i : ℕ} {d : α} (hi : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

private lemma getD_of_length_le {α : Type} {l : List α} {i : ℕ} {d : α} (hi : l.length ≤ i) :
    l.getD i d = d := by
  have hnot : ¬ i < l.length := Nat.not_lt.mpr hi
  simp [List.getD_eq_getElem?_getD, hnot]

private lemma foldl_append_singleton_length {α β : Type} (step : List α → β → α)
    (gs : List β) (init : List α) :
    (gs.foldl (fun acc g => acc ++ [step acc g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma foldl_append_singleton_getD_lt {α β : Type} (step : List α → β → α)
    (gs : List β) (init : List α) (i : ℕ) (d : α) (hi : i < init.length) :
    (gs.foldl (fun acc g => acc ++ [step acc g]) init).getD i d = init.getD i d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (init ++ [step init g]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih (init ++ [step init g]) hi']
    rw [getD_eq_getElem_of_lt hi', getD_eq_getElem_of_lt hi, List.getElem_append_left hi]

private lemma foldl_append_singleton_pre_length {α β : Type} (step : List α → β → α)
    (gs : List β) (init : List α) {j : ℕ} (hj : j ≤ gs.length) :
    ((gs.take j).foldl (fun acc g => acc ++ [step acc g]) init).length = init.length + j := by
  rw [foldl_append_singleton_length, List.length_take_of_le hj]

private lemma foldl_append_singleton_pre_getD {α β : Type} (step : List α → β → α)
    (gs : List β) (init : List α) {j i : ℕ} (d : α) (hj : j ≤ gs.length)
    (hi : i < init.length + j) :
    ((gs.take j).foldl (fun acc g => acc ++ [step acc g]) init).getD i d =
      (gs.foldl (fun acc g => acc ++ [step acc g]) init).getD i d := by
  let pre := (gs.take j).foldl (fun acc g => acc ++ [step acc g]) init
  have hpre_len : pre.length = init.length + j := foldl_append_singleton_pre_length step gs init hj
  have hi' : i < pre.length := by omega
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  exact (foldl_append_singleton_getD_lt step (gs.drop j) pre i d hi').symm

private lemma foldl_append_singleton_getD_at {α β : Type} (step : List α → β → α)
    (gs : List β) (init : List α) {j : ℕ} (d : α) (hj : j < gs.length) :
    (gs.foldl (fun acc g => acc ++ [step acc g]) init).getD (init.length + j) d =
      step ((gs.take j).foldl (fun acc g => acc ++ [step acc g]) init) gs[j] := by
  let pre := (gs.take j).foldl (fun acc g => acc ++ [step acc g]) init
  have hpre_len : pre.length = init.length + j :=
    foldl_append_singleton_pre_length step gs init (Nat.le_of_lt hj)
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    rw [List.getElem_cons_drop hj, List.take_append_drop]
  have hi : init.length + j < (pre ++ [step pre gs[j]]).length := by
    simp only [List.length_append, List.length_singleton, hpre_len]
    omega
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_append_singleton_getD_lt step (gs.drop (j + 1)) (pre ++ [step pre gs[j]])
    (init.length + j) d hi]
  rw [getD_eq_getElem_of_lt hi]
  have hlen : pre.length ≤ init.length + j := by omega
  rw [List.getElem_append_right hlen]
  have hzero : init.length + j - pre.length = 0 := by omega
  simp [hzero, pre]

private lemma gateAt_eq_getElem (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  exact getD_eq_getElem_of_lt hj

private lemma gateAt_mem (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq_getElem C hj]
  exact List.getElem_mem hj

private lemma list_eq_two {α : Type} {l : List α} (hl : l.length = 2) :
    ∃ a b, l = [a, b] := by
  match l with
  | [a, b] => exact ⟨a, b, rfl⟩
  | [] => simp at hl
  | [_] => simp at hl
  | _ :: _ :: _ :: _ => simp only [List.length_cons] at hl; omega

private lemma ao2_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∃ a b : ℕ, (gateAt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j := by
  have hmem : gateAt C j ∈ C.gates := gateAt_mem C hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := hAO2.1 (gateAt C j) hmem
  have hlen : (gateAt C j).inputs.length = 2 := hAO2.2.2 (gateAt C j) hmem
  rcases list_eq_two hlen with ⟨a, b, hab⟩
  have ha : a < n + j := hAO2.2.1 j hj a (by rw [hab]; simp)
  have hb : b < n + j := hAO2.2.1 j hj b (by rw [hab]; simp)
  exact ⟨hop, a, b, hab, ha, hb⟩

private lemma wires_length (C : Circuit) {n : ℕ} (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  unfold Circuit.wires
  rw [foldl_append_singleton_length, List.length_ofFn]

private lemma wval_lt (C : Circuit) {n : ℕ} (x : Fin n → Bool) {w : ℕ} (hw : w < n) :
    wval C x w = x ⟨w, hw⟩ := by
  unfold wval Circuit.wires
  have hw' : w < (List.ofFn x).length := by rw [List.length_ofFn]; exact hw
  rw [foldl_append_singleton_getD_lt _ C.gates (List.ofFn x) w false hw']
  rw [getD_eq_getElem_of_lt hw', List.getElem_ofFn]

private lemma wval_ge (C : Circuit) {n : ℕ} (x : Fin n → Bool) {w : ℕ}
    (hw : n + C.gates.length ≤ w) : wval C x w = false := by
  unfold wval
  apply getD_of_length_le
  rw [wires_length]
  exact hw

private def wireStepTail (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private lemma wval_gate {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ}
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    wval C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hstep := foldl_append_singleton_getD_at wireStepTail C.gates (List.ofFn x) false hj
  rw [hlen] at hstep
  change (C.gates.foldl (fun w g => w ++ [wireStepTail w g]) (List.ofFn x)).getD (n + j) false = _
  rw [hstep, ← gateAt_eq_getElem C hj]
  unfold wireStepTail
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + j := hRB j hj i hi
  exact foldl_append_singleton_pre_getD wireStepTail C.gates (List.ofFn x) false
    (Nat.le_of_lt hj) (by rw [hlen]; exact hilt)

private lemma wval_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) {a b : ℕ} (hinps : (gateAt C j).inputs = [a, b])
    (x : Fin n → Bool) :
    wval C x (n + j) = true ↔ wval C x a = true ∨ wval C x b = true := by
  rw [wval_gate hAO2.2.1 hj x, hop, hinps]
  simp [GateOp.eval]

private lemma wval_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) {a b : ℕ} (hinps : (gateAt C j).inputs = [a, b])
    (x : Fin n → Bool) :
    wval C x (n + j) = true ↔ wval C x a = true ∧ wval C x b = true := by
  rw [wval_gate hAO2.2.1 hj x, hop, hinps]
  simp [GateOp.eval]

private def coneStepTail (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => (w - n) :: cs.getD (w - n) [])

private lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  conv_lhs => unfold cones coneStep
  change (C.gates.foldl (fun cs g => cs ++ [coneStepTail n cs g]) []).length = C.gates.length
  rw [foldl_append_singleton_length]
  simp

private lemma cones_step_eq (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  conv_lhs => unfold cones coneStep
  have hstep := foldl_append_singleton_getD_at (coneStepTail n) C.gates [] [] hj
  simp only [List.length_nil, Nat.zero_add] at hstep
  change (C.gates.foldl (fun cs g => cs ++ [coneStepTail n cs g]) []).getD j [] = _
  rw [hstep, ← gateAt_eq_getElem C hj]
  set pre := (C.gates.take j).foldl (fun cs g => cs ++ [coneStepTail n cs g]) []
  have hpre_len : pre.length = j := by
    simpa using foldl_append_singleton_pre_length (coneStepTail n) C.gates [] (Nat.le_of_lt hj)
  unfold coneStepTail
  rw [hpre_len]
  apply flatMap_congr_left
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hwlt : w - n < j := by omega
  have hpre : pre.getD (w - n) [] = (cones n C).getD (w - n) [] :=
    foldl_append_singleton_pre_getD (coneStepTail n) C.gates [] []
      (Nat.le_of_lt hj) (by simpa using hwlt)
  rw [hpre]

private lemma inCone_iff (n : ℕ) (C : Circuit) {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  rw [cones_step_eq n C hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩
    exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩
    exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

private lemma inCone_lt (n : ℕ) (C : Circuit) :
    ∀ j i : ℕ, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i hij
    by_cases hj : j < C.gates.length
    · rw [inCone_iff n C hj] at hij
      rcases hij with ⟨w, _, hnw, hwj, rfl | hrec⟩
      · exact ⟨by omega, hj⟩
      · have hwlt : w - n < j := by omega
        have hlt := (ih (w - n) hwlt i hrec).1
        exact ⟨by omega, hj⟩
    · exfalso
      unfold InCone at hij
      rw [getD_of_length_le (by rw [cones_length]; exact Nat.le_of_not_lt hj)] at hij
      simp at hij

private lemma inCone_trans (n : ℕ) (C : Circuit) :
    ∀ k i j : ℕ, InCone n C i j → InCone n C j k → InCone n C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro i j hij hjk
    have hk : k < C.gates.length := (inCone_lt n C k j hjk).2
    rw [inCone_iff n C hk] at hjk ⊢
    rcases hjk with ⟨w, hwin, hnw, hwk, rfl | hrec⟩
    · exact ⟨w, hwin, hnw, hwk, Or.inr hij⟩
    · have hwlt : w - n < k := by omega
      exact ⟨w, hwin, hnw, hwk, Or.inr (ih (w - n) hwlt i j hij hrec)⟩

private lemma inCone_of_input (n : ℕ) (C : Circuit) {j w : ℕ} (hj : j < C.gates.length)
    (hw : w ∈ (gateAt C j).inputs) (hnw : n ≤ w) (hwj : w < n + j) :
    InCone n C (w - n) j := by
  rw [inCone_iff n C hj]
  exact ⟨w, hw, hnw, hwj, Or.inl rfl⟩

private lemma inOutputCone_of_inCone (n : ℕ) (C : Circuit) {i j : ℕ}
    (hij : InCone n C i j) (hj : InOutputCone n C j) : InOutputCone n C i := by
  have hi_lt : i < j := (inCone_lt n C j i hij).1
  refine ⟨lt_trans hi_lt hj.1, ?_⟩
  rcases hj.2 with hout | ⟨hnout, hcone⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [hout, Nat.add_sub_cancel_left]
    exact hij
  · right
    exact ⟨hnout, inCone_trans n C (C.output - n) i j hij hcone⟩

private def orStepTail (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  cs.length :: match g.op with
    | GateOp.or =>
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
    | _ => []

private lemma orStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    orStep n cs g = cs ++ [orStepTail n cs g] := by
  unfold orStep orStepTail
  cases g.op <;> rfl

private lemma orSets_eq_foldl (n : ℕ) (C : Circuit) :
    orSets n C = C.gates.foldl (fun cs g => cs ++ [orStepTail n cs g]) [] := by
  unfold orSets
  have hgen : ∀ (gs : List Gate) (init : List (List ℕ)),
      gs.foldl (orStep n) init = gs.foldl (fun cs g => cs ++ [orStepTail n cs g]) init := by
    intro gs init
    induction gs generalizing init with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons, orStep_eq]
      exact ih (init ++ [orStepTail n init g])
  exact hgen C.gates []

private lemma orSets_step_eq (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    (orSets n C).getD j [] =
      j :: match (gateAt C j).op with
        | GateOp.or =>
          ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
            (fun w => (orSets n C).getD (w - n) [])
        | _ => [] := by
  conv_lhs => rw [orSets_eq_foldl n C]
  have hstep := foldl_append_singleton_getD_at (orStepTail n) C.gates [] [] hj
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [hstep, ← gateAt_eq_getElem C hj]
  set pre := (C.gates.take j).foldl (fun cs g => cs ++ [orStepTail n cs g]) []
  have hpre_len : pre.length = j := by
    simpa using foldl_append_singleton_pre_length (orStepTail n) C.gates [] (Nat.le_of_lt hj)
  unfold orStepTail
  rw [hpre_len]
  cases (gateAt C j).op with
  | or =>
    dsimp only
    congr 1
    apply flatMap_congr_left
    intro w hw
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    have hwlt : w - n < j := by omega
    have hpre : pre.getD (w - n) [] = (orSets n C).getD (w - n) [] := by
      conv_rhs => rw [orSets_eq_foldl n C]
      exact foldl_append_singleton_pre_getD (orStepTail n) C.gates [] []
        (Nat.le_of_lt hj) (by simpa using hwlt)
    rw [hpre]
  | and => rfl
  | not => rfl
  | mod _ => rfl
  | maj => rfl

private lemma orReaches_lt_false (n : ℕ) (C : Circuit) {w k : ℕ} (hw : w < n) :
    ¬ OrReaches n C w k := by
  intro h
  unfold OrReaches at h
  omega

private lemma orReaches_gate_iff (n : ℕ) (C : Circuit) {j k : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) k ↔
      k = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, w < n + j ∧ OrReaches n C w k) := by
  unfold OrReaches
  rw [Nat.add_sub_cancel_left, orSets_step_eq n C hj]
  simp only [Nat.le_add_right, true_and, List.mem_cons]
  constructor
  · rintro (rfl | hmem)
    · exact Or.inl rfl
    · right
      cases hop : (gateAt C j).op with
      | or =>
        rw [hop] at hmem
        simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hmem
        rcases hmem with ⟨w, ⟨hwin, hnw, hwj⟩, hk⟩
        exact ⟨rfl, w, hwin, hwj, hnw, hk⟩
      | and => rw [hop] at hmem; simp at hmem
      | not => rw [hop] at hmem; simp at hmem
      | mod _ => rw [hop] at hmem; simp at hmem
      | maj => rw [hop] at hmem; simp at hmem
  · rintro (rfl | ⟨hop, w, hwin, hwj, hnw, hk⟩)
    · exact Or.inl rfl
    · right
      rw [hop]
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
      exact ⟨w, ⟨hwin, hnw, hwj⟩, hk⟩

private lemma orReaches_and_iff (n : ℕ) (C : Circuit) {j k : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    OrReaches n C (n + j) k ↔ k = j := by
  rw [orReaches_gate_iff n C hj]
  constructor
  · rintro (rfl | ⟨hor, _⟩)
    · rfl
    · rw [hop] at hor; cases hor
  · exact fun h => Or.inl h

private lemma orReaches_or_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j k : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) {a b : ℕ}
    (hinps : (gateAt C j).inputs = [a, b]) :
    OrReaches n C (n + j) k ↔ k = j ∨ OrReaches n C a k ∨ OrReaches n C b k := by
  rw [orReaches_gate_iff n C hj, hop, hinps]
  have ha : a < n + j := hRB j hj a (by rw [hinps]; simp)
  have hb : b < n + j := hRB j hj b (by rw [hinps]; simp)
  constructor
  · rintro (rfl | ⟨_, w, hw, _, hreach⟩)
    · exact Or.inl rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Or.inr (Or.inl hreach)
      · exact Or.inr (Or.inr hreach)
  · rintro (rfl | hreach | hreach)
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, a, by simp, ha, hreach⟩
    · exact Or.inr ⟨rfl, b, by simp, hb, hreach⟩

private lemma orReaches_inCone (n : ℕ) (C : Circuit) :
    ∀ w Y : ℕ, w < n + C.gates.length → OrReaches n C w Y →
      n ≤ w ∧ (Y = w - n ∨ InCone n C Y (w - n)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro Y hwbnd hreach
    by_cases hw : w < n
    · exact False.elim (orReaches_lt_false n C hw hreach)
    · have hnw : n ≤ w := Nat.le_of_not_lt hw
      let i := w - n
      have hi : i < C.gates.length := by omega
      have hwi : w = n + i := by omega
      rw [hwi] at hreach
      rw [orReaches_gate_iff n C hi] at hreach
      refine ⟨hnw, ?_⟩
      rcases hreach with rfl | ⟨_, u, huin, hui, hureach⟩
      · exact Or.inl rfl
      · have hubnd : u < n + C.gates.length := by omega
        rcases ih u (by omega) Y hubnd hureach with ⟨hnu, rfl | hcone⟩
        · exact Or.inr (inCone_of_input n C hi huin hnu hui)
        · right
          have h1 : InCone n C (u - n) i := inCone_of_input n C hi huin hnu hui
          exact inCone_trans n C i Y (u - n) hcone h1

private lemma orReaches_cone_and_lt {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j w Y : ℕ}
    (hj : InOutputCone n C j) (hw : w ∈ (gateAt C j).inputs) (hreach : OrReaches n C w Y) :
    Y < j ∧ InOutputCone n C Y := by
  have hjlen : j < C.gates.length := hj.1
  have hwj : w < n + j := hRB j hjlen w hw
  have hwbnd : w < n + C.gates.length := by omega
  rcases orReaches_inCone n C w Y hwbnd hreach with ⟨hnw, hYeq | hcone⟩
  · have hYj : Y < j := by omega
    have hYcone : InCone n C Y j := by
      rw [hYeq]
      exact inCone_of_input n C hjlen hw hnw hwj
    exact ⟨hYj, inOutputCone_of_inCone n C hYcone hj⟩
  · have h1 : InCone n C (w - n) j := inCone_of_input n C hjlen hw hnw hwj
    have hYcone : InCone n C Y j := inCone_trans n C j Y (w - n) hcone h1
    have hYj : Y < j := (inCone_lt n C j Y hYcone).1
    exact ⟨hYj, inOutputCone_of_inCone n C hYcone hj⟩

private lemma orIn_lt_iff (n : ℕ) (C : Circuit) {w : ℕ} (hw : w < n) (t : Fin n) :
    t ∈ orIn n C w ↔ t.val = w := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, _, hreach, _⟩)
    · exact h
    · exact False.elim (orReaches_lt_false n C hw hreach)
  · exact fun h => Or.inl h

private lemma orIn_and_false (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (t : Fin n) :
    t ∉ orIn n C (n + j) := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rintro (ht | ⟨k, _, hreach, hkor, _⟩)
  · omega
  · rw [orReaches_and_iff n C hj hop] at hreach
    subst hreach
    rw [hop] at hkor
    cases hkor

private lemma orIn_or_iff {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) {a b : ℕ}
    (hinps : (gateAt C j).inputs = [a, b]) (t : Fin n) :
    t ∈ orIn n C (n + j) ↔ t ∈ orIn n C a ∨ t ∈ orIn n C b := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (ht | ⟨k, hk, hreach, hkor, htin⟩)
    · omega
    · rw [orReaches_or_iff hAO2.2.1 hj hop hinps] at hreach
      rcases hreach with rfl | ha | hb
      · rw [hinps] at htin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htin
        rcases htin with hta | htb
        · exact Or.inl (Or.inl hta)
        · exact Or.inr (Or.inl htb)
      · exact Or.inl (Or.inr ⟨k, hk, ha, hkor, htin⟩)
      · exact Or.inr (Or.inr ⟨k, hk, hb, hkor, htin⟩)
  · rintro ((hta | ⟨k, hk, ha, hkor, htin⟩) | (htb | ⟨k, hk, hb, hkor, htin⟩))
    · right
      refine ⟨j, hj, (orReaches_or_iff hAO2.2.1 hj hop hinps).mpr (Or.inl rfl), hop, ?_⟩
      rw [hinps, hta]
      simp
    · right
      exact ⟨k, hk, (orReaches_or_iff hAO2.2.1 hj hop hinps).mpr (Or.inr (Or.inl ha)), hkor, htin⟩
    · right
      refine ⟨j, hj, (orReaches_or_iff hAO2.2.1 hj hop hinps).mpr (Or.inl rfl), hop, ?_⟩
      rw [hinps, htb]
      simp
    · right
      exact ⟨k, hk, (orReaches_or_iff hAO2.2.1 hj hop hinps).mpr (Or.inr (Or.inr hb)), hkor, htin⟩

private lemma mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  by_cases hv : v ∈ A
  · rw [ite_eq_left hv]
    constructor
    · exact Or.inl
    · rintro (hx | rfl) <;> assumption
  · rw [ite_eq_right hv]
    simp

private lemma mem_foldl_insertNew (L B : List (List ℕ)) (x : List ℕ) :
    x ∈ L.foldl insertNew B ↔ x ∈ B ∨ x ∈ L := by
  induction L generalizing B with
  | nil => simp
  | cons v L ih =>
    simp only [List.foldl_cons, ih, mem_insertNew, List.mem_cons]
    tauto

private lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (vec : List ℕ) :
    vec ∈ andStep k A B ↔ ∃ p ∈ A, ∃ q ∈ B, vec = capAdd k p q := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨p, hp, q, hq, hEq⟩
    exact ⟨p, hp, q, hq, hEq.symm⟩
  · rintro ⟨p, hp, q, hq, hEq⟩
    exact ⟨p, hp, q, hq, hEq.symm⟩

private lemma rv_lt {n : ℕ} (C : Circuit) {u v : Fin n} (huv : u ≠ v) {w : ℕ} (hw : w < n) :
    rv C n u v w = if w = u.val then [[1, 0]] else if w = v.val then [[0, 1]] else [] := by
  conv_lhs => unfold rv readVectors
  have hlen : ((List.range n).map (leafVectors [u.val, v.val] 1)).length = n := by simp
  have hw' : w < ((List.range n).map (leafVectors [u.val, v.val] 1)).length := by omega
  rw [foldl_append_singleton_getD_lt _ C.gates _ w [] hw']
  rw [getD_eq_getElem_of_lt hw', List.getElem_map, List.getElem_range]
  unfold leafVectors
  have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
  by_cases hwu : w = u.val
  · rw [ite_eq_left hwu]
    have hmem : w ∈ [u.val, v.val] := by simp [hwu]
    rw [ite_eq_left hmem]
    simp [hwu, hne.symm]
  · rw [ite_eq_right hwu]
    by_cases hwv : w = v.val
    · rw [ite_eq_left hwv]
      have hmem : w ∈ [u.val, v.val] := by simp [hwv]
      rw [ite_eq_left hmem]
      simp [hwv, hne]
    · rw [ite_eq_right hwv]
      have hnotmem : w ∉ [u.val, v.val] := by simp [hwu, hwv]
      rw [ite_eq_right hnotmem]

private def rvStepTail (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) :
    List (List ℕ) :=
  let ins := g.inputs.map fun i => R.getD i []
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

private lemma rv_gate_step {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (u v : Fin n) {j : ℕ}
    (hj : j < C.gates.length) :
    rv C n u v (n + j) =
      let ins := (gateAt C j).inputs.map (rv C n u v)
      match (gateAt C j).op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep 1) [[0, 0]]
      | _ => [] := by
  conv_lhs => unfold rv readVectors
  have hlen : ((List.range n).map (leafVectors [u.val, v.val] 1)).length = n := by simp
  have hstep := foldl_append_singleton_getD_at (rvStepTail [u.val, v.val] 1)
    C.gates ((List.range n).map (leafVectors [u.val, v.val] 1)) [] hj
  rw [hlen] at hstep
  change (C.gates.foldl (fun R g => R ++ [rvStepTail [u.val, v.val] 1 R g])
    ((List.range n).map (leafVectors [u.val, v.val] 1))).getD (n + j) [] = _
  rw [hstep, ← gateAt_eq_getElem C hj]
  set pre := (C.gates.take j).foldl (fun R g => R ++ [rvStepTail [u.val, v.val] 1 R g])
    ((List.range n).map (leafVectors [u.val, v.val] 1))
  have hins :
      (gateAt C j).inputs.map (fun i => pre.getD i []) =
        (gateAt C j).inputs.map (rv C n u v) := by
    apply List.map_congr_left
    intro i hi
    have hilt : i < n + j := hRB j hj i hi
    exact foldl_append_singleton_pre_getD (rvStepTail [u.val, v.val] 1)
      C.gates ((List.range n).map (leafVectors [u.val, v.val] 1)) []
      (Nat.le_of_lt hj) (by rw [hlen]; exact hilt)
  unfold rvStepTail
  dsimp only
  rw [hins]
  have hzero : [([u.val, v.val].map (fun _ : ℕ => (0 : ℕ)))] = [[0, 0]] := rfl
  rw [hzero]

private lemma rv_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) {a b : ℕ}
    (hinps : (gateAt C j).inputs = [a, b]) (vec : List ℕ) :
    vec ∈ rv C n u v (n + j) ↔ vec ∈ rv C n u v a ∨ vec ∈ rv C n u v b := by
  rw [rv_gate_step hAO2.2.1 u v hj, hinps, hop]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_foldl_insertNew, mem_foldl_insertNew]
  simp

private lemma rv_and_raw {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) {a b : ℕ}
    (hinps : (gateAt C j).inputs = [a, b]) (vec : List ℕ) :
    vec ∈ rv C n u v (n + j) ↔
      ∃ p ∈ rv C n u v a, ∃ q ∈ rv C n u v b, vec = capAdd 1 (capAdd 1 [0, 0] p) q := by
  rw [rv_gate_step hAO2.2.1 u v hj, hinps, hop]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_andStep]
  constructor
  · rintro ⟨p', hp', q, hq, rfl⟩
    rw [mem_andStep] at hp'
    rcases hp' with ⟨z, hz, p, hp, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    subst hz
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    refine ⟨capAdd 1 [0, 0] p, ?_, q, hq, rfl⟩
    rw [mem_andStep]
    exact ⟨[0, 0], by simp, p, hp, rfl⟩

private lemma rv_shape {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {u v : Fin n} (huv : u ≠ v) :
    ∀ w < n + C.gates.length, ∀ vec ∈ rv C n u v w,
      ∃ a b : ℕ, vec = [a, b] ∧ a ≤ 2 ∧ b ≤ 2 ∧ (1 ≤ a ∨ 1 ≤ b) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwbnd vec hvec
    by_cases hw : w < n
    · rw [rv_lt C huv hw] at hvec
      by_cases hwu : w = u.val
      · rw [ite_eq_left hwu] at hvec
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hvec
        subst hvec
        exact ⟨1, 0, rfl, by omega, by omega, Or.inl (by omega)⟩
      · rw [ite_eq_right hwu] at hvec
        by_cases hwv : w = v.val
        · rw [ite_eq_left hwv] at hvec
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hvec
          subst hvec
          exact ⟨0, 1, rfl, by omega, by omega, Or.inr (by omega)⟩
        · rw [ite_eq_right hwv] at hvec
          simp at hvec
    · have hnw : n ≤ w := Nat.le_of_not_lt hw
      let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      rw [hwj] at hvec
      rcases ao2_gate hAO2 hj with ⟨hop | hop, a, b, hinps, ha, hb⟩
      · rw [rv_and_raw hAO2 u v hj hop hinps] at hvec
        rcases hvec with ⟨p, hp, q, hq, rfl⟩
        rcases ih a (by omega) (by omega) p hp with ⟨x1, y1, rfl, hx1, hy1, hpos1⟩
        rcases ih b (by omega) (by omega) q hq with ⟨x2, y2, rfl, hx2, hy2, hpos2⟩
        refine ⟨min (min (0 + x1) 2 + x2) 2, min (min (0 + y1) 2 + y2) 2,
          ?_, Nat.min_le_right _ 2, Nat.min_le_right _ 2, ?_⟩
        · simp [capAdd]
        · omega
      · rw [rv_or hAO2 u v hj hop hinps] at hvec
        rcases hvec with ha_mem | hb_mem
        · exact ih a (by omega) (by omega) vec ha_mem
        · exact ih b (by omega) (by omega) vec hb_mem

private lemma capAdd_zero_left {x y : ℕ} (hx : x ≤ 2) (hy : y ≤ 2) :
    capAdd 1 [0, 0] [x, y] = [x, y] := by
  simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil_left, Nat.zero_add]
  congr 1
  · exact Nat.min_eq_left hx
  · simp [Nat.min_eq_left hy]

private lemma rv_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {u v : Fin n} (huv : u ≠ v)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) {a b : ℕ}
    (hinps : (gateAt C j).inputs = [a, b]) (vec : List ℕ) :
    vec ∈ rv C n u v (n + j) ↔
      ∃ p ∈ rv C n u v a, ∃ q ∈ rv C n u v b, vec = capAdd 1 p q := by
  have ha : a < n + j := hAO2.2.1 j hj a (by rw [hinps]; simp)
  rw [rv_and_raw hAO2 u v hj hop hinps]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    rcases rv_shape hAO2 huv a (by omega) p hp with ⟨x, y, rfl, hx, hy, _⟩
    rw [capAdd_zero_left hx hy]
    exact ⟨[x, y], hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    rcases rv_shape hAO2 huv a (by omega) p hp with ⟨x, y, rfl, hx, hy, _⟩
    refine ⟨[x, y], hp, q, hq, ?_⟩
    rw [capAdd_zero_left hx hy]

private lemma orIn_iff_wval_unit {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    (hOneHot : OneHotOff n C) :
    ∀ w < n + C.gates.length, ∀ t : Fin n,
      (t ∈ orIn n C w ↔ wval C (fun r => decide (r = t)) w = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwbnd t
    by_cases hw : w < n
    · rw [orIn_lt_iff n C hw t, wval_lt C (fun r => decide (r = t)) hw]
      simp only [decide_eq_true_eq, Fin.ext_iff]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    · have hnw : n ≤ w := Nat.le_of_not_lt hw
      let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      rw [hwj]
      rcases ao2_gate hAO2 hj with ⟨hop | hop, a, b, hinps, ha, hb⟩
      · constructor
        · intro hmem
          exact False.elim (orIn_and_false n C hj hop t hmem)
        · intro hval
          have hfalse : gateVal n C j (fun r => decide (r = t)) = false := hOneHot j hj hop t
          change wval C (fun r => decide (r = t)) (n + j) = false at hfalse
          rw [hfalse] at hval
          cases hval
      · rw [orIn_or_iff hAO2 hj hop hinps t, wval_or hAO2 hj hop hinps]
        rw [ih a (by omega) (by omega) t, ih b (by omega) (by omega) t]

private lemma rv_unit_of_mem_orIn {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {u v : Fin n}
    (huv : u ≠ v) :
    ∀ w < n + C.gates.length,
      (u ∈ orIn n C w → [1, 0] ∈ rv C n u v w) ∧
      (v ∈ orIn n C w → [0, 1] ∈ rv C n u v w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwbnd
    by_cases hw : w < n
    · constructor
      · intro hu
        rw [orIn_lt_iff n C hw u] at hu
        rw [rv_lt C huv hw, ite_eq_left hu.symm]
        simp
      · intro hv
        rw [orIn_lt_iff n C hw v] at hv
        have hne : w ≠ u.val := by
          intro h
          apply huv
          exact Fin.ext (hv.trans h).symm
        rw [rv_lt C huv hw, ite_eq_right hne, ite_eq_left hv.symm]
        simp
    · have hnw : n ≤ w := Nat.le_of_not_lt hw
      let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      rw [hwj]
      rcases ao2_gate hAO2 hj with ⟨hop | hop, a, b, hinps, ha, hb⟩
      · constructor
        · intro hu
          exact False.elim (orIn_and_false n C hj hop u hu)
        · intro hv
          exact False.elim (orIn_and_false n C hj hop v hv)
      · constructor
        · intro hu
          rw [orIn_or_iff hAO2 hj hop hinps u] at hu
          rw [rv_or hAO2 u v hj hop hinps]
          rcases hu with hua | hub
          · exact Or.inl ((ih a (by omega) (by omega)).1 hua)
          · exact Or.inr ((ih b (by omega) (by omega)).1 hub)
        · intro hv
          rw [orIn_or_iff hAO2 hj hop hinps v] at hv
          rw [rv_or hAO2 u v hj hop hinps]
          rcases hv with hva | hvb
          · exact Or.inl ((ih a (by omega) (by omega)).2 hva)
          · exact Or.inr ((ih b (by omega) (by omega)).2 hvb)

private lemma mem_orIn_of_zero_rv {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {u v : Fin n}
    (huv : u ≠ v) (hOneHot : OneHotOff n C) :
    ∀ w < n + C.gates.length,
      ((∃ a : ℕ, [a, 0] ∈ rv C n u v w) → u ∈ orIn n C w) ∧
      ((∃ b : ℕ, [0, b] ∈ rv C n u v w) → v ∈ orIn n C w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwbnd
    by_cases hw : w < n
    · constructor
      · rintro ⟨a, ha⟩
        rw [rv_lt C huv hw] at ha
        by_cases hwu : w = u.val
        · rw [orIn_lt_iff n C hw u]
          exact hwu.symm
        · rw [ite_eq_right hwu] at ha
          by_cases hwv : w = v.val
          · rw [ite_eq_left hwv] at ha
            simp at ha
          · rw [ite_eq_right hwv] at ha
            simp at ha
      · rintro ⟨b, hb⟩
        rw [rv_lt C huv hw] at hb
        by_cases hwu : w = u.val
        · rw [ite_eq_left hwu] at hb
          simp at hb
        · rw [ite_eq_right hwu] at hb
          by_cases hwv : w = v.val
          · rw [orIn_lt_iff n C hw v]
            exact hwv.symm
          · rw [ite_eq_right hwv] at hb
            simp at hb
    · have hnw : n ≤ w := Nat.le_of_not_lt hw
      let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      rw [hwj]
      rcases ao2_gate hAO2 hj with ⟨hop | hop, p, q, hinps, hp, hq⟩
      · constructor
        · rintro ⟨a, ha⟩
          exfalso
          rw [rv_and hAO2 huv hj hop hinps] at ha
          rcases ha with ⟨vec1, hvec1, vec2, hvec2, hEq⟩
          rcases rv_shape hAO2 huv p (by omega) vec1 hvec1 with ⟨a1, b1, rfl, ha1, hb1, hpos1⟩
          rcases rv_shape hAO2 huv q (by omega) vec2 hvec2 with ⟨a2, b2, rfl, ha2, hb2, hpos2⟩
          simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons.injEq,
            and_true] at hEq
          have hbzero : b1 = 0 ∧ b2 = 0 := by omega
          rcases hbzero with ⟨rfl, rfl⟩
          have hu_p : u ∈ orIn n C p := (ih p (by omega) (by omega)).1 ⟨a1, hvec1⟩
          have hu_q : u ∈ orIn n C q := (ih q (by omega) (by omega)).1 ⟨a2, hvec2⟩
          have hwp : wval C (fun r => decide (r = u)) p = true :=
            (orIn_iff_wval_unit hAO2 hOneHot p (by omega) u).mp hu_p
          have hwq : wval C (fun r => decide (r = u)) q = true :=
            (orIn_iff_wval_unit hAO2 hOneHot q (by omega) u).mp hu_q
          have hwg : wval C (fun r => decide (r = u)) (n + j) = true :=
            (wval_and hAO2 hj hop hinps _).mpr ⟨hwp, hwq⟩
          have hfalse : gateVal n C j (fun r => decide (r = u)) = false := hOneHot j hj hop u
          change wval C (fun r => decide (r = u)) (n + j) = false at hfalse
          rw [hwg] at hfalse
          cases hfalse
        · rintro ⟨b, hb⟩
          exfalso
          rw [rv_and hAO2 huv hj hop hinps] at hb
          rcases hb with ⟨vec1, hvec1, vec2, hvec2, hEq⟩
          rcases rv_shape hAO2 huv p (by omega) vec1 hvec1 with ⟨a1, b1, rfl, ha1, hb1, hpos1⟩
          rcases rv_shape hAO2 huv q (by omega) vec2 hvec2 with ⟨a2, b2, rfl, ha2, hb2, hpos2⟩
          simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons.injEq,
            and_true] at hEq
          have hazero : a1 = 0 ∧ a2 = 0 := by omega
          rcases hazero with ⟨rfl, rfl⟩
          have hv_p : v ∈ orIn n C p := (ih p (by omega) (by omega)).2 ⟨b1, hvec1⟩
          have hv_q : v ∈ orIn n C q := (ih q (by omega) (by omega)).2 ⟨b2, hvec2⟩
          have hwp : wval C (fun r => decide (r = v)) p = true :=
            (orIn_iff_wval_unit hAO2 hOneHot p (by omega) v).mp hv_p
          have hwq : wval C (fun r => decide (r = v)) q = true :=
            (orIn_iff_wval_unit hAO2 hOneHot q (by omega) v).mp hv_q
          have hwg : wval C (fun r => decide (r = v)) (n + j) = true :=
            (wval_and hAO2 hj hop hinps _).mpr ⟨hwp, hwq⟩
          have hfalse : gateVal n C j (fun r => decide (r = v)) = false := hOneHot j hj hop v
          change wval C (fun r => decide (r = v)) (n + j) = false at hfalse
          rw [hwg] at hfalse
          cases hfalse
      · constructor
        · rintro ⟨a, ha⟩
          rw [rv_or hAO2 u v hj hop hinps] at ha
          rw [orIn_or_iff hAO2 hj hop hinps u]
          rcases ha with hap | haq
          · exact Or.inl ((ih p (by omega) (by omega)).1 ⟨a, hap⟩)
          · exact Or.inr ((ih q (by omega) (by omega)).1 ⟨a, haq⟩)
        · rintro ⟨b, hb⟩
          rw [rv_or hAO2 u v hj hop hinps] at hb
          rw [orIn_or_iff hAO2 hj hop hinps v]
          rcases hb with hbp | hbq
          · exact Or.inl ((ih p (by omega) (by omega)).2 ⟨b, hbp⟩)
          · exact Or.inr ((ih q (by omega) (by omega)).2 ⟨b, hbq⟩)

private lemma rv_pos_of_not_mem_orIn {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {u v : Fin n}
    (huv : u ≠ v) (hOneHot : OneHotOff n C) {w : ℕ} (hwbnd : w < n + C.gates.length)
    (hu : u ∉ orIn n C w) (hv : v ∉ orIn n C w) {vec : List ℕ} (hvec : vec ∈ rv C n u v w) :
    ∃ a b : ℕ, vec = [a, b] ∧ 1 ≤ a ∧ 1 ≤ b ∧ a ≤ 2 ∧ b ≤ 2 := by
  rcases rv_shape hAO2 huv w hwbnd vec hvec with ⟨a, b, rfl, ha2, hb2, _⟩
  have ha1 : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    subst ha0
    exact hv ((mem_orIn_of_zero_rv hAO2 huv hOneHot w hwbnd).2 ⟨b, hvec⟩)
  have hb1 : 1 ≤ b := by
    by_contra h
    have hb0 : b = 0 := by omega
    subst hb0
    exact hu ((mem_orIn_of_zero_rv hAO2 huv hOneHot w hwbnd).1 ⟨a, hvec⟩)
  exact ⟨a, b, rfl, ha1, hb1, ha2, hb2⟩

private lemma pure_or_descent {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) :
    ∀ w < n + C.gates.length, wval C (pairInput u v) w = true →
      u ∉ orIn n C w → v ∉ orIn n C w →
      ∃ Y < C.gates.length, OrReaches n C w Y ∧ (gateAt C Y).op = GateOp.and ∧
        gateVal n C Y (pairInput u v) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwbnd hval hu hv
    by_cases hw : w < n
    · exfalso
      rw [wval_lt C (pairInput u v) hw] at hval
      simp only [pairInput, decide_eq_true_eq, Fin.ext_iff] at hval
      rcases hval with hwu | hwv
      · exact hu ((orIn_lt_iff n C hw u).mpr hwu.symm)
      · exact hv ((orIn_lt_iff n C hw v).mpr hwv.symm)
    · have hnw : n ≤ w := Nat.le_of_not_lt hw
      let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      rw [hwj] at hval hu hv ⊢
      rcases ao2_gate hAO2 hj with ⟨hop | hop, a, b, hinps, ha, hb⟩
      · exact ⟨j, hj, (orReaches_and_iff n C hj hop).mpr rfl, hop, hval⟩
      · rw [wval_or hAO2 hj hop hinps] at hval
        rw [orIn_or_iff hAO2 hj hop hinps u] at hu
        rw [orIn_or_iff hAO2 hj hop hinps v] at hv
        rcases hval with ha_val | hb_val
        · have hu_a : u ∉ orIn n C a := fun h => hu (Or.inl h)
          have hv_a : v ∉ orIn n C a := fun h => hv (Or.inl h)
          rcases ih a (by omega) (by omega) ha_val hu_a hv_a with ⟨Y, hY, hreach, hYop, hYval⟩
          exact ⟨Y, hY, (orReaches_or_iff hAO2.2.1 hj hop hinps).mpr (Or.inr (Or.inl hreach)),
            hYop, hYval⟩
        · have hu_b : u ∉ orIn n C b := fun h => hu (Or.inr h)
          have hv_b : v ∉ orIn n C b := fun h => hv (Or.inr h)
          rcases ih b (by omega) (by omega) hb_val hu_b hv_b with ⟨Y, hY, hreach, hYop, hYval⟩
          exact ⟨Y, hY, (orReaches_or_iff hAO2.2.1 hj hop hinps).mpr (Or.inr (Or.inr hreach)),
            hYop, hYval⟩

private lemma readTwiceAt_iff (n : ℕ) (C : Circuit) (j : ℕ) (u v : Fin n) :
    ReadTwiceAt n C j u v ↔
      ∀ vec ∈ rv C n u v (n + j), vec.all (fun a => decide (a ≤ 1)) = false := by
  unfold ReadTwiceAt readsAtMost atGate rv
  change ((readVectors C n [u.val, v.val] 1).getD (n + j) []).any
    (fun vec => vec.all fun a => decide (a ≤ 1)) = false ↔ _
  rw [List.any_eq_false]
  simp

private lemma readTwiceAt_not_mem_10 {n : ℕ} {C : Circuit} {j : ℕ} {u v : Fin n}
    (hRT : ReadTwiceAt n C j u v) : [1, 0] ∉ rv C n u v (n + j) := by
  intro hmem
  have h := (readTwiceAt_iff n C j u v).mp hRT [1, 0] hmem
  simp at h

private lemma readTwiceAt_not_mem_01 {n : ℕ} {C : Circuit} {j : ℕ} {u v : Fin n}
    (hRT : ReadTwiceAt n C j u v) : [0, 1] ∉ rv C n u v (n + j) := by
  intro hmem
  have h := (readTwiceAt_iff n C j u v).mp hRT [0, 1] hmem
  simp at h

private lemma readTwiceAt_not_mem_11 {n : ℕ} {C : Circuit} {j : ℕ} {u v : Fin n}
    (hRT : ReadTwiceAt n C j u v) : [1, 1] ∉ rv C n u v (n + j) := by
  intro hmem
  have h := (readTwiceAt_iff n C j u v).mp hRT [1, 1] hmem
  simp at h

private lemma and_branch_with_endpoint {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    {u v : Fin n} (huv : u ≠ v) (hOneHot : OneHotOff n C)
    {g A Q : ℕ} {z w : Fin n}
    (hg : g < C.gates.length)
    (hCone : InOutputCone n C g)
    (hop : (gateAt C g).op = GateOp.and)
    (hinps : (gateAt C g).inputs = [A, Q] ∨ (gateAt C g).inputs = [Q, A])
    (hzw : (z = u ∧ w = v) ∨ (z = v ∧ w = u))
    (hzA : z ∈ orIn n C A)
    (huQ : u ∉ orIn n C Q)
    (hvQ : v ∉ orIn n C Q)
    (hvalQ : wval C (pairInput u v) Q = true)
    (hih : ∀ g' < g, g' < C.gates.length → InOutputCone n C g' →
      gateVal n C g' (pairInput u v) = true → ReadTwiceAt n C g' u v → Goal n C u v) :
    Goal n C u v := by
  have hQin : Q ∈ (gateAt C g).inputs := by
    rcases hinps with h | h <;> rw [h] <;> simp
  have hQlt : Q < n + g := hAO2.2.1 g hg Q hQin
  rcases pure_or_descent hAO2 u v Q (by omega) hvalQ huQ hvQ with
    ⟨Y, hYlen, hOrQY, hYop, hYval⟩
  rcases orReaches_cone_and_lt hAO2.2.1 hCone hQin hOrQY with ⟨hYg, hYCone⟩
  rcases ao2_gate hAO2 hYlen with ⟨_, P, N, hYinps, hP, hN⟩
  have hNotSame : ∀ t : Fin n, ¬ (t ∈ orIn n C P ∧ t ∈ orIn n C N) := by
    intro t ⟨htP, htN⟩
    have h1 : wval C (fun r => decide (r = t)) P = true :=
      (orIn_iff_wval_unit hAO2 hOneHot P (by omega) t).mp htP
    have h2 : wval C (fun r => decide (r = t)) N = true :=
      (orIn_iff_wval_unit hAO2 hOneHot N (by omega) t).mp htN
    have h3 : wval C (fun r => decide (r = t)) (n + Y) = true :=
      (wval_and hAO2 hYlen hYop hYinps _).mpr ⟨h1, h2⟩
    have h4 : gateVal n C Y (fun r => decide (r = t)) = false := hOneHot Y hYlen hYop t
    change wval C (fun r => decide (r = t)) (n + Y) = false at h4
    rw [h3] at h4
    cases h4
  have hRT_of_clean_left : u ∉ orIn n C P → v ∉ orIn n C P → ReadTwiceAt n C Y u v := by
    intro huP hvP
    rw [readTwiceAt_iff]
    intro vec hvec
    rw [rv_and hAO2 huv hYlen hYop hYinps] at hvec
    rcases hvec with ⟨p, hp, q, hq, rfl⟩
    rcases rv_pos_of_not_mem_orIn hAO2 huv hOneHot (by omega) huP hvP hp with
      ⟨a1, b1, rfl, ha1, hb1, _, _⟩
    rcases rv_shape hAO2 huv N (by omega) q hq with ⟨a2, b2, rfl, _, _, hpos2⟩
    simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil_left, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
    rcases hpos2 with ha2 | hb2
    · left; omega
    · right; omega
  have hRT_of_clean_right : u ∉ orIn n C N → v ∉ orIn n C N → ReadTwiceAt n C Y u v := by
    intro huN hvN
    rw [readTwiceAt_iff]
    intro vec hvec
    rw [rv_and hAO2 huv hYlen hYop hYinps] at hvec
    rcases hvec with ⟨p, hp, q, hq, rfl⟩
    rcases rv_shape hAO2 huv P (by omega) p hp with ⟨a1, b1, rfl, _, _, hpos1⟩
    rcases rv_pos_of_not_mem_orIn hAO2 huv hOneHot (by omega) huN hvN hq with
      ⟨a2, b2, rfl, ha2, hb2, _, _⟩
    simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil_left, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
    rcases hpos1 with ha1 | hb1
    · left; omega
    · right; omega
  by_cases hzP : z ∈ orIn n C P
  · by_cases hwN : w ∈ orIn n C N
    · exact Or.inl ⟨g, hg, Y, hYlen, A, Q, P, N, z, w, hCone, hop, hinps, hYop,
        Or.inl hYinps, hOrQY, hzw, hzA, hzP, hwN⟩
    · by_cases hzN : z ∈ orIn n C N
      · exact False.elim (hNotSame z ⟨hzP, hzN⟩)
      · have huN : u ∉ orIn n C N := by
          rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hvN : v ∉ orIn n C N := by
          rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        exact hih Y hYg hYlen hYCone hYval (hRT_of_clean_right huN hvN)
  · by_cases hwP : w ∈ orIn n C P
    · by_cases hzN : z ∈ orIn n C N
      · exact Or.inl ⟨g, hg, Y, hYlen, A, Q, N, P, z, w, hCone, hop, hinps, hYop,
          Or.inr hYinps, hOrQY, hzw, hzA, hzN, hwP⟩
      · by_cases hwN : w ∈ orIn n C N
        · exact False.elim (hNotSame w ⟨hwP, hwN⟩)
        · have huN : u ∉ orIn n C N := by
            rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
          have hvN : v ∉ orIn n C N := by
            rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
          exact hih Y hYg hYlen hYCone hYval (hRT_of_clean_right huN hvN)
    · have huP : u ∉ orIn n C P := by
        rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hvP : v ∉ orIn n C P := by
        rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      by_cases huN : u ∈ orIn n C N
      · exact hih Y hYg hYlen hYCone hYval (hRT_of_clean_left huP hvP)
      · by_cases hvN : v ∈ orIn n C N
        · exact hih Y hYg hYlen hYCone hYval (hRT_of_clean_left huP hvP)
        · exact Or.inr ⟨Y, hYlen, P, N, hYCone, hYop, hYinps, hYval, huP, hvP, huN, hvN⟩

private lemma descent_from_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    {u v : Fin n} (huv : u ≠ v) (hOneHot : OneHotOff n C) :
    ∀ g < C.gates.length, InOutputCone n C g →
      gateVal n C g (pairInput u v) = true → ReadTwiceAt n C g u v → Goal n C u v := by
  intro g
  induction g using Nat.strong_induction_on with
  | ind g ih =>
    intro hg hCone hVal hRT
    have hu_g : u ∉ orIn n C (n + g) := fun hu =>
      readTwiceAt_not_mem_10 hRT ((rv_unit_of_mem_orIn hAO2 huv (n + g) (by omega)).1 hu)
    have hv_g : v ∉ orIn n C (n + g) := fun hv =>
      readTwiceAt_not_mem_01 hRT ((rv_unit_of_mem_orIn hAO2 huv (n + g) (by omega)).2 hv)
    rcases ao2_gate hAO2 hg with ⟨hop | hop, L, M, hinps, hL, hM⟩
    · have hVal' : wval C (pairInput u v) (n + g) = true := hVal
      rw [wval_and hAO2 hg hop hinps] at hVal'
      rcases hVal' with ⟨hvalL, hvalM⟩
      have hNotBothU : ¬ (u ∈ orIn n C L ∧ u ∈ orIn n C M) := by
        rintro ⟨huL, huM⟩
        have h1 : wval C (fun r => decide (r = u)) L = true :=
          (orIn_iff_wval_unit hAO2 hOneHot L (by omega) u).mp huL
        have h2 : wval C (fun r => decide (r = u)) M = true :=
          (orIn_iff_wval_unit hAO2 hOneHot M (by omega) u).mp huM
        have h3 : wval C (fun r => decide (r = u)) (n + g) = true :=
          (wval_and hAO2 hg hop hinps _).mpr ⟨h1, h2⟩
        have h4 : gateVal n C g (fun r => decide (r = u)) = false := hOneHot g hg hop u
        change wval C (fun r => decide (r = u)) (n + g) = false at h4
        rw [h3] at h4
        cases h4
      have hNotBothV : ¬ (v ∈ orIn n C L ∧ v ∈ orIn n C M) := by
        rintro ⟨hvL, hvM⟩
        have h1 : wval C (fun r => decide (r = v)) L = true :=
          (orIn_iff_wval_unit hAO2 hOneHot L (by omega) v).mp hvL
        have h2 : wval C (fun r => decide (r = v)) M = true :=
          (orIn_iff_wval_unit hAO2 hOneHot M (by omega) v).mp hvM
        have h3 : wval C (fun r => decide (r = v)) (n + g) = true :=
          (wval_and hAO2 hg hop hinps _).mpr ⟨h1, h2⟩
        have h4 : gateVal n C g (fun r => decide (r = v)) = false := hOneHot g hg hop v
        change wval C (fun r => decide (r = v)) (n + g) = false at h4
        rw [h3] at h4
        cases h4
      have hNotCrossUV : ¬ (u ∈ orIn n C L ∧ v ∈ orIn n C M) := by
        rintro ⟨huL, hvM⟩
        have hp : [1, 0] ∈ rv C n u v L := (rv_unit_of_mem_orIn hAO2 huv L (by omega)).1 huL
        have hq : [0, 1] ∈ rv C n u v M := (rv_unit_of_mem_orIn hAO2 huv M (by omega)).2 hvM
        have h11 : [1, 1] ∈ rv C n u v (n + g) := by
          rw [rv_and hAO2 huv hg hop hinps]
          exact ⟨[1, 0], hp, [0, 1], hq, by simp [capAdd]⟩
        exact readTwiceAt_not_mem_11 hRT h11
      have hNotCrossVU : ¬ (v ∈ orIn n C L ∧ u ∈ orIn n C M) := by
        rintro ⟨hvL, huM⟩
        have hp : [0, 1] ∈ rv C n u v L := (rv_unit_of_mem_orIn hAO2 huv L (by omega)).2 hvL
        have hq : [1, 0] ∈ rv C n u v M := (rv_unit_of_mem_orIn hAO2 huv M (by omega)).1 huM
        have h11 : [1, 1] ∈ rv C n u v (n + g) := by
          rw [rv_and hAO2 huv hg hop hinps]
          exact ⟨[0, 1], hp, [1, 0], hq, by simp [capAdd]⟩
        exact readTwiceAt_not_mem_11 hRT h11
      by_cases huL : u ∈ orIn n C L
      · have huM : u ∉ orIn n C M := fun h => hNotBothU ⟨huL, h⟩
        have hvM : v ∉ orIn n C M := fun h => hNotCrossUV ⟨huL, h⟩
        exact and_branch_with_endpoint hAO2 huv hOneHot hg hCone hop (Or.inl hinps)
          (Or.inl ⟨rfl, rfl⟩) huL huM hvM hvalM ih
      · by_cases hvL : v ∈ orIn n C L
        · have hvM : v ∉ orIn n C M := fun h => hNotBothV ⟨hvL, h⟩
          have huM : u ∉ orIn n C M := fun h => hNotCrossVU ⟨hvL, h⟩
          exact and_branch_with_endpoint hAO2 huv hOneHot hg hCone hop (Or.inl hinps)
            (Or.inr ⟨rfl, rfl⟩) hvL huM hvM hvalM ih
        · by_cases huM : u ∈ orIn n C M
          · exact and_branch_with_endpoint hAO2 huv hOneHot hg hCone hop (Or.inr hinps)
              (Or.inl ⟨rfl, rfl⟩) huM huL hvL hvalL ih
          · by_cases hvM : v ∈ orIn n C M
            · exact and_branch_with_endpoint hAO2 huv hOneHot hg hCone hop (Or.inr hinps)
                (Or.inr ⟨rfl, rfl⟩) hvM huL hvL hvalL ih
            · exact Or.inr ⟨g, hg, L, M, hCone, hop, hinps, hVal, huL, hvL, huM, hvM⟩
    · have hVal' : wval C (pairInput u v) (n + g) = true := hVal
      rw [wval_or hAO2 hg hop hinps] at hVal'
      rw [orIn_or_iff hAO2 hg hop hinps u] at hu_g
      rw [orIn_or_iff hAO2 hg hop hinps v] at hv_g
      have hStep : ∀ c : ℕ, c ∈ (gateAt C g).inputs → c < n + g →
          wval C (pairInput u v) c = true → u ∉ orIn n C c → v ∉ orIn n C c →
          (∀ vec ∈ rv C n u v c, vec ∈ rv C n u v (n + g)) → Goal n C u v := by
        intro c hcin hclt hcval huc hvc hsub
        have hnc : n ≤ c := by
          by_contra hlt
          have hcn : c < n := Nat.lt_of_not_le hlt
          rw [wval_lt C (pairInput u v) hcn] at hcval
          simp only [pairInput, decide_eq_true_eq, Fin.ext_iff] at hcval
          rcases hcval with hcu | hcv
          · exact huc ((orIn_lt_iff n C hcn u).mpr hcu.symm)
          · exact hvc ((orIn_lt_iff n C hcn v).mpr hcv.symm)
        let g' := c - n
        have hg'lt : g' < g := by omega
        have hcg' : c = n + g' := by omega
        have hg'len : g' < C.gates.length := lt_trans hg'lt hg
        have hg'cone : InOutputCone n C g' :=
          inOutputCone_of_inCone n C (inCone_of_input n C hg hcin hnc hclt) hCone
        have hg'val : gateVal n C g' (pairInput u v) = true := by
          change wval C (pairInput u v) (n + g') = true
          rw [← hcg']
          exact hcval
        have hg'RT : ReadTwiceAt n C g' u v := by
          rw [readTwiceAt_iff]
          intro vec hvec
          rw [← hcg'] at hvec
          exact (readTwiceAt_iff n C g u v).mp hRT vec (hsub vec hvec)
        exact ih g' hg'lt hg'len hg'cone hg'val hg'RT
      rcases hVal' with hvalL | hvalM
      · exact hStep L (by rw [hinps]; simp) hL hvalL (fun h => hu_g (Or.inl h))
          (fun h => hv_g (Or.inl h)) (fun vec h => (rv_or hAO2 u v hg hop hinps vec).mpr (Or.inl h))
      · exact hStep M (by rw [hinps]; simp) hM hvalM (fun h => hu_g (Or.inr h))
          (fun h => hv_g (Or.inr h)) (fun vec h => (rv_or hAO2 u v hg hop hinps vec).mpr (Or.inr h))

private lemma main_proof (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (hFun : circuitFun n C = graphFun G ∅) (hOneHot : OneHotOff n C)
    (u v : Fin n) (o : ℕ) (hAdj : G.Adj u v) (hOut : C.output = n + o)
    (hRT : ReadTwiceAt n C o u v) : Goal n C u v := by
  have huv : u ≠ v := G.ne_of_adj hAdj
  have hgf : graphFun G ∅ (pairInput u v) = true := by
    unfold graphFun pairInput
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    exact ⟨u, v, hAdj, Or.inl rfl, Or.inr rfl⟩
  have hcf : circuitFun n C (pairInput u v) = true := by
    rw [hFun]
    exact hgf
  have hval : wval C (pairInput u v) (n + o) = true := by
    change (C.wires (List.ofFn (pairInput u v))).getD (n + o) false = true
    rw [← hOut]
    exact hcf
  have ho_lt : o < C.gates.length := by
    by_contra hnot
    have hge : n + C.gates.length ≤ n + o := by omega
    rw [wval_ge C (pairInput u v) hge] at hval
    cases hval
  have ho_cone : InOutputCone n C o := ⟨ho_lt, Or.inl hOut⟩
  exact descent_from_gate hAO2 huv hOneHot o ho_lt ho_cone hval hRT

end PEqualNP.Outside.L_meta_3756

theorem PEqualNP.Outside.L_meta_3756 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (fun r => decide (r = t)) = false) → ∀ (u v : Fin n) (o : ℕ), G.Adj u v → C.output = n + o → PEqualNP.Core.ReadTwiceAt n C o u v → (∃ X < C.gates.length, ∃ Y < C.gates.length, ∃ (A Q P N : ℕ) (z w : Fin n), PEqualNP.Core.InOutputCone n C X ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C X).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C X).inputs = [A, Q] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C X).inputs = [Q, A]) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C Y).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C Y).inputs = [P, N] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C Y).inputs = [N, P]) ∧ PEqualNP.CleanedNonEdge.OrReaches n C Q Y ∧ ((z = u ∧ w = v) ∨ (z = v ∧ w = u)) ∧ z ∈ PEqualNP.TopForm.orIn n C A ∧ z ∈ PEqualNP.TopForm.orIn n C P ∧ w ∈ PEqualNP.TopForm.orIn n C N) ∨ (∃ W < C.gates.length, ∃ L M : ℕ, PEqualNP.Core.InOutputCone n C W ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C W).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C W).inputs = [L, M] ∧ PEqualNP.EdgeOwnership.gateVal n C W (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ u ∉ PEqualNP.TopForm.orIn n C L ∧ v ∉ PEqualNP.TopForm.orIn n C L ∧ u ∉ PEqualNP.TopForm.orIn n C M ∧ v ∉ PEqualNP.TopForm.orIn n C M) := by
  exact PEqualNP.Outside.L_meta_3756.main_proof
