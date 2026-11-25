import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.CoverPromise

-- The wire and trace arguments follow the checked proofs in L_meta_4183.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4500000 in
theorem PEqualNP.Outside.R_meta_4185_631
    (singleScarce : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ j, junk G C = {j} →
      let U := Ustar G C
      let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      let T := (tops G C \ centreless G C).card
      let S := Finset.univ.filter fun v : Fin n => gateVal n C j (pairInput v v) = true
      U.Nonempty → B < U.card + (if S.card = 0 then 2 else if S.card = 1 then 3 else 1) →
      ∃ K : Finset (Fin n), IsVertexCover G K ∧ K.card + U.card ≤ T + B)
    (multipleJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      2 ≤ (junk G C).card →
      let U := Ustar G C
      let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      let T := (tops G C \ centreless G C).card
      U.Nonempty → B < 2 * U.card →
      ∃ K : Finset (Fin n), IsVertexCover G K ∧ K.card + U.card ≤ T + B) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∃ (x9 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x9 ∧ x9.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    exact List.getD_eq_getElem _ _ hj

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

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    change ((gateAt C r).inputs.map fun i => if i < n + r then val C x i else false).any id = true ↔ _
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [if_neg hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

  have val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
      val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    change ((gateAt C r).inputs.map fun i => if i < n + r then val C x i else false).all id = true ↔ _
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
      · rw [if_neg hlt] at h'; cases h'
    · intro h i hi
      rw [if_pos (h i hi).1]; exact (h i hi).2

  have val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
      val C (List.ofFn x) u.val = x u := by
    rw [val_input (n := n) (by simp) u.isLt]
    simp [List.getD_eq_getElem?_getD]

  let OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
    ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
      w' ∈ (gateAt C k).inputs ∧ w' < n + k

  have orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
      val C x w = true := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact hv
    | head hstep _ ih =>
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

  have or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
      ∀ w : ℕ, val C x w = true →
        ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
          (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hv
      by_cases hw : w < n
      · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
      · by_cases hlen : n + C.gates.length ≤ w
        · rw [val_ge hx hlen] at hv; cases hv
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < C.gates.length := by omega
          by_cases hop : (gateAt C k).op = GateOp.or
          · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
            obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
            exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
          · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

  have pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
    change decide (u = u ∨ u = v) = true
    exact decide_eq_true (Or.inl rfl)

  have pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
    change decide (v = u ∨ v = v) = true
    exact decide_eq_true (Or.inr rfl)

  have pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
    change decide (w = u ∨ w = v) = true ↔ w = u ∨ w = v
    exact ⟨of_decide_eq_true, decide_eq_true⟩

  have graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
      graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), pairInput u v a = true) ||
      decide (∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true)) = true ↔ _
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, pairInput_true]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (G.irrefl hab).elim
      · exact hab
      · exact hab.symm
      · exact (G.irrefl hab).elim
    · intro h
      exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

  have operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
      (hv : val C (List.ofFn (pairInput u v)) p = true) :
      (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
      (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
        Relation.ReflTransGen (OrStep n C) p (n + h) ∧
        val C (List.ofFn (pairInput u v)) (n + h) = true) := by
    obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
      (by simp) p hv
    rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
    · left
      refine ⟨⟨w', hlt⟩, ?_, hr⟩
      have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
      rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
      exact (pairInput_true u v _).mp h1.symm
    · right
      exact ⟨h, hh, hop, hr, hv'⟩

  have reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
      (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
      val C (List.ofFn x) p = true :=
    orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

  have side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
      (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
      (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
      (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
      (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
      (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
      (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
    apply hF
    apply hbel
    rw [val_and (n := n) (by simp) ha hop, hin]
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
    · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

  have edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
      (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
      (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
      (u v : Fin n) (huv : F (pairInput u v) = true) :
      ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
        Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
        val C (List.ofFn (pairInput u v)) (n + a) = true := by
    rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
      ⟨t, _, hr⟩ | h
    · exfalso
      have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
      rw [hout] at h1
      exact G.irrefl (hF t t h1)
    · exact h

  have below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
      (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
      (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
      (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
    rw [← hout]
    exact orStep_up (n := n) (by simp) hr hv

  have coneStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) : coneStep n cs g =
      cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := rfl

  have cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [coneStep_eq]
      omega

  have cones_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
        rw [cones_len]; simp
      have key : ∀ k, k < gs.length →
          (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
            (gs.foldl (coneStep n) []).getD k [] := by
        intro k hk
        simp only [↓coneStep_eq, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)] at h3
          exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          simp only [↓coneStep_eq, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [e2, e1]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - n) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
          simp only [↓coneStep_eq, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩
          simp at h0
          omega

  have inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
      InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
        (i = k ∨ InCone n C i k) := by
    have h := cones_char n C.gates i j
    unfold InCone cones gateAt
    rw [h]
    constructor
    · rintro ⟨h0, w, hw, h1, h2, h3⟩
      refine ⟨h0, w - n, by omega, ?_, h3⟩
      have : n + (w - n) = w := by omega
      rw [this]
      exact hw
    · rintro ⟨h0, k, hk, hw, h3⟩
      refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
      have : n + k - n = k := by omega
      rw [this]
      exact h3

  have orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact le_rfl
    | head hstep _ ih =>
      obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
      omega

  have orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) w w') :
      ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => intro k h' h1 h2; left; omega
    | @head a c hstep hrest ih =>
      intro k h' h1 h2
      obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
      have hk : k0 = k := by omega
      subst hk
      have hle := orStep_le hrest
      obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
      subst hk1
      right
      rw [inCone_iff]
      exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

  have operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
      (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
      (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
    have hle := orStep_le hr
    obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
    rw [inCone_iff]
    exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

  letI : DecidableEq GateOp := gateOpDecEq
  have orStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) : orStep n cs g =
      cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) []) else [])] := rfl

  have orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [orStep_eq]
      omega

  have orSets_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep n) []).length = gs.length := by
        rw [orSets_len]; simp
      have key : ∀ k, k < gs.length →
          (orStep n (gs.foldl (orStep n) []) g).getD k [] =
            (gs.foldl (orStep n) []).getD k [] := by
        intro k hk
        simp only [↓orStep_eq, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, h3⟩
          refine ⟨by simp; omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3⟩
          refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
            simp only [↓orStep_eq, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen, hop]
          rw [e2]
          simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp, Or.inl h3⟩
            · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - n) (by omega)]
              exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - n) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
            simp only [↓orStep_eq, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen, hop]
          rw [e2]
          simp only [List.mem_singleton]
          constructor
          · intro h3
            exact ⟨by simp, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
          simp only [↓orStep_eq, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩
          simp at h0
          omega

  have orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
      OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
    have h := orSets_char n C.gates g k
    unfold OrReaches orSets gateAt
    have e : n + k - n = k := by omega
    rw [e, h]
    constructor
    · rintro ⟨_, hk, h3⟩
      refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
    · rintro ⟨hk, h3⟩
      refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

  have reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) w w2) :
      ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro g h1 hg
      subst h1
      exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
    | @head a c hstep hrest ih =>
      intro g h1 hg
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

  have orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
      ∀ w, OrReaches n C w g →
        Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h
      have hnw : n ≤ w := h.1
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
      rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
      · exact ⟨Relation.ReflTransGen.refl, hk⟩
      · obtain ⟨hr2, hg⟩ := ih i hlt hr
        exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

  have orIn_mem {n : ℕ} (C : Circuit) (p : ℕ) (u : Fin n) : u ∈ orIn n C p ↔
      u.val = p ∨ ∃ k < C.gates.length, OrReaches n C p k ∧
        (gateAt C k).op = GateOp.or ∧ u.val ∈ (gateAt C k).inputs := by
    change u ∈ @Finset.filter (Fin n) _ _ Finset.univ ↔ _
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)]

  have mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
      Relation.ReflTransGen (OrStep n C) p u.val := by
    rw [orIn_mem] at hu
    rcases hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

  have reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
      u ∈ PEqualNP.TopForm.orIn n C p := by
    rw [orIn_mem]
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
      exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

  have top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (h4 : NoFourCycle G) (hL : IsLeastAO G C) (a : ℕ) (ha : a ∈ tops G C) :
      Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
      (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
      ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
    obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
    obtain ⟨hlen, hop, hbel⟩ := Finset.mem_filter.mp ha
    have halen := Finset.mem_range.mp hlen
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
    have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
    have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
    have e0 : opnd C a 0 = p := by
      change (gateAt C a).inputs.getD 0 0 = p
      rw [hin] <;> rfl
    have e1 : opnd C a 1 = q := by
      change (gateAt C a).inputs.getD 1 0 = q
      rw [hin] <;> rfl
    have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
      intro u hu v hv
      change u ∈ orIn n C (opnd C a 0) at hu
      change v ∈ orIn n C (opnd C a 1) at hv
      rw [e0] at hu
      rw [e1] at hv
      exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
        p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
    refine ⟨?_, hadj, ?_⟩
    · rw [Finset.disjoint_left]
      intro u hu hv
      exact G.irrefl (hadj u hu u hv)
    · by_contra hcon
      simp only [not_or, not_le] at hcon
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
      have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hadj x hx w hw, hadj y hy w hw⟩
      have h5 := Finset.card_le_card hsub
      have h6 := h4 x y hxy
      omega

  have off_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C) (u v : Fin n)
      (huv : s(u, v) ∈ Ustar G C) :
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal n C a (pairInput u v) = true ∧
        OrReaches n C (opnd C a b) h ∧
        gateVal n C h (pairInput u v) = true := by
    obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
    obtain ⟨he, hns⟩ := Finset.mem_sdiff.mp huv
    have hadj := SimpleGraph.mem_edgeFinset.mp he
    have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
      fun u v h => (graphFun_pair G u v).mp h
    have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
      fun x => congrFun hfun x
    obtain ⟨a, halen, hnor, hreach, hval⟩ :=
      edge_trace G (graphFun G ∅) hF hout u v ((graphFun_pair G u v).mpr hadj)
    have hop : (gateAt C a).op = GateOp.and := by
      rcases hAO _ (gateAt_mem halen) with h | h
      · exact h
      · exact (hnor h).elim
    have hbel : BelowF G C a := fun x hx => below_of_reach (graphFun G ∅) hout a hreach x hx
    have hatop : a ∈ tops G C :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr halen, hop, hbel⟩
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
    have e0 : opnd C a 0 = p := by
      change (gateAt C a).inputs.getD 0 0 = p
      rw [hin] <;> rfl
    have e1 : opnd C a 1 = q := by
      change (gateAt C a).inputs.getD 1 0 = q
      rw [hin] <;> rfl
    have hpq := (val_and (n := n) (by simp) halen hop).mp hval
    have hp := hpq p (by rw [hin]; simp)
    have hq := hpq q (by rw [hin]; simp)
    have junk_of : ∀ (w : ℕ) (b : Fin 2), opnd C a b = w → w ∈ (gateAt C a).inputs → w < n + a →
        ∀ h, h < C.gates.length → (gateAt C h).op ≠ GateOp.or →
        Relation.ReflTransGen (OrStep n C) w (n + h) →
        val C (List.ofFn (pairInput u v)) (n + h) = true →
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
          gateVal n C a (pairInput u v) = true ∧
          OrReaches n C (opnd C a b) h ∧
          gateVal n C h (pairInput u v) = true := by
      intro w b hb hwin hwlt h hh hhor hr hv
      have hhand : (gateAt C h).op = GateOp.and := by
        rcases hAO _ (gateAt_mem hh) with h3 | h3
        · exact h3
        · exact (hhor h3).elim
      have hcone : InCone n C h a := operand_cone halen hwin hwlt hr
      have hnb : ¬ BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
      have hdirty : IsDirtyAnd n G C h := by
        unfold IsDirtyAnd IsDirty
        refine ⟨hhand, hh, ?_⟩
        by_contra hne
        apply hnb
        intro x hx
        by_contra hfx
        exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
      have hjunk : h ∈ junk G C :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
      refine ⟨a, hatop, b, h, hjunk, hval, ?_, hv⟩
      rw [hb]
      exact reach_orReaches hr h rfl hh
    rcases operand_trace (C := C) u v p hp.2 with ⟨t1, ht1, hr1⟩ | ⟨h, hh, hhor, hr, hv⟩
    · rcases operand_trace (C := C) u v q hq.2 with ⟨t2, ht2, hr2⟩ | ⟨h, hh, hhor, hr, hv⟩
      · exfalso
        apply hns
        have hadj12 : G.Adj t1 t2 :=
          side_adj G (graphFun G ∅) hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
        have hne : t1 ≠ t2 := G.ne_of_adj hadj12
        have hs : s(u, v) = s(t1, t2) := by
          rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
          · exact (hne (h1.trans h2.symm)).elim
          · rw [h1, h2]
          · rw [h1, h2]; exact Sym2.eq_swap
          · exact (hne (h1.trans h2.symm)).elim
        rw [hs]
        apply Finset.mem_biUnion.mpr
        refine ⟨a, hatop, Finset.mem_image.mpr ⟨(t1, t2), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩⟩
        · change t1 ∈ orIn n C (opnd C a 0)
          rw [e0]
          exact reach_mem_orIn t1 hr1
        · change t2 ∈ orIn n C (opnd C a 1)
          rw [e1]
          exact reach_mem_orIn t2 hr2
      · exact junk_of q 1 e1 (by rw [hin]; simp) hq.1 h hh hhor hr hv
    · exact junk_of p 0 e0 (by rw [hin]; simp) hp.1 h hh hhor hr hv

  intro n G _ C hFour hNonempty hLeast hTop
  classical
  obtain ⟨hAO, hBack, hTwo⟩ := hLeast.1
  let U := Ustar G C
  let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  let topsWithInputs := tops G C \ centreless G C
  let T := topsWithInputs.card

  have smallSide (P Q : Finset (Fin n)) (adj : ∀ u ∈ P, ∀ v ∈ Q, G.Adj u v) :
      P.card ≤ 1 ∨ Q.card ≤ 1 := by
    by_contra h
    push Not at h
    obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.mp h.1
    have hSub : Q ⊆ Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj u' w) := by
      intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, adj u hu w hw, adj u' hu' w hw⟩
    exact (not_le_of_gt h.2) ((Finset.card_le_card hSub).trans (hFour u u' hne))

  have starCenter : ∀ a ∈ topsWithInputs, ∃ c : Fin n,
      ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, c = u ∨ c = v := by
    intro a ha
    obtain ⟨ha, hnc⟩ := Finset.mem_sdiff.mp ha
    have h0 : (side (n := n) C a 0).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr
        (fun h => hnc (Finset.mem_filter.mpr ⟨ha, Or.inl h⟩))
    have h1 : (side (n := n) C a 1).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr
        (fun h => hnc (Finset.mem_filter.mpr ⟨ha, Or.inr h⟩))
    rcases (top_facts G C hFour hLeast a ha).2.2 with hs | hs
    · obtain ⟨c, hc⟩ := h0
      exact ⟨c, fun u hu _ _ => Or.inl (Finset.card_le_one.mp hs c hc u hu)⟩
    · obtain ⟨c, hc⟩ := h1
      exact ⟨c, fun _ _ v hv => Or.inr (Finset.card_le_one.mp hs c hc v hv)⟩
  let center (a : {a // a ∈ topsWithInputs}) : Fin n :=
    Classical.choose (starCenter a.val a.property)
  let centers := topsWithInputs.attach.image center
  have centersCard : centers.card ≤ T := by
    simpa only [centers, T, Finset.card_attach] using
      (Finset.card_image_le (s := topsWithInputs.attach) (f := center))
  have centersCover (e : Sym2 (Fin n)) (he : e ∈ starEdges G C) :
      ∃ v ∈ centers, v ∈ e := by
    obtain ⟨a, ha, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    have hnc : a ∉ centreless G C := by
      intro h
      rcases (Finset.mem_filter.mp h).2 with h0 | h1
      · rw [h0] at hu
        simp at hu
      · rw [h1] at hv
        simp at hv
    let tag : {a // a ∈ topsWithInputs} := ⟨a, Finset.mem_sdiff.mpr ⟨ha, hnc⟩⟩
    refine ⟨center tag, Finset.mem_image.mpr ⟨tag, Finset.mem_attach _ _, rfl⟩, ?_⟩
    exact Sym2.mem_iff.mpr (Classical.choose_spec (starCenter tag.val tag.property) u hu v hv)

  have finish (K : Finset (Fin n)) (hK : ∀ e ∈ U, ∃ v ∈ K, v ∈ e)
      (hCost : K.card + U.card ≤ B) :
      ∃ X : Finset (Fin n), IsVertexCover G X ∧ X.card + U.card ≤ T + B := by
    refine ⟨centers ∪ K, ?_, ?_⟩
    · intro u v huv
      have covered : ∃ w ∈ centers ∪ K, w ∈ s(u,v) := by
        by_cases he : s(u,v) ∈ starEdges G C
        · obtain ⟨w,hw,hedge⟩ := centersCover _ he
          exact ⟨w, Finset.mem_union_left _ hw, hedge⟩
        · obtain ⟨w,hw,hedge⟩ := hK _ (Finset.mem_sdiff.mpr
              ⟨SimpleGraph.mem_edgeFinset.mpr huv, he⟩)
          exact ⟨w, Finset.mem_union_right _ hw, hedge⟩
      obtain ⟨w,hw,hedge⟩ := covered
      rcases Sym2.mem_iff.mp hedge with rfl | rfl
      · exact Or.inl hw
      · exact Or.inr hw
    · have hUnion := Finset.card_union_le centers K
      omega

  have canPayTwo (hCost : 2 * U.card ≤ B) :
      ∃ X : Finset (Fin n), IsVertexCover G X ∧ X.card + U.card ≤ T + B := by
    have chooseEndpoint : ∀ e : Sym2 (Fin n), ∃ v : Fin n, v ∈ e :=
      fun e => Sym2.ind (fun u v => ⟨u, Sym2.mem_iff.mpr (Or.inl rfl)⟩) e
    let pick (e : Sym2 (Fin n)) := Classical.choose (chooseEndpoint e)
    apply finish (U.image pick)
    · intro e he
      exact ⟨pick e, Finset.mem_image_of_mem pick he, Classical.choose_spec (chooseEndpoint e)⟩
    · have hCard : (U.image pick).card ≤ U.card := Finset.card_image_le
      omega
  change ∃ X : Finset (Fin n), IsVertexCover G X ∧ X.card + U.card ≤
    T + 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  suffices hFinal : ∃ X : Finset (Fin n), IsVertexCover G X ∧ X.card + U.card ≤ T + B by
    obtain ⟨X, cover, hSize⟩ := hFinal
    refine ⟨X, cover, ?_⟩
    calc
      X.card + U.card ≤ T + B := hSize
      _ = _ := by
        change T + (_ + _ + _) = _
        rw [← Nat.add_assoc, ← Nat.add_assoc]
  by_cases twoPaid : 2 * U.card ≤ B
  · exact canPayTwo twoPaid
  have hU : U.Nonempty := Finset.card_pos.mp (by omega)
  have hJ : (junk G C).Nonempty := by
    obtain ⟨e, he⟩ := hU
    revert he
    refine Sym2.ind (fun u v he => ?_) e
    obtain ⟨_, _, _, j, hj, _⟩ := off_star G C hLeast hTop u v he
    exact ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hJ
  by_cases onlyJ : junk G C = {j}
  rotate_left
  · have many : 2 ≤ (junk G C).card := by
      by_contra h
      have hsmall : (junk G C).card ≤ 1 := by omega
      apply onlyJ
      apply Finset.ext
      intro k
      exact ⟨fun hk => Finset.mem_singleton.mpr (Finset.card_le_one.mp hsmall k hk j hj),
        fun hk => (Finset.mem_singleton.mp hk).symm ▸ hj⟩
    exact multipleJunk n G C hFour hNonempty hLeast hTop many hU (show B < 2 * U.card from Nat.lt_of_not_ge twoPaid)

  let singletons := Finset.univ.filter fun v : Fin n => gateVal n C j (pairInput v v) = true
  let allowance := if singletons.card = 0 then 2 else if singletons.card = 1 then 3 else 1
  by_cases enough : U.card + allowance ≤ B
  rotate_left
  · exact singleScarce n G C hFour hNonempty hLeast hTop j onlyJ hU
      (show B < U.card + allowance from Nat.lt_of_not_ge enough)

  have eqJ (k : ℕ) (hk : k ∈ junk G C) : k = j := by
    exact Finset.mem_singleton.mp (onlyJ ▸ hk)
  have jInfo : j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false := by
    obtain ⟨hjLen, hjDirty⟩ := Finset.mem_filter.mp hj
    exact ⟨Finset.mem_range.mp hjLen, hjDirty.1, hjDirty.2.2⟩
  have inputPair {a : ℕ} (ha : a < C.gates.length) :
      (gateAt C a).inputs = [opnd C a 0, opnd C a 1] := by
    obtain ⟨p,q,h⟩ := List.length_eq_two.mp (hTwo _ (gateAt_mem ha))
    change (gateAt C a).inputs = [(gateAt C a).inputs.getD 0 0, (gateAt C a).inputs.getD 1 0]
    rw [h] <;> rfl
  have inputMem {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
      opnd C a b ∈ (gateAt C a).inputs := by
    rw [inputPair ha]
    fin_cases b <;> simp
  have inputBack {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
      opnd C a b < n + a := hBack a ha _ (inputMem ha b)
  have andEval {a : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
      (x : Fin n → Bool) :
      gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
    change val C (List.ofFn x) (n + a) = true ↔ _
    rw [val_and (n := n) (by simp) ha hop]
    constructor
    · exact fun h b => (h _ (inputMem ha b)).2
    · intro h i hi
      refine ⟨hBack _ ha _ hi, ?_⟩
      rw [inputPair ha] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact h 0
      · exact h 1

  have nestedJunk {a k p : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
      (hm : p ∈ (gateAt C a).inputs) (hlt : p < n + a) (hk : k < C.gates.length)
      (hnor : (gateAt C k).op ≠ GateOp.or) (hr : Relation.ReflTransGen (OrStep n C) p (n+k)) :
      k ∈ junk G C := by
    have hand := (hAO _ (gateAt_mem hk)).resolve_right hnor
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hk, hand, hk, ?_⟩
    by_contra h
    have hbel : BelowF G C k := by
      intro x hv
      by_contra hn
      exact h ⟨x, hv, Bool.eq_false_iff.mpr hn⟩
    exact hTop k hk a ha hand hbel hop (operand_cone ha hm hlt hr)

  let A := side (n := n) C j 0
  let D := side (n := n) C j 1
  have evalJ (x : Fin n → Bool) :
      gateVal n C j x = true ↔ (∃ u ∈ A, x u = true) ∧ (∃ v ∈ D, x v = true) := by
    rw [andEval jInfo.1 jInfo.2.1 x]
    constructor
    · intro h
      have witness (b : Fin 2) : ∃ u ∈ side C j b, x u = true := by
        obtain ⟨w, hr, hv, hw⟩ := or_trace (n := n) (C := C) (x := List.ofFn x) (by simp) _ (h b)
        rcases hw with hw | ⟨k,hk,rfl,hnor⟩
        · refine ⟨⟨w,hw⟩, reach_mem_orIn ⟨w,hw⟩ hr, ?_⟩
          simpa only [val_ofFn C x ⟨w,hw⟩] using hv
        · have hkj := eqJ k (nestedJunk jInfo.1 jInfo.2.1 (inputMem jInfo.1 b)
              (inputBack jInfo.1 b) hk hnor hr)
          have hle := orStep_le hr
          have hlt := inputBack jInfo.1 b
          omega
      exact ⟨witness 0, witness 1⟩
    · rintro ⟨⟨u,hu,hxu⟩, ⟨v,hv,hxv⟩⟩ b
      fin_cases b
      · exact reach_var_val x _ u (mem_orIn_reach u hu) hxu
      · exact reach_var_val x _ v (mem_orIn_reach v hv) hxv

  let opposite := Finset.univ.filter fun u : Fin n =>
    ∃ a ∈ tops G C, ∃ b : Fin 2, OrReaches n C (opnd C a b) j ∧ u ∈ side C a (1-b)
  have forces {u : Fin n} (hu : u ∈ opposite) (x : Fin n → Bool)
      (hxu : x u = true) (hjx : gateVal n C j x = true) : graphFun G ∅ x = true := by
    obtain ⟨a,ha,b,hr,hus⟩ := (Finset.mem_filter.mp hu).2
    obtain ⟨hLen, hAnd, hBelow⟩ := Finset.mem_filter.mp ha
    apply hBelow
    apply (andEval (Finset.mem_range.mp hLen) hAnd _).mpr
    have jside : val C (List.ofFn x) (opnd C a b) = true :=
      orStep_up (n := n) (by simp) (orReaches_reach j _ hr).1 hjx
    have oside : val C (List.ofFn x) (opnd C a (1-b)) = true :=
      reach_var_val x _ u (mem_orIn_reach u hus) hxu
    intro b'
    fin_cases b <;> fin_cases b' <;> first
    | exact jside
    | exact oside

  have reversePair (u v : Fin n) : pairInput u v = pairInput v u := by
    funext w
    change decide (w = u ∨ w = v) = decide (w = v ∨ w = u)
    by_cases h : w = u ∨ w = v
    · rw [decide_eq_true h, decide_eq_true (or_comm.mp h)]
    · rw [decide_eq_false h, decide_eq_false (fun hOpp => h (or_comm.mp hOpp))]
  have residualTrace : ∀ e ∈ U, ∃ u v : Fin n, e = s(u,v) ∧ u ∈ opposite ∧
      gateVal n C j (pairInput u v) = true := by
    intro e
    refine Sym2.ind (fun u v he => ?_) e
    obtain ⟨a,ha,b,k,hk,hax,hr,hkx⟩ := off_star G C hLeast hTop u v he
    have hkj := eqJ k hk
    subst k
    obtain ⟨hLen, hAnd, hBelow⟩ := Finset.mem_filter.mp ha
    have hTopInfo := Finset.mem_range.mp hLen
    have hOther := (andEval hTopInfo hAnd (pairInput u v)).mp hax (1-b)
    rcases operand_trace u v (opnd C a (1-b)) hOther with ⟨t,ht,htreach⟩ | ⟨k,hk,hnor,hkr,_⟩
    · have htOpp : t ∈ opposite := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, a,ha,b,hr,reach_mem_orIn t htreach⟩
      rcases ht with htu | htv
      · exact ⟨u,v,rfl,htu ▸ htOpp,hkx⟩
      · exact ⟨v,u,Sym2.eq_swap,htv ▸ htOpp,by rw [← reversePair u v]; exact hkx⟩
    · have hkJ := eqJ k (nestedJunk hTopInfo hAnd
          (inputMem hTopInfo (1-b)) (inputBack hTopInfo (1-b)) hk hnor hkr)
      subst k
      obtain ⟨x,hjx,hFx⟩ := jInfo.2.2
      have hLeft : val C (List.ofFn x) (opnd C a b) = true :=
        orStep_up (n := n) (by simp) (orReaches_reach j _ hr).1 hjx
      have hRight : val C (List.ofFn x) (opnd C a (1-b)) = true :=
        orStep_up (n := n) (by simp) hkr hjx
      have hTrue : graphFun G ∅ x = true := by
        apply hBelow
        apply (andEval hTopInfo hAnd _).mpr
        intro b'
        fin_cases b <;> fin_cases b' <;> first
        | exact hLeft
        | exact hRight
      rw [hFx] at hTrue
      contradiction

  have singleIff (v : Fin n) : v ∈ singletons ↔ v ∈ A ∧ v ∈ D := by
    simp only [singletons, Finset.mem_filter, Finset.mem_univ, true_and, evalJ, pairInput_true]
    simp
  have crossAD {u v : Fin n} (hu : u ∈ A) (hv : v ∈ D) :
      gateVal n C j (pairInput u v) = true :=
    (evalJ _).mpr ⟨⟨u,hu,pairInput_left _ _⟩, ⟨v,hv,pairInput_right _ _⟩⟩
  have crossS (u : Fin n) (hu : u ∈ opposite) (v : Fin n) (hv : v ∈ singletons) :
      G.Adj u v := by
    obtain ⟨ha,hd⟩ := (singleIff v).mp hv
    have hvj : gateVal n C j (pairInput u v) = true :=
      (evalJ _).mpr ⟨⟨v,ha,pairInput_right _ _⟩,⟨v,hd,pairInput_right _ _⟩⟩
    exact (graphFun_pair G u v).mp (forces hu _ (pairInput_left _ _) hvj)
  have crossLeft (u : Fin n) (hu : u ∈ opposite ∩ A) (v : Fin n) (hv : v ∈ D) :
      G.Adj u v := by
    obtain ⟨ho,ha⟩ := Finset.mem_inter.mp hu
    exact (graphFun_pair G u v).mp (forces ho _ (pairInput_left _ _) (crossAD ha hv))
  have crossRight (u : Fin n) (hu : u ∈ opposite ∩ D) (v : Fin n) (hv : v ∈ A) :
      G.Adj u v := by
    obtain ⟨ho,hd⟩ := Finset.mem_inter.mp hu
    have hvj := crossAD hv hd
    rw [reversePair v u] at hvj
    exact (graphFun_pair G u v).mp (forces ho _ (pairInput_left _ _) hvj)

  have coverCross (P Q : Finset (Fin n)) (adj : ∀ u ∈ P, ∀ v ∈ Q, G.Adj u v) :
      ∃ K : Finset (Fin n), K.card ≤ 1 ∧ ∀ u ∈ P, ∀ v ∈ Q, u ∈ K ∨ v ∈ K := by
    rcases smallSide P Q adj with hl | hr
    · exact ⟨P, hl, fun _ hu _ _ => Or.inl hu⟩
    · exact ⟨Q, hr, fun _ _ _ hv => Or.inr hv⟩
  by_cases hLarge : 1 < singletons.card
  · have hSmall := (smallSide opposite singletons crossS).resolve_right (not_le_of_gt hLarge)
    apply finish opposite
    · intro e he
      obtain ⟨u,v,rfl,hu,_⟩ := residualTrace e he
      exact ⟨u,hu,Sym2.mem_iff.mpr (Or.inl rfl)⟩
    · have hOne : allowance = 1 := by
        simp only [allowance]
        split_ifs <;> omega
      omega
  obtain ⟨Kleft,kleft,coverLeft⟩ := coverCross (opposite ∩ A) D crossLeft
  obtain ⟨Kright,kright,coverRight⟩ := coverCross (opposite ∩ D) A crossRight
  let K := singletons ∪ (Kleft ∪ Kright)
  apply finish K
  · intro e he
    obtain ⟨u,v,rfl,hu,hjv⟩ := residualTrace e he
    have hNot : u ∉ singletons := fun hu' => G.irrefl (crossS u hu u hu')
    have hEither : u ∈ K ∨ v ∈ K := by
      obtain ⟨⟨p,hp,hpx⟩,⟨q,hq,hqx⟩⟩ := (evalJ _).mp hjv
      rcases (pairInput_true u v p).mp hpx with hpu | hpv <;>
        rcases (pairInput_true u v q).mp hqx with hqu | hqv
      · exact (hNot ((singleIff u).mpr ⟨hpu ▸ hp,hqu ▸ hq⟩)).elim
      · rcases coverLeft u (Finset.mem_inter.mpr ⟨hu,hpu ▸ hp⟩) v (hqv ▸ hq) with hk | hk
        · exact Or.inl (Finset.mem_union_right _ (Finset.mem_union_left _ hk))
        · exact Or.inr (Finset.mem_union_right _ (Finset.mem_union_left _ hk))
      · rcases coverRight u (Finset.mem_inter.mpr ⟨hu,hqu ▸ hq⟩) v (hpv ▸ hp) with hk | hk
        · exact Or.inl (Finset.mem_union_right _ (Finset.mem_union_right _ hk))
        · exact Or.inr (Finset.mem_union_right _ (Finset.mem_union_right _ hk))
      · exact Or.inr (Finset.mem_union_left _ ((singleIff v).mpr ⟨hpv ▸ hp,hqv ▸ hq⟩))
    rcases hEither with hk | hk
    · exact ⟨u,hk,Sym2.mem_iff.mpr (Or.inl rfl)⟩
    · exact ⟨v,hk,Sym2.mem_iff.mpr (Or.inr rfl)⟩
  · have hk := Finset.card_union_le singletons (Kleft ∪ Kright)
    have hklr := Finset.card_union_le Kleft Kright
    have hAllowance : singletons.card + 2 = allowance := by
      simp only [allowance]
      split_ifs <;> omega
    dsimp only [K]
    omega
