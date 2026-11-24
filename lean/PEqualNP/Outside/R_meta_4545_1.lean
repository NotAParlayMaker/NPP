import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- The proof pays one uncovered edge twice by following its OR path from a top to a junk AND.
-- The two hypotheses concern larger uncovered sets, split by a common endpoint.
-- The wire-tracing lemmas below are adapted from the checked L_meta_1490 proof.
set_option maxHeartbeats 3200000 in
theorem PEqualNP.Outside.R_meta_4545_1
    (star : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      (∀ D, IsLeastAO G D → TopForm G D → (Ustar G C).card ≤ (Ustar G D).card) →
      (∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) →
      (∀ v, (G.neighborSet v).ncard ≠ 1) →
      let U := Ustar G C
      2 ≤ U.card → ∀ z, (∀ e ∈ U, z ∈ e) →
      ∃ K : Finset (Fin n), (∀ e ∈ G.edgeFinset \ U, ∃ v ∈ K, v ∈ e) ∧
        (z ∈ K ∨ ∀ v, s(z,v) ∈ U → v ∈ K) ∧ U.card + K.card ≤ (tops G C \ centreless G C).card + 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
    (separate : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      (∀ D, IsLeastAO G D → TopForm G D → (Ustar G C).card ≤ (Ustar G D).card) →
      (∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) →
      (∀ v, (G.neighborSet v).ncard ≠ 1) →
      let U := Ustar G C
      (∃ e ∈ U, ∃ f ∈ U, ∀ v ∈ e, v ∉ f) →
      ∀ R : Finset (Sym2 (Fin n)), R ⊆ U →
      (∀ e ∈ R, ∀ f ∈ R, e ≠ f → ∀ v ∈ e, v ∉ f) →
      ∃ K : Finset (Fin n),
        (∀ e ∈ G.edgeFinset \ U, (∀ v ∈ e, ∀ r ∈ R, v ∉ r) → ∃ v ∈ K, v ∈ e) ∧
        U.card + R.card + K.card ≤ (tops G C \ centreless G C).card + 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Fin x1 × Fin x1)), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x10 → PEqualNP.TopForm.TopForm x2 x10 → (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.Ustar x2 x10).card) → (∃ (x11 : Fin x1 → Bool), ∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x11 x12 ≠ x11 x13) → (∀ (x12 : Fin x1), (x2.neighborSet x12).ncard ≠ (1 : ℕ)) → (∀ x13 ∈ x5, x2.Adj x13.1 x13.2) → (∀ x14 ∈ x5, ∀ x16 ∈ x5, x14.1 = x16.1 → x14 = x16) → (∀ x15 ∈ x5, ∀ x17 ∈ x5, x15.2 = x17.2 → x15 = x17) → (∀ x16 ∈ x5, ∀ x18 ∈ x5, x16.1 ≠ x18.2) → (PEqualNP.TopForm.Ustar x2 x4).card + x5.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  let _ : DecidableEq GateOp := gateOpDecEq
  have andDef (l : List Bool) : GateOp.eval .and l = l.all id := rfl
  have orDef (l : List Bool) : GateOp.eval .or l = l.any id := rfl
  have gateDef (C : Circuit) (j : ℕ) : gateAt C j = C.gates.getD j ⟨.or, []⟩ := rfl
  have coneDef (n : ℕ) (cs : List (List ℕ)) (g : Gate) : coneStep n cs g =
      cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := rfl
  have orStepDef (n : ℕ) (cs : List (List ℕ)) (g : Gate) : orStep n cs g =
      cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) []) else [])] := rfl
  have graphDef {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
      (x : Fin n → Bool) : graphFun K A x =
        (decide (∃ a ∈ A, x a = true) || decide (∃ u v, K.Adj u v ∧ x u = true ∧ x v = true)) := rfl
  have pairDef {n : ℕ} (u v w : Fin n) : pairInput u v w = decide (w = u ∨ w = v) := rfl
  have opndDef (C : Circuit) (j : ℕ) (b : Fin 2) :
      opnd C j b = (gateAt C j).inputs.getD b.val 0 := rfl
  have sideDef {n : ℕ} (C : Circuit) (j : ℕ) (b : Fin 2) :
      side (n := n) C j b = orIn n C (opnd C j b) := rfl
  have orInDef (n : ℕ) (C : Circuit) (w : ℕ) : orIn n C w = Finset.univ.filter
      (fun i : Fin n => i.val = w ∨ ∃ k < C.gates.length,
       OrReaches n C w k ∧ (gateAt C k).op = .or ∧ i.val ∈ (gateAt C k).inputs) := rfl
  have topMem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :
      j ∈ tops G C ↔ j < C.gates.length ∧ (gateAt C j).op = .and ∧ BelowF G C j := by
    change j ∈ (Finset.range _).filter _ ↔ _
    rw [Finset.mem_filter, Finset.mem_range]
  have orNMem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :
      j ∈ orN G C ↔ j < C.gates.length ∧ (gateAt C j).op = .or ∧ ¬ BelowF G C j := by
    change j ∈ (Finset.range _).filter _ ↔ _
    rw [Finset.mem_filter, Finset.mem_range]
  have Udef {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
      Ustar G C = G.edgeFinset \ starEdges G C := rfl
  have starsDef {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
      starEdges G C = (tops G C).biUnion (fun a => (side C a 0 ×ˢ side C a 1).image
        fun p : Fin n × Fin n => s(p.1,p.2)) := rfl
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
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
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

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    simp [gateDef, List.getD_eq_getElem?_getD, hj]

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
    · simp only [andDef, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro h1 i hi; exact h i hi (h1 i hi)
    · simp only [orDef, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp only [orDef, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
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
    simp only [andDef, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
      · rw [ite_eq_right hlt] at h'; cases h'
    · intro h i hi
      rw [ite_eq_left (h i hi).1]; exact (h i hi).2

  have biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
      (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
      (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
      A.card ≤ 1 ∨ B.card ≤ 1 := by
    by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
    obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
    exact h4 a b c d hac hbd
      ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

  have val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
      val C (List.ofFn x) u.val = x u := by
    rw [val_input (n := n) (by simp) u.isLt]
    simp [List.getD_eq_getElem?_getD]

  have gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
      PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

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
    simp [pairDef]

  have pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
    simp [pairDef]

  have pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
    simp [pairDef]

  have graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
      graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    rw [graphDef]
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


  have cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [coneDef]
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
        simp only [coneDef, List.getD_eq_getElem?_getD]
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
          simp only [coneDef, List.getD_eq_getElem?_getD]
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
          simp only [coneDef, List.getD_eq_getElem?_getD]
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


  have orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [orStepDef]
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
        simp only [orStepDef, List.getD_eq_getElem?_getD]
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
            simp only [orStepDef, List.getD_eq_getElem?_getD]
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
            simp only [orStepDef, List.getD_eq_getElem?_getD]
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
          simp only [orStepDef, List.getD_eq_getElem?_getD]
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

  have mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
      Relation.ReflTransGen (OrStep n C) p u.val := by
    simp only [orInDef, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rcases hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

  have reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
      u ∈ PEqualNP.TopForm.orIn n C p := by
    simp only [orInDef, Finset.mem_filter, Finset.mem_univ, true_and]
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
    rw [topMem] at ha
    obtain ⟨halen, hop, hbel⟩ := ha
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
    have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
    have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
    have e0 : opnd C a 0 = p := by simp [opndDef, hin]
    have e1 : opnd C a 1 = q := by simp [opndDef, hin]
    have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
      intro u hu v hv
      simp only [sideDef, e0] at hu
      simp only [sideDef, e1] at hv
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
    rw [Udef, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
    obtain ⟨hadj, hns⟩ := huv
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
    have hatop : a ∈ tops G C := by
      rw [topMem]
      exact ⟨halen, hop, hbel⟩
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
    have e0 : opnd C a 0 = p := by simp [opndDef, hin]
    have e1 : opnd C a 1 = q := by simp [opndDef, hin]
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
      have hjunk : h ∈ junk G C := by
        unfold junk gatesWhere
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
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
        rw [starsDef, Finset.mem_biUnion]
        refine ⟨a, hatop, Finset.mem_image.mpr ⟨(t1, t2), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩⟩
        · simp only [sideDef, e0]
          exact reach_mem_orIn t1 hr1
        · simp only [sideDef, e1]
          exact reach_mem_orIn t2 hr2
      · exact junk_of q 1 e1 (by rw [hin]; simp) hq.1 h hh hhor hr hv
    · exact junk_of p 0 e0 (by rw [hin]; simp) hp.1 h hh hhor hr hv


  -- On an OR-only path from a nonempty raw input set to an AND, a gate loses all raw
  -- inputs along the child that continues the path. Such a gate cannot be in lambda.
  have boundary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (ao : IsAO2 n C) (h : ℕ) (hand : (gateAt C h).op = GateOp.and) (w : ℕ)
      (reach : OrReaches n C w h) :
      (orIn n C w).Nonempty → (orN G C \ lam G C).Nonempty := by
    classical
    have path := (orReaches_reach h w reach).1
    clear reach
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl =>
      rintro ⟨i,hi⟩
      rcases (mem_orIn_reach i hi).cases_head with eq | ⟨k, step, _⟩
      · omega
      · obtain ⟨j,_, eqj, hop, _, _⟩ := step
        have ej : h = j := by omega
        subst j
        rw [hand] at hop
        contradiction
    | @head v y edge rest ih =>
      intro hv
      by_cases raw : (orIn n C y).Nonempty
      · exact ih raw
      · obtain ⟨j, hj, rfl, op, hy, _⟩ := edge
        obtain ⟨i, hi⟩ := hv
        have dirty : ¬ BelowF G C j := by
          intro clean
          apply G.irrefl (v := i)
          apply (graphFun_pair G i i).mp
          apply clean (pairInput i i)
          exact reach_var_val _ _ i (mem_orIn_reach i hi) (pairInput_left i i)
        have mem : j ∈ orN G C := by
          rw [orNMem]
          exact ⟨hj, op, dirty⟩
        refine ⟨j, Finset.mem_sdiff.mpr ⟨mem, fun hLam => ?_⟩⟩
        obtain ⟨-,h0,h1,-⟩ := Finset.mem_filter.mp hLam
        obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hj))
        rw [hab] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact raw (by simpa [opndDef, hab, List.getD_eq_getElem?_getD] using h0)
        · exact raw (by simpa [opndDef, hab, List.getD_eq_getElem?_getD] using h1)

  have two_slots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (least : IsLeastAO G C) (top : TopForm G C) (res : (Ustar G C).Nonempty) :
      2 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
    classical
    obtain ⟨e, he⟩ := res
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨a,ha,b,h,hh,_,reach,_⟩ := off_star G C least top u v he
      have jpos : 0 < (junk G C).card := Finset.card_pos.mpr ⟨_,hh⟩
      by_cases c : a ∈ centreless G C
      · have cpos := Finset.card_pos.mpr ⟨a,c⟩
        omega
      · have raw : (side (n := n) C a b).Nonempty := by
          apply Finset.nonempty_iff_ne_empty.mpr
          intro empty
          apply c
          refine Finset.mem_filter.mpr ⟨ha, ?_⟩
          fin_cases b
          · exact Or.inl empty
          · exact Or.inr empty
        have andh : (gateAt C h).op = GateOp.and :=
          (show PEqualNP.CleanedNonEdge.IsDirtyAnd n G C h from (Finset.mem_filter.mp hh).2).1
        have opos := Finset.card_pos.mpr (boundary G C least.1 h andh (opnd C a b) reach raw)
        omega
  have covered_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (AO : IsLeastAO G C) (hf : NoFourCycle G) (M : Finset (Fin n × Fin n))
      (covered : ∀ p ∈ M, s(p.1, p.2) ∈ starEdges G C)
      (first : ∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q)
      (second : ∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q)
      (cross : ∀ p ∈ M, ∀ q ∈ M, p.1 ≠ q.2) :
      M.card ≤ (tops G C \ centreless G C).card := by
    classical
    let good := tops G C \ centreless G C
    have witness (p : M) : ∃ j : good, ∃ u ∈ side C j.val 0, ∃ v ∈ side C j.val 1,
        s(u, v) = s(p.val.1, p.val.2) := by
      obtain ⟨j, hj, hpair⟩ := Finset.mem_biUnion.mp (covered p.val p.property)
      obtain ⟨⟨u, v⟩, huv, eq⟩ := Finset.mem_image.mp hpair
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
      have goodj : j ∈ good := by
        refine Finset.mem_sdiff.mpr ⟨hj, ?_⟩
        intro hcent
        rcases (Finset.mem_filter.mp hcent).2 with e | e
        · simp [e] at hu
        · simp [e] at hv
      exact ⟨⟨j, goodj⟩, u, hu, v, hv, eq⟩
    choose owner howner using witness
    refine Finset.card_le_card_of_injective (f := owner) ?_
    intro p q heq
    apply Subtype.ext
    by_contra diff
    obtain ⟨a, ha, b, hb, ab⟩ := howner p
    obtain ⟨c, hc, d, hd, cd⟩ := howner q
    rw [← heq] at hc hd
    have ht := (Finset.mem_sdiff.mp (owner p).property).1
    have apart (i k : Fin n) (pi : i = p.val.1 ∨ i = p.val.2) (qk : k = q.val.1 ∨ k = q.val.2) : i ≠ k := by
      intro e
      rcases pi with rfl | rfl <;> rcases qk with rfl | rfl
      · exact diff (first _ p.property _ q.property e)
      · exact cross _ p.property _ q.property e
      · exact cross _ q.property _ p.property e.symm
      · exact diff (second _ p.property _ q.property e)
    have endpoints {x y : Fin n} {edge : Fin n × Fin n} (e : s(x,y) = s(edge.1, edge.2)) :
        (x = edge.1 ∨ x = edge.2) ∧ (y = edge.1 ∨ y = edge.2) := by
      rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := edge)).mp e with ep | ep
      · exact ⟨Or.inl (congrArg Prod.fst ep), Or.inr (congrArg Prod.snd ep)⟩
      · exact ⟨Or.inr (congrArg Prod.fst ep), Or.inl (congrArg Prod.snd ep)⟩
    have ac : a ≠ c := apart a c (endpoints ab).1 (endpoints cd).1
    have bd : b ≠ d := apart b d (endpoints ab).2 (endpoints cd).2
    have twocommon : ({b, d} : Finset (Fin n)) ⊆ (Finset.univ.filter fun x => G.Adj a x ∧ G.Adj c x) := by
      intro t ht'
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using ht' : t = b ∨ t = d) with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (fun j hj u v hu hv => (top_facts G C hf AO j hj).2.1 u hu v hv) _ ht _ _ ha hb,
          (fun j hj u v hu hv => (top_facts G C hf AO j hj).2.1 u hu v hv) _ ht _ _ hc hb⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (fun j hj u v hu hv => (top_facts G C hf AO j hj).2.1 u hu v hv) _ ht _ _ ha hd,
          (fun j hj u v hu hv => (top_facts G C hf AO j hj).2.1 u hu v hv) _ ht _ _ hc hd⟩
    have low := Finset.card_le_card twocommon
    have high := hf a c ac
    simp [bd] at low
    omega

  have matched_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (AO : IsLeastAO G C) (hf : NoFourCycle G) (M : Finset (Fin n × Fin n))
      (edges : ∀ p ∈ M, G.Adj p.1 p.2)
      (first : ∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q)
      (second : ∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q)
      (cross : ∀ p ∈ M, ∀ q ∈ M, p.1 ≠ q.2) :
      M.card ≤ (tops G C \ centreless G C).card + (Ustar G C).card := by
    classical
    let mark (p : Fin n × Fin n) := s(p.1, p.2) ∈ starEdges G C
    let A := M.filter mark
    let B := M.filter fun p => ¬ mark p
    have optA : A.card ≤ (tops G C \ centreless G C).card := by
      apply covered_bound G C AO hf A
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
      · intro p hp q hq e
        exact first p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 e
      · intro p hp q hq e
        exact second p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 e
      · intro p hp q hq
        exact cross p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
    have optB : B.card ≤ (Ustar G C).card := by
      apply Finset.card_le_card_of_injOn (fun p : Fin n × Fin n => s(p.1, p.2))
      · intro p hp
        obtain ⟨hpm, hno⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.2 (edges p hpm)), hno⟩
      · intro p hp q hq e
        rcases (Sym2.mk_eq_mk_iff (p := p) (q := q)).mp e with same | swap
        · exact same
        · have hpm := (Finset.mem_filter.mp hp).1
          have hqm := (Finset.mem_filter.mp hq).1
          exact (cross p hpm q hqm (congrArg Prod.fst swap)).elim
    have sum : A.card + B.card = M.card := Finset.card_filter_add_card_filter_not mark
    omega
  intro n G decG C M hf ne hc ht lex bip deg edges first second cross
  classical
  let U := Ustar G C
  let total := (tops G C \ centreless G C).card + 2 * (centreless G C).card +
    (junk G C).card + (orN G C \ lam G C).card
  change U.card + M.card ≤ total
  by_cases small : U.card ≤ 1
  · have pay := matched_budget G C hc hf M edges first second cross
    by_cases un : U.Nonempty
    · have b := two_slots G C hc ht un
      change (Ustar G C).card ≤ 1 at small
      dsimp only [U,total]
      omega
    · have zero : U.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp un)
      change (Ustar G C).card = 0 at zero
      dsimp only [U,total]
      omega
  let E := M.image fun p => s(p.1,p.2)
  have enn : E.card = M.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb eq
    rcases (Sym2.mk_eq_mk_iff (p := a) (q := b)).mp eq with same | rev
    · exact same
    · exact (cross a ha b hb (congrArg Prod.fst rev)).elim
  have ein : E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.2 (edges p hp))
  have apart : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ v ∈ e, v ∉ f := by
    intro e he f hf hdiff v hv hv'
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hf
    rcases Sym2.mem_iff.mp hv with h | h <;> rcases Sym2.mem_iff.mp hv' with h' | h'
    · exact hdiff (congrArg (fun t : Fin n × Fin n => s(t.1,t.2)) (first p hp q hq (h.symm.trans h')))
    · exact cross p hp q hq (h.symm.trans h')
    · exact cross q hq p hp (h'.symm.trans h)
    · exact hdiff (congrArg (fun t : Fin n × Fin n => s(t.1,t.2)) (second p hp q hq (h.symm.trans h')))
  have charge (F : Finset (Sym2 (Fin n))) (hF : F ⊆ E) (K : Finset (Fin n))
      (cover : ∀ e ∈ F, ∃ v ∈ K, v ∈ e) : F.card ≤ K.card := by
    choose v hK hv using (fun e : F => cover e.val e.property)
    let pay (e : F) : K := ⟨v e,hK e⟩
    have inj : Function.Injective pay := by
      intro e f h
      apply Subtype.ext
      by_contra neq
      have eq : v e = v f := congrArg Subtype.val h
      exact apart e (hF e.property) f (hF f.property) neq (v e) (hv e) (eq ▸ hv f)
    simpa using Fintype.card_le_of_injective pay inj
  by_cases centered : ∃ z : Fin n, ∀ e ∈ U, z ∈ e
  · obtain ⟨z,hz⟩ := centered
    obtain ⟨K,covered,leaf,cost⟩ := star n G C hf ne hc ht lex bip deg (show 2 ≤ U.card by omega) z hz
    have paid := charge E (fun _ => id) K (by
      intro e he
      by_cases hu : e ∈ U
      · obtain ⟨v,eq⟩ := Sym2.mem_iff_exists.mp (hz e hu)
        rcases leaf with h | h
        · exact ⟨z,h,hz e hu⟩
        · exact ⟨v,h v (eq ▸ hu),eq ▸ Sym2.mem_mk_right z v⟩
      · exact covered e (Finset.mem_sdiff.mpr ⟨ein he,hu⟩))
    change U.card + K.card ≤ total at cost
    omega
  · have sep : ∃ e ∈ U, ∃ f ∈ U, ∀ v ∈ e, v ∉ f := by
      by_contra! meet
      obtain ⟨e,he⟩ : U.Nonempty := Finset.card_pos.mp (by omega)
      induction e using Sym2.inductionOn with
      | _ a b =>
        have missed (v : Fin n) : ∃ e ∈ U, v ∉ e := by
          by_contra! h
          exact centered ⟨v,h⟩
        obtain ⟨p,hp,ha⟩ := missed a
        obtain ⟨q,hq,hb⟩ := missed b
        obtain ⟨v,hv,vp⟩ := meet _ he _ hp
        obtain ⟨w,hw,wq⟩ := meet _ he _ hq
        have bp : b ∈ p := by
          rcases Sym2.mem_iff.mp hv with rfl | rfl
          · exact (ha vp).elim
          · exact vp
        have aq : a ∈ q := by
          rcases Sym2.mem_iff.mp hw with rfl | rfl
          · exact wq
          · exact (hb wq).elim
        obtain ⟨s,rfl⟩ := Sym2.mem_iff_exists.mp bp
        obtain ⟨t,rfl⟩ := Sym2.mem_iff_exists.mp aq
        obtain ⟨x,hx,hy⟩ := meet _ hp _ hq
        have st : s = t := by
          rcases Sym2.mem_iff.mp hx with rfl | rfl
          · exact (hb hy).elim
          · rcases Sym2.mem_iff.mp hy with rfl | rfl
            · exact (ha (Sym2.mem_mk_right _ _)).elim
            · rfl
        subst t
        obtain ⟨c,hc⟩ := bip
        have adj {u v : Fin n} (h : s(u,v) ∈ U) : G.Adj u v :=
          G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp ((Finset.mem_sdiff.mp h).1))
        have ab := hc _ _ (adj he)
        have bs := hc _ _ (adj hp)
        have as' := hc _ _ (adj hq)
        exact (show ∀ x y z : Bool, x ≠ y → y ≠ z → x ≠ z → False by decide) _ _ _ ab bs as'
    let R := E.filter fun e => e ∈ U
    let F := E.filter fun e => e ∉ U
    have rU : R ⊆ U := fun _ h => (Finset.mem_filter.mp h).2
    have rE : R ⊆ E := Finset.filter_subset _ _
    have fE : F ⊆ E := Finset.filter_subset _ _
    obtain ⟨K,covered,cost⟩ := separate n G C hf ne hc ht lex bip deg sep R rU
      (fun e he f hf => apart e (rE he) f (rE hf))
    have paid := charge F fE K (by
      intro e he
      have eu := (Finset.mem_filter.mp he).2
      apply covered e (Finset.mem_sdiff.mpr ⟨ein (fE he),eu⟩)
      intro v hv r hr
      exact apart e (fE he) r (rE hr) (fun eq => eu (eq ▸ rU hr)) v hv)
    have sum : R.card + F.card = E.card := Finset.card_filter_add_card_filter_not _
    change U.card + R.card + K.card ≤ total at cost
    omega
