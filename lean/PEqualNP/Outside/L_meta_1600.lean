import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1600

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
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

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
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

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
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

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
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

lemma graphFun_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    graphFun G ∅ (fun _ : Fin n => false) = false := by
  simp [graphFun]

lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
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

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → graphFun G ∅ x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  have hF : graphFun G ∅ (pairInput u v) = true := by
    apply hbel
    rw [val_and (n := n) (by simp) ha hop, hin]
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
    · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩
  exact (graphFun_pair G u v).mp hF

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
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
      simp only [coneStep, List.getD_eq_getElem?_getD]
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
        simp only [coneStep, List.getD_eq_getElem?_getD]
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
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
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

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
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

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

lemma mono_op {C : Circuit} (hM : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    g.op = GateOp.and ∨ g.op = GateOp.or := by
  have h := (hM g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  exact h

lemma and_inputs_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true) :
    (gateAt C j).inputs ≠ [] := by
  intro he
  have htrue : gateVal n C j (fun _ => false) = true := by
    rw [gateVal_eq_val, val_and (n := n) (by simp) hj hand, he]
    intro i hi; cases hi
  have := hbel _ htrue
  rw [graphFun_false G] at this
  cases this

lemma owns_trace_var {n : ℕ} {C : Circuit} (hM : Monotone2 C)
    {j : ℕ} (hj : j < C.gates.length) (_hand : (gateAt C j).op = GateOp.and)
    (u v : Fin n) (hows : Owns n C j u v) (w : ℕ)
    (hin : w ∈ (gateAt C j).inputs) (hw : w < n + j)
    (hv : val C (List.ofFn (pairInput u v)) w = true) :
    ∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) w t.val := by
  rcases operand_trace (C := C) u v w hv with h | ⟨h, hh, hnor, hr, hval⟩
  · exact h
  · have handh : (gateAt C h).op = GateOp.and := by
      rcases mono_op hM (gateAt_mem hh) with h1 | h1
      · exact h1
      · exact (hnor h1).elim
    have hcone : InCone n C h j := operand_cone hj hin hw hr
    have hlt : h < j := by
      have := orStep_le hr
      omega
    have hfalse := hows.2.2.2 h hlt hcone handh
    rw [gateVal_eq_val] at hfalse
    rw [hfalse] at hval
    cases hval

lemma owns_fanin_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hM : Monotone2 C)
    {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true)
    {u v : Fin n} (hows : Owns n C j u v) :
    ∃ p q, (gateAt C j).inputs = [p, q] := by
  have hle : (gateAt C j).inputs.length ≤ 2 := (hM _ (gateAt_mem hj)).2
  have hne := and_inputs_nonempty G hj hand hbel
  cases hinputs : (gateAt C j).inputs with
  | nil => exact (hne hinputs).elim
  | cons p rest =>
    cases rest with
    | nil =>
      exfalso
      have hlen : (gateAt C j).inputs = [p] := by simpa using hinputs
      have hval := hows.2.2.1
      rw [gateVal_eq_val, val_and (n := n) (by simp) hj hand, hlen] at hval
      have hpq := hval p (by simp)
      obtain ⟨t, _, hr⟩ := owns_trace_var hM hj hand u v hows p (by simp [hlen]) hpq.1 hpq.2
      have hcopy : gateVal n C j (pairInput t t) = true := by
        rw [gateVal_eq_val, val_and (n := n) (by simp) hj hand, hlen]
        intro i hi
        have hi' : i = p := List.mem_singleton.mp hi
        rw [hi']
        exact ⟨hpq.1, reach_var_val (pairInput t t) p t hr (pairInput_left t t)⟩
      have := (graphFun_pair G t t).mp (hbel _ hcopy)
      exact G.irrefl this
    | cons q rest2 =>
      cases rest2 with
      | nil =>
        exact ⟨p, q, rfl⟩
      | cons _r _rest3 =>
        exfalso
        have h3 : 3 ≤ (gateAt C j).inputs.length := by
          simpa [hinputs]
        omega

lemma owned_ends {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hM : Monotone2 C)
    {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true)
    (w0 w1 : ℕ) (hin : (gateAt C j).inputs = [w0, w1])
    {u v : Fin n} (hows : Owns n C j u v) :
    w0 < n + j ∧ w1 < n + j ∧
      ((Relation.ReflTransGen (OrStep n C) w0 u.val ∧
          Relation.ReflTransGen (OrStep n C) w1 v.val) ∨
        (Relation.ReflTransGen (OrStep n C) w1 u.val ∧
          Relation.ReflTransGen (OrStep n C) w0 v.val)) := by
  have hval := hows.2.2.1
  rw [gateVal_eq_val, val_and (n := n) (by simp) hj hand, hin] at hval
  have hp := hval w0 (by simp)
  have hq := hval w1 (by simp)
  obtain ⟨tu, htu, hru⟩ := owns_trace_var hM hj hand u v hows w0 (by simp [hin]) hp.1 hp.2
  obtain ⟨tv, htv, hrv⟩ := owns_trace_var hM hj hand u v hows w1 (by simp [hin]) hq.1 hq.2
  refine ⟨hp.1, hq.1, ?_⟩
  have hdiff : tu ≠ tv := by
    intro he
    subst he
    have hgate : gateVal n C j (pairInput tu tu) = true := by
      rw [gateVal_eq_val, val_and (n := n) (by simp) hj hand, hin]
      intro i hi
      have hi' : i = w0 ∨ i = w1 := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using hi
      rcases hi' with h | h
      · rw [h]; exact ⟨hp.1, reach_var_val (pairInput tu tu) w0 tu hru (pairInput_left tu tu)⟩
      · rw [h]; exact ⟨hq.1, reach_var_val (pairInput tu tu) w1 tu hrv (pairInput_left tu tu)⟩
    exact G.irrefl ((graphFun_pair G tu tu).mp (hbel _ hgate))
  rcases htu with htu | htu
  · rcases htv with htv | htv
    · exact (hdiff (htu.trans htv.symm)).elim
    · subst htu; subst htv; exact Or.inl ⟨hru, hrv⟩
  · rcases htv with htv | htv
    · subst htu; subst htv; exact Or.inr ⟨hrv, hru⟩
    · exact (hdiff (htu.trans htv.symm)).elim

theorem main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hM : Monotone2 C)
    (j : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true) :
    (∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v) ∨
      ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → Owns n C j p q → p = s ∨ q = s := by
  classical
  by_cases hnone : ∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v
  · exact Or.inl hnone
  · right
    push Not at hnone
    obtain ⟨u0, v0, _, howns0⟩ := hnone
    obtain ⟨p, q, hin⟩ := owns_fanin_two G hM hj hand hbel howns0
    obtain ⟨hp0, hq0, _⟩ := owned_ends G hM hj hand hbel p q hin howns0
    let A : Finset (Fin n) :=
      Finset.univ.filter fun u => Relation.ReflTransGen (OrStep n C) p u.val
    let B : Finset (Fin n) :=
      Finset.univ.filter fun u => Relation.ReflTransGen (OrStep n C) q u.val
    have hadjAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b := by
      intro a ha b hb
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact side_adj G j hj hand (fun x hx => by
          simpa [gateVal_eq_val] using hbel x (by simpa [gateVal_eq_val] using hx))
        p q hin hp0 hq0 a b ha hb
    have hcard := biclique_star G h4 A B hadjAB
    have howned : ∀ x y : Fin n, Owns n C j x y →
        (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A) := by
      intro x y hows
      obtain ⟨_, _, hdir⟩ := owned_ends G hM hj hand hbel p q hin hows
      simpa only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] using hdir
    rcases hcard with hA | hB
    · have hAne : A.Nonempty := by
        obtain ⟨_, _, hdir⟩ := owned_ends G hM hj hand hbel p q hin howns0
        refine Finset.nonempty_iff_ne_empty.mpr ?_
        intro hempty
        have : u0 ∈ A ∨ v0 ∈ A := by
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hdir with ⟨hru, _⟩ | ⟨_, hrv⟩
          · exact Or.inl hru
          · exact Or.inr hrv
        have hmem : ∀ z ∈ A, False := by
          intro z hz; rw [hempty] at hz; cases hz
        rcases this with hu | hv
        · exact hmem _ hu
        · exact hmem _ hv
      obtain ⟨s, hs⟩ := Finset.card_eq_one.mp (le_antisymm hA (Finset.one_le_card.mpr hAne))
      refine ⟨s, ?_⟩
      intro x y _ hows
      have hsx : x ∈ A → x = s := by
        intro hx; simpa [hs] using hx
      have hsy : y ∈ A → y = s := by
        intro hy; simpa [hs] using hy
      rcases howned x y hows with ⟨hx, _⟩ | ⟨_, hy⟩
      · exact Or.inl (hsx hx)
      · exact Or.inr (hsy hy)
    · have hBne : B.Nonempty := by
        obtain ⟨_, _, hdir⟩ := owned_ends G hM hj hand hbel p q hin howns0
        refine Finset.nonempty_iff_ne_empty.mpr ?_
        intro hempty
        have : u0 ∈ B ∨ v0 ∈ B := by
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hdir with ⟨_, hrv⟩ | ⟨hru, _⟩
          · exact Or.inr hrv
          · exact Or.inl hru
        have hmem : ∀ z ∈ B, False := by
          intro z hz; rw [hempty] at hz; cases hz
        rcases this with hu | hv
        · exact hmem _ hu
        · exact hmem _ hv
      obtain ⟨s, hs⟩ := Finset.card_eq_one.mp (le_antisymm hB (Finset.one_le_card.mpr hBne))
      refine ⟨s, ?_⟩
      intro x y _ hows
      have hsx : x ∈ B → x = s := by
        intro hx; simpa [hs] using hx
      have hsy : y ∈ B → y = s := by
        intro hy; simpa [hs] using hy
      rcases howned x y hows with ⟨_, hy⟩ | ⟨hx, _⟩
      · exact Or.inr (hsy hy)
      · exact Or.inl (hsx hx)

end PEqualNP.Outside.L_meta_1600

theorem PEqualNP.Outside.L_meta_1600 :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → ∀ j : ℕ, j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C j x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) → (∀ u v : Fin n, G.Adj u v → ¬ PEqualNP.EdgeOwnership.Owns n C j u v) ∨ ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → PEqualNP.EdgeOwnership.Owns n C j p q → p = s ∨ q = s := by
  intro n G _ hC4 C hM j hj hand hbel
  exact PEqualNP.Outside.L_meta_1600.main G hC4 C hM j hj hand hbel
