import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1652

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

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

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

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

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

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

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

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

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
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

open PEqualNP.EdgeOwnership in
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

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
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

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
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

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

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

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
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
      simp only [orStep, List.getD_eq_getElem?_getD]
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
          simp only [orStep, List.getD_eq_getElem?_getD]
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
          simp only [orStep, List.getD_eq_getElem?_getD]
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
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
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

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
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

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
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

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

open PEqualNP.TopForm in
lemma top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
    (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
    ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
    intro u hu v hv
    simp only [side, e0] at hu
    simp only [side, e1] at hv
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


lemma gateAt_ge {C : Circuit} {k : ℕ} (hk : C.gates.length ≤ k) :
    gateAt C k = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

lemma orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (OrStep n C) p u.val :=
  ⟨mem_orIn_reach u, reach_mem_orIn u⟩

lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)

lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)
lemma opnd_lt {n : ℕ} {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hRB : ReadsBack n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    PEqualNP.TopForm.opnd C a b < n + a := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem ha))
  have hp : p < n + a := hRB a ha p (by rw [hin]; simp)
  have hq : q < n + a := hRB a ha q (by rw [hin]; simp)
  fin_cases b
  · simpa [PEqualNP.TopForm.opnd, hin] using hp
  · simpa [PEqualNP.TopForm.opnd, hin] using hq

open PEqualNP.TopForm

lemma fin2_sub : ∀ b : Fin 2, (b = 0 ∧ 1 - b = 1) ∨ (b = 1 ∧ 1 - b = 0) := by decide

lemma fin2_ne' : ∀ b c : Fin 2, b ≠ c → 1 - c = b := by decide

open Classical in
theorem count {α : Type} [DecidableEq α] (lv : ℕ → Finset α) (R : ℕ → ℕ → Prop) (Br : ℕ → Prop)
    (hrefl : ∀ w, R w w) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hcase : ∀ N, (lv N).card ≤ 1 ∨ ∃ a b, a < N ∧ b < N ∧ R N a ∧ R N b ∧
      lv N ⊆ lv a ∪ lv b ∧ ((lv a).Nonempty → (lv b).Nonempty → Br N)) :
    ∀ (N : ℕ) (S : Finset ℕ), (∀ w ∈ S, w < N) →
      (S.biUnion lv).card ≤ S.card +
        ((Finset.range N).filter (fun h => Br h ∧ ∃ w ∈ S, R w h)).card := by
  intro N
  induction N with
  | zero =>
    intro S hS
    have hS0 : S = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun w hw => by have := hS w hw; omega)
    subst hS0
    simp
  | succ N ih =>
    intro S hS
    have mono : ∀ S2 : Finset ℕ, (∀ w ∈ S2, ∃ w' ∈ S, R w' w) →
        (Finset.range N).filter (fun h => Br h ∧ ∃ w ∈ S2, R w h) ⊆
        ((Finset.range (N + 1)).filter (fun h => Br h ∧ ∃ w ∈ S, R w h)).erase N := by
      intro S2 h2 h hh
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase] at hh ⊢
      obtain ⟨h1, hb, w, hw, hr⟩ := hh
      obtain ⟨w', hw', hr'⟩ := h2 w hw
      exact ⟨by omega, by omega, hb, w', hw', htrans _ _ _ hr' hr⟩
    have herase := Finset.card_erase_le
      (s := (Finset.range (N + 1)).filter (fun h => Br h ∧ ∃ w ∈ S, R w h)) (a := N)
    by_cases hN : N ∈ S
    · have hS'lt : ∀ w ∈ S.erase N, w < N := by
        intro w hw
        have h1 := Finset.mem_erase.mp hw
        have := hS w h1.2
        omega
      have hcard : (S.erase N).card + 1 = S.card := Finset.card_erase_add_one hN
      have hbu : S.biUnion lv = lv N ∪ (S.erase N).biUnion lv := by
        conv_lhs => rw [← Finset.insert_erase hN]
        rw [Finset.biUnion_insert]
      have hself : ∀ w ∈ S.erase N, ∃ w' ∈ S, R w' w :=
        fun w hw => ⟨w, (Finset.mem_erase.mp hw).2, hrefl w⟩
      have one : ∀ e, e < N → R N e → lv N ⊆ lv e →
          (S.biUnion lv).card ≤ S.card +
            ((Finset.range (N + 1)).filter (fun h => Br h ∧ ∃ w ∈ S, R w h)).card := by
        intro e he hRe hsub
        have hS2lt : ∀ w ∈ insert e (S.erase N), w < N := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact he
          · exact hS'lt w hw
        have hS2r : ∀ w ∈ insert e (S.erase N), ∃ w' ∈ S, R w' w := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact ⟨N, hN, hRe⟩
          · exact hself w hw
        have h2 := ih _ hS2lt
        have h3 := Finset.card_le_card (mono _ hS2r)
        have h5 : S.biUnion lv ⊆ (insert e (S.erase N)).biUnion lv := by
          rw [hbu, Finset.biUnion_insert]
          exact Finset.union_subset_union hsub (Finset.Subset.refl _)
        have h6 := Finset.card_le_card h5
        have h7 := Finset.card_insert_le e (S.erase N)
        omega
      rcases hcase N with h1 | ⟨a, b, ha, hb, hRa, hRb, hsub, hbr⟩
      · have h2 := ih (S.erase N) hS'lt
        have h3 := Finset.card_le_card (mono (S.erase N) hself)
        have h5 : (S.biUnion lv).card ≤ (lv N).card + ((S.erase N).biUnion lv).card := by
          rw [hbu]; exact Finset.card_union_le _ _
        omega
      · by_cases hna : (lv a).Nonempty
        · by_cases hnb : (lv b).Nonempty
          · have hNB : N ∈ (Finset.range (N + 1)).filter
                (fun h => Br h ∧ ∃ w ∈ S, R w h) := by
              simp only [Finset.mem_filter, Finset.mem_range]
              exact ⟨by omega, hbr hna hnb, N, hN, hrefl N⟩
            have h4 := Finset.card_erase_add_one hNB
            have hS2lt : ∀ w ∈ insert a (insert b (S.erase N)), w < N := by
              intro w hw
              rcases Finset.mem_insert.mp hw with rfl | hw
              · exact ha
              · rcases Finset.mem_insert.mp hw with rfl | hw
                · exact hb
                · exact hS'lt w hw
            have hS2r : ∀ w ∈ insert a (insert b (S.erase N)), ∃ w' ∈ S, R w' w := by
              intro w hw
              rcases Finset.mem_insert.mp hw with rfl | hw
              · exact ⟨N, hN, hRa⟩
              · rcases Finset.mem_insert.mp hw with rfl | hw
                · exact ⟨N, hN, hRb⟩
                · exact hself w hw
            have h2 := ih _ hS2lt
            have h3 := Finset.card_le_card (mono _ hS2r)
            have h5 : S.biUnion lv ⊆ (insert a (insert b (S.erase N))).biUnion lv := by
              rw [hbu, Finset.biUnion_insert, Finset.biUnion_insert]
              intro u hu
              rcases Finset.mem_union.mp hu with hu | hu
              · rcases Finset.mem_union.mp (hsub hu) with h | h
                · exact Finset.mem_union_left _ h
                · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
              · exact Finset.mem_union_right _ (Finset.mem_union_right _ hu)
            have h6 := Finset.card_le_card h5
            have e1 := Finset.card_insert_le a (insert b (S.erase N))
            have e2 := Finset.card_insert_le b (S.erase N)
            omega
          · refine one a ha hRa ?_
            rw [Finset.not_nonempty_iff_eq_empty] at hnb
            rw [hnb, Finset.union_empty] at hsub
            exact hsub
        · refine one b hb hRb ?_
          rw [Finset.not_nonempty_iff_eq_empty] at hna
          rw [hna, Finset.empty_union] at hsub
          exact hsub
    · have hlt : ∀ w ∈ S, w < N := by
        intro w hw
        have h1 := hS w hw
        have h2 : w ≠ N := fun h => hN (h ▸ hw)
        omega
      have h2 := ih S hlt
      have h3 := Finset.card_le_card (mono S (fun w hw => ⟨w, hw, hrefl w⟩))
      omega

theorem top_branch (St : ℕ → ℕ → Prop) (hlt : ∀ w w', St w w' → w' < w) (Mw : Set ℕ) (r : ℕ)
    (hne : ∀ w, Relation.ReflTransGen St r w → w ∉ Mw → ∀ w1 w2, St w w1 → St w w2 →
      (∃ p ∈ Mw, Relation.ReflTransGen St w1 p) → (∃ q ∈ Mw, Relation.ReflTransGen St w2 q) →
      w1 = w2) :
    ∀ w, Relation.ReflTransGen St r w → (∃ p ∈ Mw, Relation.ReflTransGen St w p) →
      (∀ p ∈ Mw, Relation.ReflTransGen St w p) →
      ∃ k ∈ Mw, ∀ p ∈ Mw, Relation.ReflTransGen St k p := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hrw hex hall
    by_cases hw : w ∈ Mw
    · exact ⟨w, hw, hall⟩
    · obtain ⟨p, hp, hwp⟩ := hex
      rcases Relation.ReflTransGen.cases_head hwp with h | ⟨w1, hst, hr1⟩
      · exact absurd (by rw [h]; exact hp) hw
      · refine ih w1 (hlt _ _ hst) (hrw.tail hst) ⟨p, hp, hr1⟩ ?_
        intro q hq
        rcases Relation.ReflTransGen.cases_head (hall q hq) with h | ⟨w2, hst2, hr2⟩
        · exact absurd (by rw [h]; exact hq) hw
        · have h12 := hne w hrw hw w1 w2 hst hst2 ⟨p, hp, hr1⟩ ⟨q, hq, hr2⟩
          rw [h12]
          exact hr2

lemma inputs_eq {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) {k : ℕ}
    (hk : k < C.gates.length) :
    (gateAt C k).inputs = [opnd C k 0, opnd C k 1] := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
  have e0 : opnd C k 0 = p := by simp [opnd, hin]
  have e1 : opnd C k 1 = q := by simp [opnd, hin]
  rw [e0, e1, hin]

lemma opnd_mem {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) {k : ℕ}
    (hk : k < C.gates.length) (b : Fin 2) :
    opnd C k b ∈ (gateAt C k).inputs := by
  have hin := inputs_eq h2 hk
  rcases fin2_sub b with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · rw [hin]; exact List.mem_cons_self
  · rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self

lemma orIn_mono {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    orIn n C w' ⊆ orIn n C w :=
  fun u hu => (orIn_iff_reach w u).2 (h.trans ((orIn_iff_reach w' u).1 hu))

lemma orIn_opnd {n : ℕ} {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hRB : ReadsBack n C) {k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (b : Fin 2) :
    orIn n C (opnd C k b) ⊆ orIn n C (n + k) :=
  fun u hu => (orIn_gate C k u).mpr ⟨hk, hop, opnd C k b, opnd_mem h2 hk b,
    opnd_lt h2 hRB hk b, hu⟩

lemma not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ)
    (h : (orIn n C (n + k)).Nonempty) : ¬ BelowF G C k := by
  intro hb
  obtain ⟨u, hu⟩ := h
  have hr := mem_orIn_reach u hu
  have hv := reach_var_val (pairInput u u) (n + k) u hr (pairInput_left u u)
  have h3 := hb (pairInput u u) ((gateVal_eq_val n C k _).trans hv)
  exact G.irrefl ((graphFun_pair G u u).mp h3)

lemma mem_lam {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hRB : ReadsBack n C)
    (k : ℕ) (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or)
    (h0 : (orIn n C (opnd C k 0)).Nonempty) (h1 : (orIn n C (opnd C k 1)).Nonempty)
    (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2) (c : Fin n)
    (hs : side (n := n) C a (1 - b) = {c})
    (hr : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + k)) :
    k ∈ lam G C ∧ OrReaches n C (opnd C a b) k := by
  have hor := reach_orReaches hr k rfl hk
  refine ⟨?_, hor⟩
  have hnb : ¬ BelowF G C k := by
    apply not_below
    obtain ⟨u, hu⟩ := h0
    exact ⟨u, orIn_opnd h2 hRB hk hop 0 hu⟩
  have hc1 : (side (n := n) C a (1 - b)).card = 1 := by
    rw [hs]; exact Finset.card_singleton c
  simp only [lam, orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
  exact ⟨⟨hk, hop, hnb⟩, h0, h1, a, ha, b, hc1, hor⟩

lemma lam_ne {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hRB : ReadsBack n C) (h : ℕ)
    (hh : h ∈ lam G C) : (orIn n C (n + h)).Nonempty := by
  simp only [lam, orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hh
  obtain ⟨⟨hk, hop, _⟩, ⟨u, hu⟩, _⟩ := hh
  exact ⟨u, orIn_opnd h2 hRB hk hop 0 hu⟩

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C)
    (c : Fin n) (T M : Finset ℕ) (L : Finset (Fin n))
    (hT : ∀ t, t ∈ T ↔ t ∈ tops G C ∧ ∃ p : Fin 2, side (n := n) C t (1 - p) = {c})
    (hM : ∀ h, h ∈ M ↔ h ∈ lam G C ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
      side (n := n) C a (1 - b) = {c} ∧ OrReaches n C (opnd C a b) h)
    (hLd : ∀ v, v ∈ L ↔ ∃ d ∈ tops G C, ∃ q : Fin 2,
      side (n := n) C d (1 - q) = {c} ∧ v ∈ side (n := n) C d q)
    (Bc : Finset (Finset (Fin n))) (hBc : ∀ X ∈ Bc, ∃ k ∈ M, orIn n C (n + k) = X) :
    (∀ w ∈ L, G.Adj c w ∧ s(c, w) ∈ starEdges G C) ∧ L.card ≤ T.card + M.card ∧
    (Bc.Nonempty → Bc.card + 1 ≤ T.card + M.card) ∧
    (Bc.Nonempty → (∀ X' ∈ Bc, ∃ X'' ∈ Bc, ¬ X'' ⊆ X') → Bc.card + 2 ≤ T.card + M.card) := by
  have hL' := hL
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL'
  -- adjacency of the centre with the other side
  have hadj : ∀ d ∈ tops G C, ∀ q : Fin 2, side (n := n) C d (1 - q) = {c} →
      ∀ w ∈ side (n := n) C d q, G.Adj c w := by
    intro d hd q hs w hw
    have hf := (top_facts G C h4 hL d hd).2.1
    have hc : c ∈ side (n := n) C d (1 - q) := by rw [hs]; exact Finset.mem_singleton_self c
    rcases fin2_sub q with ⟨rfl, e⟩ | ⟨rfl, e⟩
    · rw [e] at hc
      exact (hf w hw c hc).symm
    · rw [e] at hc
      exact hf c hc w hw
  have huniq : ∀ d ∈ tops G C, ∀ q q' : Fin 2, side (n := n) C d (1 - q) = {c} →
      side (n := n) C d (1 - q') = {c} → q = q' := by
    intro d hd q q' hs hs'
    by_contra hne
    rw [fin2_ne' q q' hne] at hs'
    exact G.irrefl (hadj d hd q hs c (by rw [hs']; exact Finset.mem_singleton_self c))
  have hBM : Bc.card ≤ M.card := by
    refine le_trans (Finset.card_le_card (t := M.image (fun k => orIn n C (n + k))) ?_)
      Finset.card_image_le
    intro X hX
    obtain ⟨k, hk, rfl⟩ := hBc X hX
    exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
  have hTne : Bc.Nonempty → 1 ≤ T.card := by
    rintro ⟨X, hX⟩
    obtain ⟨k, hk, _⟩ := hBc X hX
    obtain ⟨_, a, ha, b, hs, _⟩ := (hM k).mp hk
    exact Finset.card_pos.mpr ⟨a, (hT a).mpr ⟨ha, b, hs⟩⟩
  have hch : ∀ t, t ∈ T → ∃ p : Fin 2, side (n := n) C t (1 - p) = {c} :=
    fun t ht => ((hT t).mp ht).2
  choose! qf hqf using hch
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨d, hd, q, hs, hwq⟩ := (hLd w).mp hw
    refine ⟨hadj d hd q hs w hwq, ?_⟩
    have hc : c ∈ side (n := n) C d (1 - q) := by rw [hs]; exact Finset.mem_singleton_self c
    unfold starEdges
    rcases fin2_sub q with ⟨rfl, e⟩ | ⟨rfl, e⟩
    · rw [e] at hc
      exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr
        ⟨(w, c), Finset.mem_product.mpr ⟨hwq, hc⟩, Sym2.eq_swap⟩⟩
    · rw [e] at hc
      exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr
        ⟨(c, w), Finset.mem_product.mpr ⟨hc, hwq⟩, rfl⟩⟩
  · have hLsub : L ⊆ (T.image (fun d => opnd C d (qf d))).biUnion (orIn n C) := by
      intro v hv
      obtain ⟨d, hd, q, hs, hvq⟩ := (hLd v).mp hv
      have hdT : d ∈ T := (hT d).mpr ⟨hd, q, hs⟩
      have hq : q = qf d := huniq d hd q (qf d) hs (hqf d hdT)
      rw [Finset.mem_biUnion]
      refine ⟨opnd C d (qf d), Finset.mem_image.mpr ⟨d, hdT, rfl⟩, ?_⟩
      rw [← hq]
      exact hvq
    have hcase : ∀ N, (orIn n C N).card ≤ 1 ∨ ∃ a b, a < N ∧ b < N ∧
        Relation.ReflTransGen (OrStep n C) N a ∧ Relation.ReflTransGen (OrStep n C) N b ∧
        orIn n C N ⊆ orIn n C a ∪ orIn n C b ∧
        ((orIn n C a).Nonempty → (orIn n C b).Nonempty →
          ∃ k, N = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
            (orIn n C (opnd C k 0)).Nonempty ∧ (orIn n C (opnd C k 1)).Nonempty) := by
      intro N
      by_cases hNn : N < n
      · exact Or.inl (orIn_input C N hNn)
      · obtain ⟨k, rfl⟩ : ∃ k, N = n + k := ⟨N - n, by omega⟩
        by_cases hg : k < C.gates.length ∧ (gateAt C k).op = GateOp.or
        · right
          obtain ⟨hk, hop⟩ := hg
          have hin := inputs_eq h2 hk
          refine ⟨opnd C k 0, opnd C k 1, opnd_lt h2 hRB hk 0, opnd_lt h2 hRB hk 1,
            ?_, ?_, ?_, ?_⟩
          · exact Relation.ReflTransGen.single
              ⟨k, hk, rfl, hop, opnd_mem h2 hk 0, opnd_lt h2 hRB hk 0⟩
          · exact Relation.ReflTransGen.single
              ⟨k, hk, rfl, hop, opnd_mem h2 hk 1, opnd_lt h2 hRB hk 1⟩
          · intro u hu
            obtain ⟨_, _, w, hw, _, huw⟩ := (orIn_gate C k u).mp hu
            rw [hin] at hw
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
            rcases hw with rfl | rfl
            · exact Finset.mem_union_left _ huw
            · exact Finset.mem_union_right _ huw
          · intro ha hb
            exact ⟨k, rfl, hk, hop, ha, hb⟩
        · left
          have hemp : orIn n C (n + k) = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro u hu
            obtain ⟨h1, h2', _⟩ := (orIn_gate C k u).mp hu
            exact hg ⟨h1, h2'⟩
          rw [hemp]
          simp
    have hcnt := count (orIn n C) (Relation.ReflTransGen (OrStep n C))
      (fun w => ∃ k, w = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
        (orIn n C (opnd C k 0)).Nonempty ∧ (orIn n C (opnd C k 1)).Nonempty)
      (fun w => Relation.ReflTransGen.refl) (fun a b c h1 h2 => h1.trans h2) hcase
      ((T.image (fun d => opnd C d (qf d))).sup id + 1) (T.image (fun d => opnd C d (qf d)))
      (fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := id) hw))
    refine le_trans (Finset.card_le_card hLsub) (le_trans hcnt ?_)
    refine Nat.add_le_add Finset.card_image_le ?_
    refine le_trans (Finset.card_le_card (t := M.image (fun k => n + k)) ?_)
      Finset.card_image_le
    intro h hh
    simp only [Finset.mem_filter] at hh
    obtain ⟨_, ⟨k, rfl, hk, hop, h0, h1⟩, w, hw, hr⟩ := hh
    obtain ⟨d, hdT, rfl⟩ := Finset.mem_image.mp hw
    have hd := ((hT d).mp hdT).1
    have hl := mem_lam G C h2 hRB k hk hop h0 h1 d hd (qf d) c (hqf d hdT) hr
    exact Finset.mem_image.mpr ⟨k, (hM k).mpr ⟨hl.1, d, hd, qf d, hqf d hdT, hl.2⟩, rfl⟩
  · intro hne
    have := hTne hne
    omega
  · intro hne hmax
    have hT1 := hTne hne
    by_cases hT2 : 2 ≤ T.card
    · omega
    · have hT1' : T.card = 1 := by omega
      obtain ⟨a, hTa⟩ := Finset.card_eq_one.mp hT1'
      have haT : a ∈ T := by rw [hTa]; exact Finset.mem_singleton_self a
      have hd := ((hT a).mp haT).1
      have hs := hqf a haT
      -- every gate of M is reached from the one root
      have hroot : ∀ h ∈ M,
          Relation.ReflTransGen (OrStep n C) (opnd C a (qf a)) (n + h) := by
        intro h hh
        obtain ⟨_, a', ha', b', hs', hor⟩ := (hM h).mp hh
        have ha'T : a' ∈ T := (hT a').mpr ⟨ha', b', hs'⟩
        rw [hTa, Finset.mem_singleton] at ha'T
        subst ha'T
        have hb : b' = qf a' := huniq a' ha' b' (qf a') hs' hs
        rw [hb] at hor
        exact (orReaches_reach h _ hor).1
      have hMne : M.Nonempty := by
        obtain ⟨X, hX⟩ := hne
        obtain ⟨k, hk, _⟩ := hBc X hX
        exact ⟨k, hk⟩
      obtain ⟨k1, hk1⟩ := hMne
      have hne2 : ∀ p, p ∈ {w : ℕ | ∃ h ∈ M, w = n + h} → ∀ w1,
          Relation.ReflTransGen (OrStep n C) w1 p → (orIn n C w1).Nonempty := by
        rintro p ⟨h, hh, rfl⟩ w1 hr
        obtain ⟨u, hu⟩ := lam_ne G C h2 hRB h ((hM h).mp hh).1
        exact ⟨u, orIn_mono hr hu⟩
      have hbr := top_branch (OrStep n C)
        (fun w w' hst => by obtain ⟨k, _, rfl, _, _, hlt⟩ := hst; exact hlt)
        {w : ℕ | ∃ h ∈ M, w = n + h} (opnd C a (qf a))
        (by
          intro w hrw hw w1 w2 hst1 hst2 hp hq
          obtain ⟨p, hp, hrp⟩ := hp
          obtain ⟨q, hq, hrq⟩ := hq
          have hn1 := hne2 p hp w1 hrp
          have hn2 := hne2 q hq w2 hrq
          obtain ⟨k, hk, rfl, hop, hin1, _⟩ := hst1
          obtain ⟨k', _, e, _, hin2, _⟩ := hst2
          have hkk : k' = k := by omega
          subst hkk
          by_contra hneq
          apply hw
          have hin := inputs_eq h2 hk
          rw [hin] at hin1 hin2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1 hin2
          have h01 : (orIn n C (opnd C k' 0)).Nonempty ∧ (orIn n C (opnd C k' 1)).Nonempty := by
            rcases hin1 with e1 | e1 <;> rcases hin2 with e2 | e2
            · exact absurd (e1.trans e2.symm) hneq
            · exact ⟨e1 ▸ hn1, e2 ▸ hn2⟩
            · exact ⟨e2 ▸ hn2, e1 ▸ hn1⟩
            · exact absurd (e1.trans e2.symm) hneq
          have hl := mem_lam G C h2 hRB k' hk hop h01.1 h01.2 a hd (qf a) c hs hrw
          exact ⟨k', (hM k').mpr ⟨hl.1, a, hd, qf a, hs, hl.2⟩, rfl⟩)
        (opnd C a (qf a)) Relation.ReflTransGen.refl
        ⟨n + k1, ⟨k1, hk1, rfl⟩, hroot k1 hk1⟩
        (by rintro p ⟨h, hh, rfl⟩; exact hroot h hh)
      obtain ⟨_, ⟨k0, hk0, rfl⟩, hall⟩ := hbr
      have hX0 : orIn n C (n + k0) ∉ Bc := by
        intro hin
        obtain ⟨X'', hX'', hns⟩ := hmax _ hin
        obtain ⟨k'', hk'', rfl⟩ := hBc X'' hX''
        exact hns (orIn_mono (hall (n + k'') ⟨k'', hk'', rfl⟩))
      have hsub : Bc ⊆ (M.erase k0).image (fun k => orIn n C (n + k)) := by
        intro X hX
        obtain ⟨k, hk, rfl⟩ := hBc X hX
        refine Finset.mem_image.mpr ⟨k, Finset.mem_erase.mpr ⟨?_, hk⟩, rfl⟩
        rintro rfl
        exact hX0 hX
      have h5 := le_trans (Finset.card_le_card hsub) Finset.card_image_le
      have h6 := Finset.card_erase_add_one hk0
      omega

end PEqualNP.Outside.L_meta_1652

theorem PEqualNP.Outside.L_meta_1652 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → ∀ (c : Fin n) (T M : Finset ℕ) (L : Finset (Fin n)), (∀ t, t ∈ T ↔ t ∈ PEqualNP.TopForm.tops G C ∧ ∃ p : Fin 2, PEqualNP.TopForm.side (n := n) C t (1 - p) = {c}) → (∀ h, h ∈ M ↔ h ∈ PEqualNP.TopForm.lam G C ∧ ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, PEqualNP.TopForm.side (n := n) C a (1 - b) = {c} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h) → (∀ v, v ∈ L ↔ ∃ d ∈ PEqualNP.TopForm.tops G C, ∃ q : Fin 2, PEqualNP.TopForm.side (n := n) C d (1 - q) = {c} ∧ v ∈ PEqualNP.TopForm.side (n := n) C d q) → ∀ (Bc : Finset (Finset (Fin n))), (∀ X ∈ Bc, ∃ k ∈ M, PEqualNP.TopForm.orIn n C (n + k) = X) → (∀ w ∈ L, G.Adj c w ∧ s(c, w) ∈ PEqualNP.TopForm.starEdges G C) ∧ L.card ≤ T.card + M.card ∧ (Bc.Nonempty → Bc.card + 1 ≤ T.card + M.card) ∧ (Bc.Nonempty → (∀ X' ∈ Bc, ∃ X'' ∈ Bc, ¬ X'' ⊆ X') → Bc.card + 2 ≤ T.card + M.card) := by
  intro n G _ C h4 _ hL _ c T M L hT hM hLd Bc hBc
  exact PEqualNP.Outside.L_meta_1652.main n G C h4 hL c T M L hT hM hLd Bc hBc
