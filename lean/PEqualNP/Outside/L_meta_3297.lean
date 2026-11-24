import Mathlib
import PEqualNP.Defs

-- The wire, OR closure and cone lemmas (from stepWire to orReaches_reach) are those of the merged
-- file L_meta_1491.lean of this repository, with the namespace changed. New are the lemmas on the
-- substituted circuit: the semantic invariant along the wires and the inclusion of live gates.

namespace PEqualNP.Outside.L_meta_3297

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


-- The factor substitution itself.

open PEqualNP.FactorSubst PEqualNP.TopForm

lemma subst_length (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n c sigma).gates.length = C.gates.length := by
  simp [substReads]

lemma gateAt_subst (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (substReads C n c sigma) j =
      ⟨(gateAt C j).op, (gateAt C j).inputs.map fun i => if i = n + c then sigma j else i⟩ := by
  rw [gateAt_eq (by rw [subst_length]; exact hj), gateAt_eq hj]
  simp [substReads]

lemma subst_output (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n c sigma).output = C.output := rfl

lemma mem_subst_inputs {C : Circuit} {n c : ℕ} {sigma : ℕ → ℕ} {j : ℕ} (hj : j < C.gates.length)
    {i' : ℕ} (h : i' ∈ (gateAt (substReads C n c sigma) j).inputs) :
    ∃ i ∈ (gateAt C j).inputs, i' = if i = n + c then sigma j else i := by
  rw [gateAt_subst C n c sigma hj] at h
  simp only [List.mem_map] at h
  obtain ⟨i, hi, e⟩ := h
  exact ⟨i, hi, e.symm⟩

lemma subst_inputs_of {C : Circuit} {n c : ℕ} {sigma : ℕ → ℕ} {j : ℕ} (hj : j < C.gates.length)
    {i : ℕ} (hi : i ∈ (gateAt C j).inputs) :
    (if i = n + c then sigma j else i) ∈ (gateAt (substReads C n c sigma) j).inputs := by
  rw [gateAt_subst C n c sigma hj]
  exact List.mem_map.mpr ⟨i, hi, rfl⟩

-- Facts about the OR closure.

lemma orReaches_self {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length) :
    OrReaches n C (n + k) k :=
  (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩

lemma orClosure_iff {n : ℕ} {C : Circuit} {c k : ℕ} :
    k ∈ orClosure n C c ↔ k < C.gates.length ∧ k ≠ c ∧ OrReaches n C (n + k) c := by
  simp [orClosure]

lemma orClosure_or {n : ℕ} {C : Circuit} {c k : ℕ} (h : k ∈ orClosure n C c) :
    (gateAt C k).op = GateOp.or := by
  obtain ⟨_, hne, hr⟩ := orClosure_iff.mp h
  obtain ⟨_, h3⟩ := (orReaches_iff n C k c).mp hr
  rcases h3 with e | ⟨hop, _⟩
  · exact absurd e.symm hne
  · exact hop

lemma orClosure_gt {n : ℕ} {C : Circuit} {c k : ℕ} (h : k ∈ orClosure n C c) : c < k := by
  obtain ⟨_, hne, hr⟩ := orClosure_iff.mp h
  have := orStep_le (orReaches_reach c (n + k) hr).1
  omega

lemma val_closure {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w g : ℕ}
    (hr : OrReaches n C w g) (hv : val C x (n + g) = true) : val C x w = true :=
  orStep_up hx (orReaches_reach g w hr).1 hv

lemma val_and2 {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {k p q : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and)
    (hin : (gateAt C k).inputs = [p, q]) (hp : p < n + k) (hq : q < n + k) :
    val C x (n + k) = (val C x p && val C x q) := by
  rw [val_gate hx hk, hop, hin]
  simp [GateOp.eval, hp, hq]

-- Main semantic invariant.

section Semantic

variable {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ}

def InO (n : ℕ) (C : Circuit) (c w : ℕ) : Prop := ∃ k ∈ orClosure n C c, w = n + k

theorem semantic (hAO : IsAO2 n C) (hc : c < C.gates.length)
    (hcand : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b)
    (hfront : ∀ g ∈ frontier n C c, (gateAt C g).op = GateOp.and → ∀ u y : ℕ,
      ((gateAt C g).inputs = [u, y] ∨ (gateAt C g).inputs = [y, u]) →
      (∃ w ∈ insert c (orClosure n C c), u = n + w) →
      (∀ w' ∈ insert c (orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ readers n C c,
        (r = g ∨ OrReaches n C u r) →
        (sigma r = b → ∀ x : Fin n → Bool, wireVal n C y x = true → wireVal n C a x = true) ∧
        (sigma r = a → ∀ x' : Fin n → Bool, wireVal n C y x' = true → wireVal n C b x' = true))
    (z : Fin n → Bool) :
    ∀ w, (¬ InO n C c w → val (substReads C n c sigma) (List.ofFn z) w =
        val C (List.ofFn z) w) ∧
      (InO n C c w → (val C (List.ofFn z) w = true →
          val (substReads C n c sigma) (List.ofFn z) w = true) ∧
        (val (substReads C n c sigma) (List.ofFn z) w = true →
          val C (List.ofFn z) w = true ∨ ∃ r ∈ readers n C c, OrReaches n C w r ∧
            val C (List.ofFn z) (sigma r) = true)) := by
  obtain ⟨hAnd, hRB, hLen⟩ := hAO
  set C' := substReads C n c sigma with hC'
  set x := List.ofFn z with hxdef
  have hx : x.length = n := by simp [hxdef]
  have hlen' : C'.gates.length = C.gates.length := subst_length C n c sigma
  have hab : a < n + c ∧ b < n + c := by
    have h1 := hRB c hc a (by rw [hcin]; simp)
    have h2 := hRB c hc b (by rw [hcin]; simp)
    exact ⟨h1, h2⟩
  have hvc : val C x (n + c) = (val C x a && val C x b) := by
    rw [val_gate hx hc, hcand, hcin]
    simp [GateOp.eval, hab.1, hab.2]
  -- a reader of c reads it below itself, and sigma of a reader is below c
  have hreader {r : ℕ} (hr : r < C.gates.length) (hin : n + c ∈ (gateAt C r).inputs) :
      r ∈ readers n C c ∧ c < r ∧ (sigma r = a ∨ sigma r = b) := by
    have hrd : r ∈ readers n C c := by simp [readers, hr, hin]
    have := hRB r hr _ hin
    exact ⟨hrd, by omega, hsig r hrd⟩
  have notInO_lt {w : ℕ} (hw : w < n + c) : ¬ InO n C c w := by
    rintro ⟨k, hk, rfl⟩
    have := orClosure_gt hk
    omega
  have InO_c : ¬ InO n C c (n + c) := by
    rintro ⟨k, hk, e⟩
    have := orClosure_gt hk
    omega
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  by_cases hwn : w < n
  · have e1 : val C' x w = val C x w := by rw [val_input hx hwn, val_input hx hwn]
    refine ⟨fun _ => e1, fun hO => ?_⟩
    obtain ⟨k, _, rfl⟩ := hO
    omega
  by_cases hwl : n + C.gates.length ≤ w
  · have e1 : val C' x w = false := val_ge hx (by rw [hlen']; exact hwl)
    have e2 : val C x w = false := val_ge hx hwl
    refine ⟨fun _ => by rw [e1, e2], fun _ => ⟨(fun h => by rw [e2] at h; cases h),
      (fun h => by rw [e1] at h; cases h)⟩⟩
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have hk : k < C.gates.length := by omega
  have hk' : k < C'.gates.length := by rw [hlen']; exact hk
  -- values read by gate k in C' and in C
  have hval' : val C' x (n + k) = (gateAt C k).op.eval
      (((gateAt C k).inputs.map fun i => if i = n + c then sigma k else i).map fun i =>
        if i < n + k then val C' x i else false) := by
    rw [val_gate hx hk', gateAt_subst C n c sigma hk]
  have hval : val C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then val C x i else false) := val_gate hx hk
  -- inputs of gate k are earlier wires
  have hrb : ∀ i ∈ (gateAt C k).inputs, i < n + k := hRB k hk
  -- the IH for the wires gate k reads
  have IHeq : ∀ i ∈ (gateAt C k).inputs, ¬ InO n C c i → i ≠ n + c →
      val C' x i = val C x i := fun i hi h1 _ => (ih i (hrb i hi)).1 h1
  by_cases hkO : k ∈ orClosure n C c
  · -- gate k is an OR of the closure
    have hop := orClosure_or hkO
    have hOk : InO n C c (n + k) := ⟨k, hkO, rfl⟩
    refine ⟨fun h => absurd hOk h, fun _ => ⟨?_, ?_⟩⟩
    · intro hv
      rw [val_or hx hk hop] at hv
      obtain ⟨i, hi, hlt, hvi⟩ := hv
      have hgk := gateAt_mem (C := C) hk
      have hop' : (gateAt C' k).op = GateOp.or := by rw [gateAt_subst C n c sigma hk]; exact hop
      rw [val_or hx hk' hop']
      by_cases hic : i = n + c
      · obtain ⟨_, hck, hsk⟩ := hreader hk (hic ▸ hi)
        refine ⟨sigma k, by have := subst_inputs_of (n := n) (c := c) (sigma := sigma) hk hi; simpa [hic] using this, ?_, ?_⟩
        · rcases hsk with h | h <;> rw [h] <;> omega
        · have hs : sigma k < n + c := by rcases hsk with h | h <;> rw [h] <;> omega
          rw [(ih _ (by omega)).1 (notInO_lt hs)]
          rw [hic, hvc] at hvi
          simp only [Bool.and_eq_true] at hvi
          rcases hsk with h | h <;> rw [h]
          · exact hvi.1
          · exact hvi.2
      · refine ⟨i, by have := subst_inputs_of (n := n) (c := c) (sigma := sigma) hk hi; simpa [hic] using this, hlt, ?_⟩
        by_cases hiO : InO n C c i
        · exact ((ih i hlt).2 hiO).1 hvi
        · rw [(ih i hlt).1 hiO]; exact hvi
    · intro hv
      have hop' : (gateAt C' k).op = GateOp.or := by rw [gateAt_subst C n c sigma hk]; exact hop
      rw [val_or hx hk' hop'] at hv
      obtain ⟨i', hi', hlt, hvi⟩ := hv
      obtain ⟨i, hi, e⟩ := mem_subst_inputs hk hi'
      by_cases hic : i = n + c
      · rw [if_pos hic] at e
        subst e
        obtain ⟨hrd, _, hsk⟩ := hreader hk (hic ▸ hi)
        have hs : sigma k < n + c := by rcases hsk with h | h <;> rw [h] <;> omega
        right
        refine ⟨k, hrd, orReaches_self hk, ?_⟩
        rw [← (ih _ hlt).1 (notInO_lt hs)]
        exact hvi
      · rw [if_neg hic] at e
        subst e
        by_cases hiO : InO n C c i'
        · rcases ((ih i' hlt).2 hiO).2 hvi with h | ⟨r, hrd, hrr, hvr⟩
          · left
            rw [val_or hx hk hop]
            exact ⟨i', hi, hlt, h⟩
          · right
            exact ⟨r, hrd, (orReaches_iff n C k r).mpr ⟨hk, Or.inr ⟨hop, i', hi, hlt, hrr⟩⟩, hvr⟩
        · left
          rw [val_or hx hk hop]
          exact ⟨i', hi, hlt, by rw [← (ih i' hlt).1 hiO]; exact hvi⟩
  · have hnO : ¬ InO n C c (n + k) := by
      rintro ⟨k2, hk2, e⟩
      have : k2 = k := by omega
      subst this
      exact hkO hk2
    refine ⟨fun _ => ?_, fun h => absurd h hnO⟩
    -- does gate k read c or a gate of the closure?
    by_cases hread : ∃ w ∈ insert c (orClosure n C c), n + w ∈ (gateAt C k).inputs
    · by_cases hkc : k = c
      · -- gate c reads a and b only
        exfalso
        subst hkc
        obtain ⟨w, hw, hwin⟩ := hread
        rw [hcin] at hwin
        rcases Finset.mem_insert.mp hw with rfl | hwO
        · simp at hwin; omega
        · have := orClosure_gt hwO
          simp at hwin; omega
      have hfr : k ∈ PEqualNP.FactorSubst.frontier n C c := by
        simp only [PEqualNP.FactorSubst.frontier, Finset.mem_filter, Finset.mem_range]
        exact ⟨hk, hkc, hkO, hread⟩
      -- gate k is an AND gate: an OR gate reading the closure would be in it
      have hand : (gateAt C k).op = GateOp.and := by
        rcases hAnd _ (gateAt_mem hk) with h | h
        · exact h
        · exfalso
          apply hkO
          obtain ⟨w, hw, hwin⟩ := hread
          refine orClosure_iff.mpr ⟨hk, hkc, ?_⟩
          refine (orReaches_iff n C k c).mpr ⟨hk, Or.inr ⟨h, n + w, hwin, hrb _ hwin, ?_⟩⟩
          rcases Finset.mem_insert.mp hw with rfl | hwO
          · exact orReaches_self hc
          · exact (orClosure_iff.mp hwO).2.2
      have h2 := hLen _ (gateAt_mem hk)
      obtain ⟨p, q, hpq⟩ : ∃ p q, (gateAt C k).inputs = [p, q] := by
        match h : (gateAt C k).inputs, h2 with
        | [p, q], _ => exact ⟨p, q, rfl⟩
      obtain ⟨w, hw, hwin⟩ := hread
      -- u is the operand in the closure, y the other one
      obtain ⟨u, y, huy, hu⟩ : ∃ u y, ((gateAt C k).inputs = [u, y] ∨
          (gateAt C k).inputs = [y, u]) ∧ u = n + w := by
        rw [hpq] at hwin
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hwin
        rcases hwin with e | e
        · exact ⟨p, q, Or.inl hpq, e.symm⟩
        · exact ⟨q, p, Or.inr hpq, e.symm⟩
      obtain ⟨hy, hrs⟩ := hfront k hfr hand u y huy ⟨w, hw, hu⟩
      have hmem : u ∈ (gateAt C k).inputs ∧ y ∈ (gateAt C k).inputs := by
        rcases huy with e | e <;> rw [e] <;> simp
      have hult := hrb u hmem.1
      have hylt := hrb y hmem.2
      have hyc : y ≠ n + c := hy c (Finset.mem_insert_self _ _)
      have hyO : ¬ InO n C c y := by
        rintro ⟨k2, hk2, e⟩
        exact hy k2 (Finset.mem_insert_of_mem hk2) e
      have hvy : val C' x y = val C x y := (ih y hylt).1 hyO
      -- the AND value as the AND of the two operands, in both circuits
      have hAndC : val C x (n + k) = (val C x u && val C x y) := by
        rcases huy with e | e
        · exact val_and2 hx hk hand e hult hylt
        · rw [val_and2 hx hk hand e hylt hult, Bool.and_comm]
      have hinC' : ∀ p q, (gateAt C k).inputs = [p, q] → (gateAt C' k).inputs =
          [if p = n + c then sigma k else p, if q = n + c then sigma k else q] := by
        intro p q e
        rw [gateAt_subst C n c sigma hk, e]
        rfl
      have hand' : (gateAt C' k).op = GateOp.and := by
        rw [gateAt_subst C n c sigma hk]; exact hand
      -- the value C' reads for u
      set u' := if u = n + c then sigma k else u with hu'
      have hu'lt : u' < n + k := by
        by_cases e : u = n + c
        · have hs := (hreader hk (e ▸ hmem.1)).2.2
          simp only [hu', if_pos e]
          rcases hs with h | h <;> rw [h] <;> omega
        · simp only [hu', if_neg e]; exact hult
      have hAndC' : val C' x (n + k) = (val C' x u' && val C' x y) := by
        rcases huy with e | e
        · have h3 := hinC' u y e
          rw [if_neg hyc] at h3
          exact val_and2 hx hk' hand' h3 hu'lt hylt
        · have h3 := hinC' y u e
          rw [if_neg hyc] at h3
          rw [val_and2 hx hk' hand' h3 hylt hu'lt, Bool.and_comm]
      rw [hAndC, hAndC', hvy]
      have toWire : ∀ v, wireVal n C v z = val C x v := fun v => rfl
      by_cases huc : u = n + c
      · -- k reads c directly: the factor sigma k replaces c
        obtain ⟨hrd, _, hsk⟩ := hreader hk (huc ▸ hmem.1)
        have hs : sigma k < n + c := by rcases hsk with h | h <;> rw [h] <;> omega
        have hu'e : u' = sigma k := by simp [hu', huc]
        rw [hu'e, (ih _ (by omega)).1 (notInO_lt hs), huc, hvc]
        have hr := hrs k hrd (Or.inl rfl)
        rcases hsk with h | h
        · rw [h]
          have himp : val C x y = true → val C x b = true := hr.2 h z
          cases hya : val C x y
          · simp
          · rw [himp hya]; simp
        · rw [h]
          have himp : val C x y = true → val C x a = true := hr.1 h z
          cases hya : val C x y
          · simp
          · rw [himp hya]; simp
      · -- k reads an OR gate of the closure: the sandwich
        have hu'e : u' = u := by simp [hu', huc]
        rw [hu'e]
        have hwO : w ∈ orClosure n C c := by
          rcases Finset.mem_insert.mp hw with rfl | h
          · exact absurd hu huc
          · exact h
        have huO : InO n C c u := ⟨w, hwO, hu⟩
        have hlo := ((ih u hult).2 huO).1
        have hhi := ((ih u hult).2 huO).2
        have hcu : val C x (n + c) = true → val C x u = true :=
          val_closure hx (hu ▸ (orClosure_iff.mp hwO).2.2)
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          rcases hhi h1 with h | ⟨r, hrd, hrr, hvr⟩
          · exact h
          · apply hcu
            rw [hvc, Bool.and_eq_true]
            have hr := hrs r hrd (Or.inr hrr)
            rcases hsig r hrd with e | e
            · exact ⟨e ▸ hvr, hr.2 e z h2⟩
            · exact ⟨hr.1 e z h2, e ▸ hvr⟩
        · rintro ⟨h1, h2⟩
          exact ⟨hlo h1, h2⟩
    · -- gate k reads neither c nor the closure: same gate, same inputs
      have hsame : ∀ i ∈ (gateAt C k).inputs, i ≠ n + c ∧ ¬ InO n C c i := by
        intro i hi
        refine ⟨fun e => hread ⟨c, Finset.mem_insert_self _ _, e ▸ hi⟩, ?_⟩
        rintro ⟨k2, hk2, rfl⟩
        exact hread ⟨k2, Finset.mem_insert_of_mem hk2, hi⟩
      rw [hval', hval]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp_apply, if_neg (hsame i hi).1]
      by_cases hlt : i < n + k
      · rw [if_pos hlt, if_pos hlt, (ih i hlt).1 (hsame i hi).2]
      · rw [if_neg hlt, if_neg hlt]

end Semantic

-- Cones of the substituted circuit.

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) :
    InCone n C j k → InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro h2
  obtain ⟨hk, m, hm, hin, h3⟩ := (inCone_iff n C j k).mp h2
  refine (inCone_iff n C i k).mpr ⟨hk, m, hm, hin, Or.inr ?_⟩
  rcases h3 with rfl | h3
  · exact h1
  · exact ih m hm h3

lemma inCone_direct {n : ℕ} {C : Circuit} {i k : ℕ} (hk : k < C.gates.length) (hik : i < k)
    (hin : n + i ∈ (gateAt C k).inputs) : InCone n C i k :=
  (inCone_iff n C i k).mpr ⟨hk, i, hik, hin, Or.inl rfl⟩

theorem cone_subst {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ}
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ m j, InCone n (substReads C n c sigma) j m → InCone n C j m ∧ j ≠ c := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro j h
  obtain ⟨hm, k, hkm, hin, h3⟩ := (inCone_iff n _ j m).mp h
  rw [subst_length] at hm
  obtain ⟨i, hi, e⟩ := mem_subst_inputs hm hin
  have hab : a < n + c ∧ b < n + c :=
    ⟨hRB c hc a (by rw [hcin]; simp), hRB c hc b (by rw [hcin]; simp)⟩
  -- the edge m → k exists in C, directly or through c
  have hedge : InCone n C k m ∧ k ≠ c := by
    by_cases hic : i = n + c
    · rw [if_pos hic] at e
      have hrd : m ∈ readers n C c := by simp [readers, hm, ← hic, hi]
      have hcm : c < m := by have := hRB m hm i hi; omega
      have hs := hsig m hrd
      have hkc : k < c := by rcases hs with h | h <;> rw [h] at e <;> omega
      refine ⟨inCone_trans (j := c) ?_ (inCone_direct hm hcm (hic ▸ hi)), by omega⟩
      apply inCone_direct hc hkc
      rw [hcin]
      rcases hs with h | h <;> rw [h] at e <;> simp [e]
    · rw [if_neg hic] at e
      refine ⟨inCone_direct hm hkm (e ▸ hi), ?_⟩
      intro hkc
      exact hic (by rw [← e, hkc])
  rcases h3 with rfl | h3
  · exact hedge
  · obtain ⟨h4, h5⟩ := ih k hkm j h3
    exact ⟨inCone_trans h4 hedge.1, h5⟩

theorem live_subst {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ}
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b)
    (hout : C.output ≠ n + c) :
    liveGates n (substReads C n c sigma) ⊆ (liveGates n C).erase c := by
  intro j hj
  simp only [liveGates, Finset.mem_filter, Finset.mem_range, subst_length, subst_output] at hj
  obtain ⟨hjl, hno, h⟩ := hj
  rw [Finset.mem_erase]
  simp only [liveGates, Finset.mem_filter, Finset.mem_range]
  rcases h with e | h
  · refine ⟨?_, hjl, hno, Or.inl e⟩
    intro hjc
    apply hout
    omega
  · obtain ⟨h1, h2⟩ := cone_subst hRB hc hcin hsig _ _ h
    exact ⟨h2, hjl, hno, Or.inr h1⟩

end PEqualNP.Outside.L_meta_3297

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.FactorSubst
  PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.L_meta_3297 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C := by
  intro n C c a b sigma hAO hc hcand hcin hsig hfront _ hout hlive
  refine ⟨?_, ?_⟩
  · intro k _ _ hkO z
    refine (PEqualNP.Outside.L_meta_3297.semantic hAO hc hcand hcin hsig hfront z (n + k)).1 ?_
    rintro ⟨k2, hk2, e⟩
    have : k2 = k := by omega
    subst this
    exact hkO hk2
  · have hsub := PEqualNP.Outside.L_meta_3297.live_subst hAO.2.1 hc hcin hsig
      (hout c (Finset.mem_insert_self _ _))
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hlive] at h1
    have h2 := Finset.card_pos.mpr ⟨c, hlive⟩
    unfold liveSize
    omega
