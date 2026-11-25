import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6159

namespace Table6159Upper

open PEqualNP.CircuitLowerBounds

theorem upper :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 4 => (855 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  -- Union of the rectangles {0,1} × {0,2} and {0,2} × {0,1}.
  let C : Circuit := ⟨[
    ⟨.or, [0,1]⟩, ⟨.or, [4,6]⟩, ⟨.and, [8,9]⟩,
    ⟨.or, [0,2]⟩, ⟨.or, [4,5]⟩, ⟨.and, [11,12]⟩,
    ⟨.or, [10,13]⟩], 14⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · intro g hg
    change g ∈ C.gates at hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact ⟨Or.inl rfl, le_rfl⟩ | exact ⟨Or.inr rfl, le_rfl⟩
  · change ∀ u v : Fin 4,
      C.eval (PEqualNP.Represents.oneEach u v) = (855 : ℕ).testBit (4 * u.val + v.val)
    decide +kernel

end Table6159Upper

namespace Table6159Finite

def raw : Finset ℕ := {15,240,3840,4369,8738,17476}

def Separates (S : Finset ℕ) : Prop :=
  ∀ p q : Fin 16, (855 : ℕ).testBit p.val = true → (855 : ℕ).testBit q.val = false →
    ∃ x ∈ S, x.testBit p.val = true ∧ x.testBit q.val = false

instance (S : Finset ℕ) : Decidable (Separates S) := by
  unfold Separates
  infer_instance

def emit (S : Finset ℕ) (allow : Bool) (a b z : ℕ) : Finset (Finset ℕ × Bool) :=
  if a = b then ∅
  else if z ∈ S then ∅
  else
    Finset.filter (fun t : Finset ℕ × Bool => Separates t.1)
      (insert (insert z ((S.erase a).erase b), allow)
        (if allow then {(insert z (S.erase b),false),(insert z (S.erase a),false)} else ∅))

def next (S : Finset ℕ) (allow : Bool) : Finset (Finset ℕ × Bool) :=
  S.biUnion fun a => S.biUnion fun b =>
    emit S allow a b (a &&& b) ∪ emit S allow a b (a ||| b)

private theorem from_emit {S : Finset ℕ} {allow : Bool} {a b z : ℕ}
    {t : Finset ℕ × Bool} (ha : a ∈ S) (hb : b ∈ S)
    (op : z = (a &&& b) ∨ z = (a ||| b))
    (yes : t ∈ emit S allow a b z) : t ∈ next S allow := by
  change t ∈ S.biUnion (fun a => S.biUnion (fun b =>
    emit S allow a b (a &&& b) ∪ emit S allow a b (a ||| b)))
  refine Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_biUnion.mpr ⟨b,hb,?_⟩⟩
  apply Finset.mem_union.mpr
  rcases op with e | e
  · rw [e] at yes
    exact Or.inl yes
  · rw [e] at yes
    exact Or.inr yes

private theorem emit_of_keep_rule {S : Finset ℕ} {allow : Bool} {a b z : ℕ}
    {t : Finset ℕ × Bool} (ne : a ≠ b) (fresh : z ∉ S)
    (rule : t ∈ insert (insert z ((S.erase a).erase b), allow)
      (if allow then {(insert z (S.erase b),false),(insert z (S.erase a),false)}
       else (∅ : Finset (Finset ℕ × Bool))))
    (sep : Separates t.1) : t ∈ emit S allow a b z := by
  simp only [emit,ite_eq_right ne,ite_eq_right fresh]
  exact Finset.mem_filter.mpr ⟨rule,sep⟩

theorem mem_next_drop_both {S : Finset ℕ} {allow : Bool} {a b z : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (ne : a ≠ b) (fresh : z ∉ S)
    (op : z = (a &&& b) ∨ z = (a ||| b))
    (sep : Separates (insert z ((S.erase a).erase b))) :
    (insert z ((S.erase a).erase b),allow) ∈ next S allow :=
  from_emit ha hb op (emit_of_keep_rule ne fresh (Finset.mem_insert_self _ _) sep)

theorem mem_next_keep_a {S : Finset ℕ} {allow : Bool} {a b z : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (ne : a ≠ b) (fresh : z ∉ S)
    (op : z = (a &&& b) ∨ z = (a ||| b)) (allowed : allow = true)
    (sep : Separates (insert z (S.erase b))) :
    (insert z (S.erase b),false) ∈ next S allow := by
  apply from_emit ha hb op
  refine emit_of_keep_rule ne fresh ?_ sep
  apply Finset.mem_insert.mpr
  right
  rw [ite_eq_left allowed]
  exact Finset.mem_insert_self _ _

theorem mem_next_keep_b {S : Finset ℕ} {allow : Bool} {a b z : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (ne : a ≠ b) (fresh : z ∉ S)
    (op : z = (a &&& b) ∨ z = (a ||| b)) (allowed : allow = true)
    (sep : Separates (insert z (S.erase a))) :
    (insert z (S.erase a),false) ∈ next S allow := by
  apply from_emit ha hb op
  refine emit_of_keep_rule ne fresh ?_ sep
  apply Finset.mem_insert.mpr
  right
  rw [ite_eq_left allowed]
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))

def layerOne : Finset (Finset ℕ × Bool) :=
  {({15,240,3840,4369,8738,20292}, false),
   ({15,240,3840,4369,8738,21845}, false),
   ({15,240,3840,4369,8946,17476}, false),
   ({15,240,3840,4369,13107,17476}, false),
   ({15,240,3855,4369,8738,17476}, false),
   ({15,240,4369,8738,17476,20292}, false),
   ({15,240,4369,8738,20292}, true),
   ({15,255,3840,4369,8738,17476}, false),
   ({15,3840,4369,8738,8946,17476}, false),
   ({15,3840,4369,8946,17476}, true)}

def layerTwo : Finset (Finset ℕ × Bool) :=
  {({15,240,3840,13107,21845}, false),
   ({15,240,4369,8946,20292}, false),
   ({15,240,4369,13107,20292}, false),
   ({15,255,4369,8738,20292}, false),
   ({15,3840,4369,8946,20292}, false),
   ({15,3840,4369,8946,21845}, false),
   ({15,3855,4369,8946,17476}, false),
   ({15,4369,8738,8946,20292}, false),
   ({15,4369,8946,17476,20292}, false),
   ({15,4369,8946,20292}, true),
   ({255,3855,4369,8738,17476}, false)}

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem first_layer : next raw true = layerOne := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem second_layer : layerOne.biUnion (fun s => next s.1 s.2) = layerTwo := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem third_layer : layerTwo.biUnion (fun s => next s.1 s.2) = ∅ := by decide +kernel

theorem no_third {s t u : Finset ℕ × Bool}
    (first : s ∈ next raw true) (second : t ∈ next s.1 s.2)
    (third : u ∈ next t.1 t.2) : False := by
  rw [first_layer] at first
  have tLayer : t ∈ layerOne.biUnion (fun v => next v.1 v.2) :=
    Finset.mem_biUnion.mpr ⟨s,first,second⟩
  rw [second_layer] at tLayer
  have uLayer : u ∈ layerTwo.biUnion (fun v => next v.1 v.2) :=
    Finset.mem_biUnion.mpr ⟨t,tLayer,third⟩
  rw [third_layer] at uLayer
  exact Finset.notMem_empty _ uLayer

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem raw_minimal_checked : ∀ S : ↥raw.powerset, Separates S.val → S.val = raw := by
  decide +kernel

theorem raw_subset_separating (S : Finset ℕ) (subset : S ⊆ raw) (sep : Separates S) :
    S = raw := raw_minimal_checked ⟨S,Finset.mem_powerset.mpr subset⟩ sep

end Table6159Finite

namespace Table6159Trace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents


def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  change C.gates.getD j ⟨.or, []⟩ = C.gates[j]
  exact List.getD_eq_getElem _ _ hj

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

theorem opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · change (l.map f).all id = true → (l.map g).all id = true
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · change (l.map f).any id = true → (l.map g).any id = true
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

theorem andOrOnly_of_monotone2 {C : Circuit} (h : Monotone2 C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := by
  intro g hg
  have h1 := (h g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [ite_eq_left hi, ite_eq_left hi]
            exact ih i hi
          · rw [ite_eq_right hi, ite_eq_right hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

def t1_bits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => Nat.bit (f 0) (t1_bits (fun i => f (i + 1)) m)

theorem t1_bits_testBit (m : ℕ) : ∀ (f : ℕ → Bool) (i : ℕ),
    (t1_bits f m).testBit i = (decide (i < m) && f i) := by
  induction m with
  | zero => intro f i; simp [t1_bits]
  | succ m ih =>
    intro f i
    cases i with
    | zero => simp [t1_bits]
    | succ i =>
      have e : (t1_bits f (m + 1)).testBit (i + 1) = (t1_bits (fun i => f (i + 1)) m).testBit i :=
        Nat.testBit_bit_succ i _ _
      rw [e, ih]
      simp

theorem t1_bits_ext {f g : ℕ → Bool} {m : ℕ} (h : ∀ k, k < m → f k = g k) :
    t1_bits f m = t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [t1_bits_testBit, t1_bits_testBit]
  by_cases hi : i < m
  · rw [h i hi]
  · simp [hi]

theorem t1_bits_and (f g : ℕ → Bool) (m : ℕ) :
    t1_bits (fun i => f i && g i) m = t1_bits f m &&& t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land, t1_bits_testBit]
  cases (decide (i < m)) <;> cases (f i) <;> cases (g i) <;> rfl

theorem t1_bits_or (f g : ℕ → Bool) (m : ℕ) :
    t1_bits (fun i => f i || g i) m = t1_bits f m ||| t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_lor, t1_bits_testBit]
  cases (decide (i < m)) <;> cases (f i) <;> cases (g i) <;> rfl

theorem t1_bits_false (m : ℕ) : t1_bits (fun _ => false) m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [t1_bits_testBit]

theorem t1_bits_true16 : t1_bits (fun _ => true) 16 = 65535 := by decide

def t1_Step (S : List ℕ) (p : ℕ) : Prop := ∃ a ∈ S, ∃ b ∈ S, p = a &&& b ∨ p = a ||| b

theorem t1_gate_step (S : List ℕ) (R : ℕ → ℕ → Bool) (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2)
    (hR : ∀ i ∈ l, t1_bits (fun k => R k i) 16 ∈ S) (h0 : 0 ∈ S) (h1 : 65535 ∈ S) :
    t1_Step S (t1_bits (fun k => op.eval (l.map (R k))) 16) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval (([] : List ℕ).map (R k))) = fun _ => true := by
        funext k; rfl
      rw [e, t1_bits_true16]
      exact ⟨65535, h1, 65535, h1, Or.inl (by decide)⟩
    · have e : (fun k => GateOp.or.eval (([] : List ℕ).map (R k))) = fun _ => false := by
        funext k; rfl
      rw [e, t1_bits_false]
      exact ⟨0, h0, 0, h0, Or.inr (by decide)⟩
  · have ha := hR a (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval ([a].map (R k))) = fun k => R k a && true := by
        funext k; rfl
      rw [e, t1_bits_and, t1_bits_true16]
      exact ⟨_, ha, 65535, h1, Or.inl rfl⟩
    · have e : (fun k => GateOp.or.eval ([a].map (R k))) = fun k => R k a || false := by
        funext k; rfl
      rw [e, t1_bits_or, t1_bits_false]
      exact ⟨_, ha, 0, h0, Or.inr rfl⟩
  · have ha := hR a (by simp)
    have hb := hR b (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval ([a, b].map (R k))) = fun k => R k a && R k b := by
        funext k
        change (R k a && (R k b && true)) = _
        rw [Bool.and_true]
      rw [e, t1_bits_and]
      exact ⟨_, ha, _, hb, Or.inl rfl⟩
    · have e : (fun k => GateOp.or.eval ([a, b].map (R k))) = fun k => R k a || R k b := by
        funext k
        change (R k a || (R k b || false)) = _
        rw [Bool.or_false]
      rw [e, t1_bits_or]
      exact ⟨_, ha, _, hb, Or.inr rfl⟩
  · simp only [List.length_cons] at hl
    omega


abbrev Gate := Bool × ℕ × ℕ

def result (g : Gate) : ℕ :=
  if g.1 then g.2.1 ||| g.2.2 else g.2.1 &&& g.2.2

def Admissible (W : Finset ℕ) : List Gate → Prop
  | [] => True
  | g :: gs =>
    g.2.1 ∈ W ∧ g.2.2 ∈ W ∧ g.2.1 ≠ g.2.2 ∧ result g ∉ W ∧ Admissible (insert (result g) W) gs

def finish (W : Finset ℕ) (gs : List Gate) : Finset ℕ :=
  gs.foldl (fun U g => insert (result g) U) W

def raw : Finset ℕ := {15, 240, 3840, 4369, 8738, 17476}

private def virtuals (W : Finset ℕ) : Finset ℕ := insert 0 (insert 65535 W)

private theorem virtual_mem {W : Finset ℕ} {v : ℕ} :
    v ∈ virtuals W ↔ v = 0 ∨ v = 65535 ∨ v ∈ W := by
  simp only [virtuals, Finset.mem_insert]

private theorem mem_virtuals {W : Finset ℕ} {v : ℕ} (h : v ∈ W) : v ∈ virtuals W :=
  virtual_mem.mpr (Or.inr (Or.inr h))

private theorem virtual_mono {W W' : Finset ℕ} (ss : W ⊆ W') : virtuals W ⊆ virtuals W' := by
  intro v hv
  apply virtual_mem.mpr
  rcases virtual_mem.mp hv with z | o | m
  · exact Or.inl z
  · exact Or.inr (Or.inl o)
  · exact Or.inr (Or.inr (ss m))

private theorem virtual_bound {W : Finset ℕ} {v : ℕ} (hw : ∀ a ∈ W, a < 65536)
    (hv : v ∈ virtuals W) : v < 65536 := by
  rcases virtual_mem.mp hv with rfl | rfl | m
  · decide
  · decide
  · exact hw v m

private theorem full_sign (i : ℕ) : (65535 : ℕ).testBit i = decide (i < 16) := by
  rw [← t1_bits_true16, t1_bits_testBit, Bool.and_true]

private theorem low_mask_bound (a i : ℕ) (ha : a < 65536) (hi : 16 ≤ i) :
    a.testBit i = false := by
  apply Nat.testBit_eq_false_of_lt
  exact ha.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hi)

private theorem full_and (a : ℕ) (ha : a < 65536) : 65535 &&& a = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, full_sign i]
  by_cases hi : i < 16
  · simp only [decide_eq_true hi, Bool.true_and]
  · rw [low_mask_bound a i ha (Nat.le_of_not_gt hi), Bool.and_false]

private theorem full_or (a : ℕ) (ha : a < 65536) : 65535 ||| a = 65535 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_lor, full_sign i]
  by_cases hi : i < 16
  · simp only [decide_eq_true hi, Bool.true_or]
  · rw [low_mask_bound a i ha (Nat.le_of_not_gt hi), Bool.or_false]

private theorem result_comm (op : Bool) (a b : ℕ) : result (op, a, b) = result (op, b, a) := by
  cases op
  · exact Nat.and_comm a b
  · exact Nat.or_comm a b

private theorem result_idem (op : Bool) (a : ℕ) : result (op, a, a) = a := by
  cases op
  · exact Nat.and_self a
  · exact Nat.or_self a

private theorem result_left_virtual (W : Finset ℕ) (op : Bool) (a b : ℕ)
    (hw : ∀ v ∈ W, v < 65536) (ha : a = 0 ∨ a = 65535) (hb : b ∈ virtuals W) :
    result (op, a, b) ∈ virtuals W := by
  rcases ha with zero | full
  · cases op
    · change a &&& b ∈ virtuals W
      rw [zero, Nat.zero_and]
      exact virtual_mem.mpr (Or.inl rfl)
    · change a ||| b ∈ virtuals W
      rw [zero, Nat.zero_or]
      exact hb
  · cases op
    · change a &&& b ∈ virtuals W
      rw [full, full_and b (virtual_bound hw hb)]
      exact hb
    · change a ||| b ∈ virtuals W
      rw [full, full_or b (virtual_bound hw hb)]
      exact virtual_mem.mpr (Or.inr (Or.inl rfl))

private theorem proper_operands (W : Finset ℕ) (op : Bool) (a b : ℕ)
    (hw : ∀ v ∈ W, v < 65536) (ha : a ∈ virtuals W) (hb : b ∈ virtuals W)
    (fresh : result (op, a, b) ∉ virtuals W) :
    a ∈ W ∧ b ∈ W ∧ a ≠ b ∧ result (op, a, b) ∉ W := by
  have live (u v : ℕ) (hu : u ∈ virtuals W) (hv : v ∈ virtuals W)
      (hnew : result (op, u, v) ∉ virtuals W) : u ∈ W := by
    rcases virtual_mem.mp hu with zero | full | hm
    · exact (hnew (result_left_virtual W op u v hw (Or.inl zero) hv)).elim
    · exact (hnew (result_left_virtual W op u v hw (Or.inr full) hv)).elim
    · exact hm
  refine ⟨live a b ha hb fresh, live b a hb ha (by rwa [result_comm]), ?_, fun h => fresh (mem_virtuals h)⟩
  intro eq
  subst b
  exact fresh (by rwa [result_idem])

theorem finish_snoc (W : Finset ℕ) (gs : List Gate) (g : Gate) :
    finish W (gs ++ [g]) = insert (result g) (finish W gs) := by
  unfold finish
  rw [List.foldl_append]
  rfl

theorem admissible_snoc (W : Finset ℕ) (gs : List Gate) (g : Gate) (h : Admissible W gs)
    (a : g.2.1 ∈ finish W gs) (b : g.2.2 ∈ finish W gs)
    (ab : g.2.1 ≠ g.2.2) (fresh : result g ∉ finish W gs) :
    Admissible W (gs ++ [g]) := by
  induction gs generalizing W with
  | nil => exact ⟨a, b, ab, fresh, trivial⟩
  | cons d gs ih =>
    obtain ⟨d1, d2, dne, dnew, tail⟩ := h
    exact ⟨d1, d2, dne, dnew, ih _ tail a b fresh⟩

private def original (u v : Fin 4) (i : Fin 8) : Bool :=
  (oneEach u v).getD i.val false

private def clamp (u v : Fin 4) (i : Fin 8) : Bool :=
  original u v i && decide (i.val ≠ 3 ∧ i.val ≠ 7)

private def target (u v : Fin 4) : Bool := (855 : ℕ).testBit (4 * u.val + v.val)

private def samples (k : ℕ) : List Bool :=
  List.ofFn (clamp ⟨k / 4 % 4, by omega⟩ ⟨k % 4, by omega⟩)

private def prof (C : Circuit) (i : ℕ) : ℕ :=
  t1_bits (fun k => val C (samples k) i) 16

private theorem sample_len (k : ℕ) : (samples k).length = 8 := List.length_ofFn

private theorem original_as_ofFn : ∀ u v : Fin 4, List.ofFn (original u v) = oneEach u v := by
  decide +kernel

private theorem clamp_positive :
    ∀ u v : Fin 4, target u v = true → List.ofFn (clamp u v) = oneEach u v := by
  decide +kernel

private theorem clamp_rep (C : Circuit) (hm : Monotone2 C) (hr : Represents target C)
    (u v : Fin 4) : C.eval (List.ofFn (clamp u v)) = target u v := by
  cases h : target u v
  · cases heval : C.eval (List.ofFn (clamp u v))
    · rfl
    · have order (i : Fin 8) (hi : clamp u v i = true) : original u v i = true :=
        (Bool.and_eq_true_iff.mp hi).1
      have hout := mono 8 C (andOrOnly_of_monotone2 hm) (clamp u v) (original u v)
        order C.output heval
      change C.eval (List.ofFn (original u v)) = true at hout
      rw [original_as_ofFn u v, hr u v, h] at hout
      cases hout
  · rw [clamp_positive u v h]
    exact (hr u v).trans h

private theorem raw_signatures :
    ∀ i : Fin 8, t1_bits (fun k => (samples k).getD i.val false) 16 ∈ virtuals raw := by
  decide +kernel

private theorem raw_bound (v : ℕ) (hv : v ∈ raw) : v < 65536 := by
  simp only [raw, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem prof_early (C : Circuit) (i : ℕ) (hi : i < 8) :
    prof C i ∈ virtuals raw := by
  change t1_bits (fun k => val C (samples k) i) 16 ∈ _
  have eq : (fun k => val C (samples k) i) = (fun k => (samples k).getD i false) :=
    funext (fun k => val_input (sample_len k) hi)
  rw [eq]
  exact raw_signatures ⟨i, hi⟩

private theorem prof_beyond (C : Circuit) (i : ℕ) (hi : 8 + C.gates.length ≤ i) :
    prof C i = 0 := by
  change t1_bits (fun k => val C (samples k) i) 16 = 0
  have eq : (fun k => val C (samples k) i) = (fun _ => false) :=
    funext (fun k => val_ge (sample_len k) hi)
  rw [eq, t1_bits_false]

private theorem prof_target (C : Circuit) (hm : Monotone2 C) (hr : Represents target C) :
    prof C C.output = 855 := by
  have tgt : t1_bits (fun k => (855 : ℕ).testBit k) 16 = 855 := by decide +kernel
  change t1_bits (fun k => val C (samples k) C.output) 16 = 855
  rw [← tgt]
  apply t1_bits_ext
  intro k hk
  let u : Fin 4 := ⟨k / 4 % 4, by omega⟩
  let v : Fin 4 := ⟨k % 4, by omega⟩
  have index : 4 * u.val + v.val = k := by
    dsimp [u, v]
    omega
  have h : C.eval (List.ofFn (clamp u v)) = (855 : ℕ).testBit (4 * u.val + v.val) :=
    clamp_rep C hm hr u v
  rw [index] at h
  exact h

private theorem gate_prof (C : Circuit) (hm : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (W : Finset ℕ) (available : ∀ i < 8 + j, prof C i ∈ virtuals W) :
    ∃ op a b, a ∈ virtuals W ∧ b ∈ virtuals W ∧ result (op, a, b) = prof C (8 + j) := by
  have hg := hm _ (gateAt_mem hj)
  have hOp : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := hg.1
  let read (k i : ℕ) : Bool := if i < 8 + j then val C (samples k) i else false
  have e : prof C (8 + j) =
      t1_bits (fun k => (gateAt C j).op.eval ((gateAt C j).inputs.map (read k))) 16 := by
    change t1_bits (fun k => val C (samples k) (8 + j)) 16 = _
    congr 1
    funext k
    exact val_gate (sample_len k) hj
  have zero : 0 ∈ virtuals W := virtual_mem.mpr (Or.inl rfl)
  have full : 65535 ∈ virtuals W := virtual_mem.mpr (Or.inr (Or.inl rfl))
  have stepOK := t1_gate_step (virtuals W).toList read (gateAt C j).op (gateAt C j).inputs
    hOp hg.2 (by
      intro i _
      apply Finset.mem_toList.mpr
      by_cases hi : i < 8 + j
      · simpa only [read, ite_eq_left hi, prof] using available i hi
      · simp only [read, ite_eq_right hi, t1_bits_false]
        exact zero) (Finset.mem_toList.mpr zero) (Finset.mem_toList.mpr full)
  obtain ⟨a, ha, b, hb, hop⟩ := stepOK
  rw [← e] at hop
  rcases hop with andH | orH
  · exact ⟨false, a, b, Finset.mem_toList.mp ha, Finset.mem_toList.mp hb, andH.symm⟩
  · exact ⟨true, a, b, Finset.mem_toList.mp ha, Finset.mem_toList.mp hb, orH.symm⟩

private theorem result_bound (op : Bool) (a b : ℕ) (ha : a < 65536) (hb : b < 65536) :
    result (op, a, b) < 65536 := by
  cases op
  · exact Nat.and_lt_two_pow a (n := 16) hb
  · exact Nat.or_lt_two_pow (n := 16) ha hb

private theorem scan (C : Circuit) (hm : Monotone2 C) (j : ℕ) (hj : j ≤ C.gates.length) :
    ∃ gs : List Gate, gs.length ≤ j ∧ Admissible raw gs ∧
      (∀ g ∈ gs, 0 < result g ∧ result g < 65535) ∧
      (∀ v ∈ finish raw gs, v < 65536) ∧
      ∀ i < 8 + j, prof C i ∈ virtuals (finish raw gs) := by
  induction j with
  | zero =>
    exact ⟨[], le_rfl, trivial, fun _ h => (List.not_mem_nil h).elim, raw_bound,
      fun i hi => prof_early C i hi⟩
  | succ j ih =>
    obtain ⟨gs, gas, validTrace, proper, bound, ready⟩ := ih (by omega)
    let W := finish raw gs
    let r := prof C (8 + j)
    have next (V : Finset ℕ) (sub : W ⊆ V) (added : r ∈ virtuals V) :
        ∀ i < 8 + (j + 1), prof C i ∈ virtuals V := by
      intro i hi
      by_cases old : i < 8 + j
      · exact virtual_mono sub (ready i old)
      · have e : i = 8 + j := by omega
        subst i
        exact added
    by_cases seen : r ∈ virtuals W
    · exact ⟨gs, gas.trans (by omega), validTrace, proper, bound, next W Finset.Subset.rfl seen⟩
    · obtain ⟨op, a, b, ha, hb, hp⟩ := gate_prof C hm j (by omega) W ready
      have hnew : result (op, a, b) ∉ virtuals W := by
        intro h
        rw [hp] at h
        exact seen h
      have hab := proper_operands W op a b bound ha hb hnew
      let g : Gate := (op, a, b)
      have hproper : 0 < result g ∧ result g < 65535 := by
        have lower : result g ≠ 0 := fun e => hnew (virtual_mem.mpr (Or.inl e))
        have upper : result g ≠ 65535 := fun e => hnew (virtual_mem.mpr (Or.inr (Or.inl e)))
        have small : result g < 65536 := result_bound op a b (virtual_bound bound ha) (virtual_bound bound hb)
        omega
      have ending : finish raw (gs ++ [g]) = insert (result g) W := finish_snoc raw gs g
      refine ⟨gs ++ [g], ?_, admissible_snoc raw gs g validTrace hab.1 hab.2.1 hab.2.2.1 hab.2.2.2, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact proper d hd
        · have e := List.mem_singleton.mp hd
          subst d
          exact hproper
      · rw [ending]
        intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hproper.2.trans (by decide)
        · exact bound d hd
      · rw [ending]
        apply next (insert (result g) W) (Finset.subset_insert _ _)
        exact mem_virtuals (Finset.mem_insert.mpr (Or.inl hp.symm))

theorem traceOfRep
    (h : RepSizeAtMost (fun u v : Fin 4 => (855 : ℕ).testBit (4 * u.val + v.val)) 6) :
    ∃ gs : List Gate, gs.length ≤ 6 ∧ Admissible raw gs ∧ 855 ∈ finish raw gs ∧
      ∀ g ∈ gs, 0 < result g ∧ result g < 65535 := by
  obtain ⟨C, hm, hs, hr⟩ := h
  obtain ⟨gs, gas, validTrace, proper, _, ready⟩ := scan C hm C.gates.length le_rfl
  have output : prof C C.output ∈ virtuals (finish raw gs) := by
    by_cases hi : C.output < 8 + C.gates.length
    · exact ready C.output hi
    · rw [prof_beyond C C.output (Nat.le_of_not_gt hi)]
      exact virtual_mem.mpr (Or.inl rfl)
  have eq : prof C C.output = 855 := prof_target C hm hr
  rw [eq] at output
  refine ⟨gs, gas.trans hs, validTrace, ?_, proper⟩
  rcases virtual_mem.mp output with contradiction | contradiction | member
  · omega
  · omega
  · exact member

end Table6159Trace

namespace Table6159Bridge

abbrev Instr := Table6159Trace.Gate
abbrev result := Table6159Trace.result
abbrev admissible := Table6159Trace.Admissible
abbrev finish := Table6159Trace.finish

def kept (T : Finset ℕ) (a b : ℕ) : ℕ :=
  (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0)

def liveStep (S T : Finset ℕ) (extra : ℕ) : Prop :=
  ∃ g : Instr, g.2.1 ≠ g.2.2 ∧ result g ∉ S ∧ result g ∈ T ∧
    S = insert g.2.1 (insert g.2.2 (T.erase (result g))) ∧ extra = kept T g.2.1 g.2.2

def route : ℕ → Finset ℕ → ℕ → Prop
  | 0, S, extra => S = {855} ∧ extra = 0
  | k + 1, S, extra => ∃ T u v, liveStep S T u ∧ route k T v ∧ extra = u + v

theorem route_of_program (W : Finset ℕ) (gs : List Instr)
    (prog : admissible W gs) (reaches : 855 ∈ finish W gs) :
    ∃ S ⊆ W, ∃ k ≤ gs.length, ∃ extra, route k S extra := by
  induction gs generalizing W with
  | nil =>
    exact ⟨{855}, Finset.singleton_subset_iff.mpr reaches, 0, by simp, 0, rfl, rfl⟩
  | cons g tail ih =>
    change g.2.1 ∈ W ∧ g.2.2 ∈ W ∧ g.2.1 ≠ g.2.2 ∧ result g ∉ W ∧
      admissible (insert (result g) W) tail at prog
    obtain ⟨a,b,distinct,new,rest⟩ := prog
    change 855 ∈ finish (insert (result g) W) tail at reaches
    obtain ⟨T,sub,k,budget,extra,later⟩ := ih _ rest reaches
    by_cases used : result g ∈ T
    · let S := insert g.2.1 (insert g.2.2 (T.erase (result g)))
      have hS : S ⊆ W := by
        intro i hi
        simp only [S,Finset.mem_insert,Finset.mem_erase] at hi
        rcases hi with rfl | rfl | ⟨hz,ht⟩
        · exact a
        · exact b
        · exact (Finset.mem_insert.mp (sub ht)).resolve_left hz
      have live : liveStep S T (kept T g.2.1 g.2.2) :=
        ⟨g,distinct,fun bad => new (hS bad),used,rfl,rfl⟩
      exact ⟨S,hS,k+1,by simpa using budget,kept T g.2.1 g.2.2+extra,
        ⟨T,_,extra,live,later,rfl⟩⟩
    · have ts : T ⊆ W := by
        intro i hi
        apply (Finset.mem_insert.mp (sub hi)).resolve_left
        rintro rfl
        exact used hi
      exact ⟨T,ts,k,budget.trans (by simp),extra,later⟩

def separates (S : Finset ℕ) : Prop :=
  ∀ p q : Fin 16, (855 : ℕ).testBit p.val = true → (855 : ℕ).testBit q.val = false →
    ∃ x ∈ S, x.testBit p.val = true ∧ x.testBit q.val = false

theorem bit_witness (g : Instr) (p q : Fin 16)
    (hp : (result g).testBit p.val = true) (hq : (result g).testBit q.val = false) :
    (g.2.1.testBit p.val = true ∧ g.2.1.testBit q.val = false) ∨
    (g.2.2.testBit p.val = true ∧ g.2.2.testBit q.val = false) := by
  cases g with
  | mk flag pair =>
    cases pair with
    | mk a b =>
      cases flag
      · change (a &&& b).testBit p.val = true at hp
        change (a &&& b).testBit q.val = false at hq
        rw [Nat.testBit_and,Bool.and_eq_true_iff] at hp
        rw [Nat.testBit_and,Bool.and_eq_false_iff] at hq
        exact hq.elim (fun h => Or.inl ⟨hp.1,h⟩) (fun h => Or.inr ⟨hp.2,h⟩)
      · change (a ||| b).testBit p.val = true at hp
        change (a ||| b).testBit q.val = false at hq
        rw [Nat.testBit_or,Bool.or_eq_true_iff] at hp
        rw [Nat.testBit_or,Bool.or_eq_false_iff] at hq
        exact hp.elim (fun h => Or.inl ⟨h,hq.1⟩) (fun h => Or.inr ⟨h,hq.2⟩)

theorem step_separates {S T : Finset ℕ} {extra : ℕ}
    (h : liveStep S T extra) (sep : separates T) : separates S := by
  obtain ⟨g,_,_,_,hs,_⟩ := h
  intro p q hp hq
  obtain ⟨x,hx,xp,xq⟩ := sep p q hp hq
  by_cases new : x = result g
  · subst x
    rcases bit_witness g p q xp xq with a | b
    · exact ⟨g.2.1,by rw [hs]; simp,a.1,a.2⟩
    · exact ⟨g.2.2,by rw [hs]; simp,b.1,b.2⟩
  · exact ⟨x,by rw [hs]; simp [new,hx],xp,xq⟩

theorem route_separates (k : ℕ) (S : Finset ℕ) (extra : ℕ) (h : route k S extra) : separates S := by
  induction k generalizing S extra with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact fun p q hp hq => ⟨855,by simp,hp,hq⟩
  | succ k ih =>
    obtain ⟨T,u,v,step,later,_⟩ := h
    exact step_separates step (ih T v later)

theorem step_card {S T : Finset ℕ} {extra : ℕ} (h : liveStep S T extra) :
    S.card + extra = T.card + 1 := by
  obtain ⟨g,ab,new,inT,hs,he⟩ := h
  have ac : g.2.1 ≠ result g := fun eq => new (by rw [hs,←eq]; simp)
  have bc : g.2.2 ≠ result g := fun eq => new (by rw [hs,←eq]; simp)
  have lower : (T.erase (result g)).card + 1 = T.card := Finset.card_erase_add_one inT
  rw [hs,he]
  unfold kept
  by_cases ha : g.2.1 ∈ T <;> by_cases hb : g.2.2 ∈ T
  · have h1 : g.2.1 ∈ insert g.2.2 (T.erase (result g)) := by simp [ac,ha]
    have h2 : g.2.2 ∈ T.erase (result g) := by simp [bc,hb]
    rw [Finset.card_insert_of_mem h1,Finset.card_insert_of_mem h2,ite_eq_left ha,ite_eq_left hb]
    omega
  · have h1 : g.2.1 ∈ insert g.2.2 (T.erase (result g)) := by simp [ac,ha]
    have h2 : g.2.2 ∉ T.erase (result g) := by simp [hb]
    rw [Finset.card_insert_of_mem h1,Finset.card_insert_of_notMem h2,ite_eq_left ha,ite_eq_right hb]
    omega
  · have h1 : g.2.1 ∉ insert g.2.2 (T.erase (result g)) := by simp [ab,ha]
    have h2 : g.2.2 ∈ T.erase (result g) := by simp [bc,hb]
    rw [Finset.card_insert_of_notMem h1,Finset.card_insert_of_mem h2,ite_eq_right ha,ite_eq_left hb]
    omega
  · have h1 : g.2.1 ∉ insert g.2.2 (T.erase (result g)) := by simp [ab,ha]
    have h2 : g.2.2 ∉ T.erase (result g) := by simp [hb]
    rw [Finset.card_insert_of_notMem h1,Finset.card_insert_of_notMem h2,ite_eq_right ha,ite_eq_right hb]
    omega

theorem route_card (k : ℕ) (S : Finset ℕ) (extra : ℕ) (h : route k S extra) :
    S.card + extra = k + 1 := by
  induction k generalizing S extra with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    simp
  | succ k ih =>
    obtain ⟨T,u,v,first,rest,rfl⟩ := h
    have := step_card first
    have := ih T v rest
    omega

end Table6159Bridge

namespace Table6159Bridge

theorem step_forward {S T : Finset ℕ} {extra : ℕ} (h : liveStep S T extra) (cap : extra ≤ 1) :
    ∃ a b z : ℕ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ z ∉ S ∧ (z = (a &&& b) ∨ z = (a ||| b)) ∧
      ((T = insert z ((S.erase a).erase b) ∧ extra = 0) ∨
        (T = insert z (S.erase b) ∧ extra = 1) ∨
        (T = insert z (S.erase a) ∧ extra = 1)) := by
  obtain ⟨g,diff,fresh,live,initial,cost⟩ := h
  let a := g.2.1
  let b := g.2.2
  let z := result g
  refine ⟨a,b,z,?_,?_,diff,fresh,?_,?_⟩
  · rw [initial]
    simp [a]
  · rw [initial]
    simp [b]
  · change (if g.1 then (a ||| b) else (a &&& b)) = (a &&& b) ∨
      (if g.1 then (a ||| b) else (a &&& b)) = (a ||| b)
    by_cases flag : g.1 = true <;> simp [flag]
  · have hs : S = insert a (insert b (T.erase z)) := initial
    have ec : extra = kept T a b := cost
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
    · have he : extra = 2 := by simpa [kept,ha,hb] using ec
      omega
    · right
      left
      refine ⟨?_,by simpa [kept,ha,hb] using ec⟩
      ext x
      have eA : x = a → x ∈ T := fun e => e ▸ ha
      have eB : x = b → x ∉ T := fun e => e ▸ hb
      have eZ : x = z → x ∈ T := fun e => e ▸ live
      rw [hs]
      simp only [Finset.mem_insert,Finset.mem_erase]
      tauto
    · right
      right
      refine ⟨?_,by simpa [kept,ha,hb] using ec⟩
      ext x
      have eA : x = a → x ∉ T := fun e => e ▸ ha
      have eB : x = b → x ∈ T := fun e => e ▸ hb
      have eZ : x = z → x ∈ T := fun e => e ▸ live
      rw [hs]
      simp only [Finset.mem_insert,Finset.mem_erase]
      tauto
    · left
      refine ⟨?_,by simpa [kept,ha,hb] using ec⟩
      ext x
      have eA : x = a → x ∉ T := fun e => e ▸ ha
      have eB : x = b → x ∉ T := fun e => e ▸ hb
      have eZ : x = z → x ∈ T := fun e => e ▸ live
      rw [hs]
      simp only [Finset.mem_insert,Finset.mem_erase]
      tauto

end Table6159Bridge

namespace Table6159Finish

open Table6159Bridge Table6159Finite

def fuel (allow : Bool) : ℕ := if allow then 1 else 0

def remaining (allow : Bool) (spent : ℕ) : Bool := allow && decide (spent = 0)

theorem fuel_max (allow : Bool) : fuel allow ≤ 1 := by cases allow <;> decide

theorem fuel_advance (allow : Bool) (used after : ℕ) (cap : used + after ≤ fuel allow) :
    after ≤ fuel (remaining allow used) := by
  cases allow <;> cases used <;> simp [fuel,remaining] at cap ⊢ <;> omega

theorem enumerate_live {S T : Finset ℕ} {extra : ℕ} (step : liveStep S T extra)
    (nextSeparates : separates T) (allow : Bool) (bound : extra ≤ fuel allow) :
    (T,remaining allow extra) ∈ next S allow := by
  have cap := bound.trans (fuel_max allow)
  obtain ⟨a,b,z,ha,hb,ne,fresh,op,moves⟩ := step_forward step cap
  rcases moves with one | two | three
  · obtain ⟨rfl,rfl⟩ := one
    simpa [remaining] using mem_next_drop_both (allow := allow) ha hb ne fresh op nextSeparates
  · obtain ⟨rfl,rfl⟩ := two
    have allowed : allow = true := by cases allow <;> simp [fuel] at bound ⊢
    simpa [remaining] using mem_next_keep_a ha hb ne fresh op allowed nextSeparates
  · obtain ⟨rfl,rfl⟩ := three
    have allowed : allow = true := by cases allow <;> simp [fuel] at bound ⊢
    simpa [remaining] using mem_next_keep_b ha hb ne fresh op allowed nextSeparates

theorem impossible_program : ∀ gs : List Instr, gs.length ≤ 6 → admissible raw gs →
    855 ∈ finish raw gs → False := by
  intro gs length prog goal
  obtain ⟨S,subset,k,len,extra,live⟩ := route_of_program raw gs prog goal
  have eq : S = raw := raw_subset_separating S subset (route_separates k S extra live)
  subst S
  have card := route_card k raw extra live
  have six : raw.card = 6 := by decide +kernel
  rw [six] at card
  have hshort : k ≤ 6 := len.trans length
  have hk : k - 3 + 3 = k := by omega
  let rest := k - 3
  have whole : route (rest + 3) raw extra := hk.symm ▸ live
  obtain ⟨S1,a,rem1,s1,t1,split1⟩ := whole
  have sep1 := route_separates _ _ _ t1
  obtain ⟨S2,b,rem2,s2,t2,split2⟩ := t1
  have sep2 := route_separates _ _ _ t2
  obtain ⟨S3,c,rem3,s3,t3,split3⟩ := t2
  have allFuel : a + rem1 ≤ fuel true := by
    change a + rem1 ≤ 1
    omega
  let allow1 := remaining true a
  let allow2 := remaining allow1 b
  have bound1 : a ≤ fuel true := by omega
  have fuel1 : rem1 ≤ fuel allow1 := fuel_advance true a rem1 allFuel
  have bound2 : b ≤ fuel allow1 := by omega
  have fuel2 : rem2 ≤ fuel allow2 := fuel_advance allow1 b rem2 (split2 ▸ fuel1)
  have bound3 : c ≤ fuel allow2 := by omega
  have e1 := enumerate_live s1 sep1 true bound1
  have e2 := enumerate_live s2 sep2 allow1 bound2
  have e3 := enumerate_live s3 (route_separates _ _ _ t3) allow2 bound3
  exact no_third e1 e2 e3

end Table6159Finish

end PEqualNP.Outside.L_meta_6159

theorem PEqualNP.Outside.L_meta_6159 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (855 : ℕ).testBit (4 * u.val + v.val)) 7 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (855 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  refine ⟨PEqualNP.Outside.L_meta_6159.Table6159Upper.upper, ?_⟩
  intro witness
  obtain ⟨gs, budget, admissible, occurs, _⟩ := PEqualNP.Outside.L_meta_6159.Table6159Trace.traceOfRep witness
  exact PEqualNP.Outside.L_meta_6159.Table6159Finish.impossible_program gs budget admissible occurs
