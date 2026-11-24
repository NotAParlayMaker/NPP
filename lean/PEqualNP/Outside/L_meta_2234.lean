import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2234

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
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

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
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)


lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

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

open PEqualNP.TopForm

lemma fin2 : ∀ p : Fin 2, p = 0 ∨ p = 1 := by decide

lemma e10 : (1 - 0 : Fin 2) = 1 := by decide

lemma e11 : (1 - 1 : Fin 2) = 0 := by decide

lemma two_inputs {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {k : ℕ} (hk : k < C.gates.length) :
    ∃ p q, (gateAt C k).inputs = [p, q] ∧ p < n + k ∧ q < n + k ∧ opnd C k 0 = p ∧
      opnd C k 1 = q := by
  obtain ⟨_, hRB, h2⟩ := hA
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
  exact ⟨p, q, hin, hRB k hk p (by rw [hin]; simp), hRB k hk q (by rw [hin]; simp),
    by simp [opnd, hin], by simp [opnd, hin]⟩

lemma reach_input {n : ℕ} {C : Circuit} {w w' : ℕ} (hw : w < n)
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' = w := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hstep, _⟩
  · exact h.symm
  · obtain ⟨k, _, e, _⟩ := hstep
    omega

lemma reach_gate {n : ℕ} {C : Circuit} {k w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) (n + k) w') :
    w' = n + k ∨ (k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ c ∈ (gateAt C k).inputs, c < n + k ∧ Relation.ReflTransGen (OrStep n C) c w') := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hstep, hr⟩
  · exact Or.inl h.symm
  · obtain ⟨k', hk', e, hop, hin, hlt⟩ := hstep
    have hkk : k' = k := by omega
    subst hkk
    exact Or.inr ⟨hk', hop, c, hin, hlt, hr⟩

lemma orIn_card_input {n : ℕ} {C : Circuit} {w : ℕ} (hw : w < n) : (orIn n C w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have h1 := reach_input hw (mem_orIn_reach a ha)
  have h2 := reach_input hw (mem_orIn_reach b hb)
  exact Fin.ext (h1.trans h2.symm)

lemma orIn_gate {n : ℕ} {C : Circuit} {k : ℕ} (u : Fin n) (hu : u ∈ orIn n C (n + k)) :
    k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ c ∈ (gateAt C k).inputs, c < n + k ∧ u ∈ orIn n C c := by
  rcases reach_gate (mem_orIn_reach u hu) with h | ⟨hk, hop, c, hc, hlt, hr⟩
  · have := u.isLt
    omega
  · exact ⟨hk, hop, c, hc, hlt, reach_mem_orIn u hr⟩

lemma orIn_up {n : ℕ} {C : Circuit} {k c : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hc : c ∈ (gateAt C k).inputs) (hlt : c < n + k) :
    orIn n C c ⊆ orIn n C (n + k) := by
  intro u hu
  exact reach_mem_orIn u
    (Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hc, hlt⟩ (mem_orIn_reach u hu))

lemma orIn_mono {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : orIn n C w' ⊆ orIn n C w := by
  intro u hu
  exact reach_mem_orIn u (h.trans (mem_orIn_reach u hu))

lemma count_abs {α : Type} [DecidableEq α] (f : ℕ → Finset α) (d : ℕ → Finset ℕ)
    (h : ∀ m, (f m).card ≤ 1 ∨ (∃ q, q < m ∧ f m ⊆ f q ∧ d q ⊆ d m) ∨
      (∃ p q k, p < m ∧ q < m ∧ f m ⊆ f p ∪ f q ∧ d p ⊆ d m ∧ d q ⊆ d m ∧ k ∈ d m ∧
        ∀ w, w < m → k ∉ d w)) :
    ∀ m (W : Finset ℕ), (∀ w ∈ W, w < m) →
      (W.biUnion f).card ≤ W.card + (W.biUnion d).card := by
  intro m
  induction m with
  | zero =>
    intro W hW
    have hW0 : W = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun w hw => by have := hW w hw; omega)
    subst hW0
    simp
  | succ m ih =>
    intro W hW
    by_cases hm : m ∈ W
    · have hW' : ∀ w ∈ W.erase m, w < m := by
        intro w hw
        have h1 := hW w (Finset.mem_of_mem_erase hw)
        have h2 := Finset.ne_of_mem_erase hw
        omega
      have hc : (W.erase m).card + 1 = W.card := Finset.card_erase_add_one hm
      have hD : (W.erase m).biUnion d ⊆ W.biUnion d :=
        Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.erase_subset _ _)
      have hdm : d m ⊆ W.biUnion d := Finset.subset_biUnion_of_mem d hm
      have hU : W.biUnion f = f m ∪ (W.erase m).biUnion f := by
        rw [← Finset.biUnion_insert, Finset.insert_erase hm]
      rcases h m with h1 | ⟨q, hq, hfq, hdq⟩ | ⟨p, q, k, hp, hq, hf, hdp, hdq, hk, hkn⟩
      · have h0 := ih (W.erase m) hW'
        have h2 := Finset.card_union_le (f m) ((W.erase m).biUnion f)
        have h3 := Finset.card_le_card hD
        rw [hU]
        omega
      · have hW2 : ∀ w ∈ insert q (W.erase m), w < m := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hq
          · exact hW' w hw
        have h1 := ih _ hW2
        have h2 : W.biUnion f ⊆ (insert q (W.erase m)).biUnion f := by
          rw [hU, Finset.biUnion_insert]
          exact Finset.union_subset_union hfq (Finset.Subset.refl _)
        have h3 : (insert q (W.erase m)).biUnion d ⊆ W.biUnion d := by
          rw [Finset.biUnion_insert]
          exact Finset.union_subset (hdq.trans hdm) hD
        have h4 := Finset.card_insert_le q (W.erase m)
        have h5 := Finset.card_le_card h2
        have h6 := Finset.card_le_card h3
        omega
      · obtain ⟨W2, hW2def⟩ : ∃ W2, W2 = insert p (insert q (W.erase m)) := ⟨_, rfl⟩
        have hW2 : ∀ w ∈ W2, w < m := by
          intro w hw
          rw [hW2def] at hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hp
          · rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hq
            · exact hW' w hw
        have h1 := ih _ hW2
        have h2 : W.biUnion f ⊆ W2.biUnion f := by
          rw [hU, hW2def, Finset.biUnion_insert, Finset.biUnion_insert, ← Finset.union_assoc]
          exact Finset.union_subset_union hf (Finset.Subset.refl _)
        have h3 : insert k (W2.biUnion d) ⊆ W.biUnion d := by
          rw [hW2def, Finset.biUnion_insert, Finset.biUnion_insert]
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hdm hk
          · rcases Finset.mem_union.mp hx with hx | hx
            · exact hdm (hdp hx)
            · rcases Finset.mem_union.mp hx with hx | hx
              · exact hdm (hdq hx)
              · exact hD hx
        have hkn2 : k ∉ W2.biUnion d := by
          intro hx
          obtain ⟨w, hw, hkw⟩ := Finset.mem_biUnion.mp hx
          exact hkn w (hW2 w hw) hkw
        have h4 : W2.card ≤ (W.erase m).card + 2 := by
          have a1 := Finset.card_insert_le p (insert q (W.erase m))
          have a2 := Finset.card_insert_le q (W.erase m)
          rw [hW2def]
          omega
        have h5 := Finset.card_le_card h2
        have h6 := Finset.card_le_card h3
        rw [Finset.card_insert_of_notMem hkn2] at h6
        omega
    · apply ih W
      intro w hw
      have h1 := hW w hw
      have h2 : w ≠ m := fun e => hm (e ▸ hw)
      omega


noncomputable def sset (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k => OrReaches n C w k ∧
    (gateAt C k).op = GateOp.or ∧ 2 ≤ (orIn n C (n + k)).card

lemma mem_sset {n : ℕ} {C : Circuit} {w k : ℕ} : k ∈ sset n C w ↔ k < C.gates.length ∧
    OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ 2 ≤ (orIn n C (n + k)).card := by
  unfold sset
  simp only [Finset.mem_filter, Finset.mem_range]

lemma count_hyp2 {n : ℕ} {C : Circuit} (hA : IsAO2 n C) (m : ℕ) :
    (orIn n C m).card ≤ 1 ∨
    (∃ q, q < m ∧ orIn n C m ⊆ orIn n C q ∧ sset n C q ⊆ sset n C m) ∨
    (∃ p q k, p < m ∧ q < m ∧ orIn n C m ⊆ orIn n C p ∪ orIn n C q ∧
      sset n C p ⊆ sset n C m ∧ sset n C q ⊆ sset n C m ∧ k ∈ sset n C m ∧
      ∀ w, w < m → k ∉ sset n C w) := by
  by_cases hc : (orIn n C m).card ≤ 1
  · exact Or.inl hc
  by_cases hm : m < n
  · exact Or.inl (orIn_card_input hm)
  · obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    by_cases hgo : k < C.gates.length ∧ (gateAt C k).op = GateOp.or
    · obtain ⟨hk, hop⟩ := hgo
      obtain ⟨p, q, hin, hp, hq, e0, e1⟩ := two_inputs hA hk
      have hsub : orIn n C (n + k) ⊆ orIn n C p ∪ orIn n C q := by
        intro u hu
        obtain ⟨_, _, c, hc, _, huc⟩ := orIn_gate u hu
        rw [hin] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact Finset.mem_union_left _ huc
        · exact Finset.mem_union_right _ huc
      have hd : ∀ c, c ∈ (gateAt C k).inputs → c < n + k →
          sset n C c ⊆ sset n C (n + k) := by
        intro c hc hlt g hg
        rw [mem_sset] at hg ⊢
        exact ⟨hg.1, (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hc, hlt, hg.2.1⟩⟩, hg.2.2⟩
      have hpin : p ∈ (gateAt C k).inputs := by rw [hin]; simp
      have hqin : q ∈ (gateAt C k).inputs := by rw [hin]; simp
      by_cases hpe : (orIn n C p).Nonempty
      · by_cases hqe : (orIn n C q).Nonempty
        · refine Or.inr (Or.inr ⟨p, q, k, hp, hq, hsub, hd p hpin hp, hd q hqin hq, ?_, ?_⟩)
          · rw [mem_sset]
            exact ⟨hk, (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hop, by omega⟩
          · intro w hw hmem
            rw [mem_sset] at hmem
            have h3 := orStep_le (orReaches_reach k w hmem.2.1).1
            omega
        · refine Or.inr (Or.inl ⟨p, hp, ?_, hd p hpin hp⟩)
          intro u hu
          rcases Finset.mem_union.mp (hsub hu) with h | h
          · exact h
          · exact (hqe ⟨u, h⟩).elim
      · refine Or.inr (Or.inl ⟨q, hq, ?_, hd q hqin hq⟩)
        intro u hu
        rcases Finset.mem_union.mp (hsub hu) with h | h
        · exact (hpe ⟨u, h⟩).elim
        · exact h
    · left
      have he : orIn n C (n + k) = ∅ := Finset.eq_empty_of_forall_notMem
        (fun u hu => hgo ⟨(orIn_gate u hu).1, (orIn_gate u hu).2.1⟩)
      rw [he]
      simp

lemma partA {n : ℕ} {C : Circuit}
    (hz : ∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false)
    (i : ℕ) (hc : 2 ≤ (orIn n C (n + i)).card) : ¬ OrReaches n C C.output i := by
  intro hr
  obtain ⟨a, ha⟩ : (orIn n C (n + i)).Nonempty := Finset.card_pos.mp (by omega)
  have h1 := (orReaches_reach i C.output hr).1
  have h2 := mem_orIn_reach a ha
  have h3 := reach_var_val (fun k1 => decide (k1 = a)) C.output a (h1.trans h2) (by simp)
  have h4 := hz a
  unfold PEqualNP.MetaComplexity.circuitFun at h4
  rw [eval_eq_val, h3] at h4
  exact Bool.noConfusion h4

lemma partB (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ) (h4 : NoFourCycle G) (hA : IsAO2 n C)
    (hs : ∀ j ∈ F, ∀ b : Fin n, b ∈ orIn n C (lf j) → G.Adj (ctr j) b) :
    ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n =>
        ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))).card ≤
      Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
        2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} + F.card := by
  classical
  let W : Fin n → Finset ℕ := fun c => (F.filter (fun j => ctr j = c)).image lf
  let D : Fin n → Finset ℕ := fun c => (W c).biUnion (sset n C)
  let S : Finset ℕ := (Finset.range C.gates.length).filter (fun i2 =>
    (gateAt C i2).op = GateOp.or ∧ 2 ≤ (orIn n C (n + i2)).card ∧
      ∃ j3 ∈ F, OrReaches n C (lf j3) i2)
  have hSet : {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
      2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} = (S : Set ℕ) := by
    ext i2
    simp [S]
  rw [hSet, Set.ncard_coe_finset]
  have hmemW : ∀ c w, w ∈ W c ↔ ∃ j ∈ F, ctr j = c ∧ lf j = w := by
    intro c w
    simp only [W, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, ⟨hj, hc⟩, e⟩
      exact ⟨j, hj, hc, e⟩
    · rintro ⟨j, hj, hc, e⟩
      exact ⟨j, ⟨hj, hc⟩, e⟩
  let M : ℕ := (F.image lf).sup id + 1
  have hM : ∀ c, ∀ w ∈ W c, w < M := by
    intro c w hw
    obtain ⟨j, hj, _, rfl⟩ := (hmemW c w).mp hw
    have : lf j ≤ (F.image lf).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    simp only [M]
    omega
  have hper : ∀ c, (Finset.univ.filter (fun b2 : Fin n =>
      ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))).card ≤ (W c).card + (D c).card := by
    intro c
    have hsub : Finset.univ.filter (fun b2 : Fin n =>
        ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2)) ⊆ (W c).biUnion (orIn n C) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      obtain ⟨j, hj, hc, hb⟩ := hb
      exact Finset.mem_biUnion.mpr ⟨lf j, (hmemW c (lf j)).mpr ⟨j, hj, hc, rfl⟩, hb⟩
    have h1 := Finset.card_le_card hsub
    have h2 := count_abs (orIn n C) (sset n C) (count_hyp2 hA) M (W c) (hM c)
    simp only [D]
    omega
  have hWsum : ∑ c : Fin n, (W c).card ≤ F.card := by
    have h1 : ∀ c, (W c).card ≤ (F.filter (fun j => ctr j = c)).card :=
      fun c => Finset.card_image_le
    have h2 := Finset.card_eq_sum_card_fiberwise (s := F) (t := Finset.univ) (f := ctr)
      (fun j _ => Finset.mem_coe.mpr (Finset.mem_univ (ctr j)))
    rw [h2]
    exact Finset.sum_le_sum (fun c _ => h1 c)
  have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint D := by
    intro c _ c' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨w, hw, hkw⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨w', hw', hkw'⟩ := Finset.mem_biUnion.mp hk'
    obtain ⟨j, hj, hc, rfl⟩ := (hmemW c w).mp hw
    obtain ⟨j', hj', hc', rfl⟩ := (hmemW c' w').mp hw'
    rw [mem_sset] at hkw hkw'
    have s1 := orIn_mono (orReaches_reach k (lf j) hkw.2.1).1
    have s2 := orIn_mono (orReaches_reach k (lf j') hkw'.2.1).1
    have hsub : orIn n C (n + k) ⊆ Finset.univ.filter (fun w => G.Adj c w ∧ G.Adj c' w) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · rw [← hc]; exact hs j hj b (s1 hb)
      · rw [← hc']; exact hs j' hj' b (s2 hb)
    have e1 := Finset.card_le_card hsub
    have e2 := h4 c c' hne
    have e3 := hkw.2.2.2
    omega
  have hDsum : ∑ c : Fin n, (D c).card ≤ S.card := by
    rw [← Finset.card_biUnion hdisj]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨w, hw, hkw⟩ := Finset.mem_biUnion.mp hkc
    obtain ⟨j, hj, _, rfl⟩ := (hmemW c w).mp hw
    rw [mem_sset] at hkw
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨hkw.1, hkw.2.2.1, hkw.2.2.2, j, hj, hkw.2.1⟩
  calc ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n =>
        ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))).card
      ≤ ∑ c : Fin n, ((W c).card + (D c).card) := Finset.sum_le_sum (fun c _ => hper c)
    _ = ∑ c : Fin n, (W c).card + ∑ c : Fin n, (D c).card := Finset.sum_add_distrib
    _ ≤ S.card + F.card := by omega

end PEqualNP.Outside.L_meta_2234

theorem PEqualNP.Outside.L_meta_2234 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  intro n G _ C F ctr lf h4 hA hz hs
  exact ⟨fun i _ _ hc _ => PEqualNP.Outside.L_meta_2234.partA hz i hc,
    PEqualNP.Outside.L_meta_2234.partB n G C F ctr lf h4 hA hs⟩
