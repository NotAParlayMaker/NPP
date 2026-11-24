import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2235

section B2231
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire_b31 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl_b31 (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire_b31 x := rfl

lemma foldl_length_b31 (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire_b31 w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire_b31]
    omega

lemma foldl_getD_lt_b31 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire_b31 w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire_b31 w g).length := by simp [stepWire_b31]; omega
    rw [ih (stepWire_b31 w g) hlt]
    simp [stepWire_b31, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_b31 (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate_b31 (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire_b31 w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire_b31 w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire_b31 w g).length := by simp [stepWire_b31]
      rw [Nat.add_zero, foldl_getD_lt_b31 gs (stepWire_b31 w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire_b31 w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire_b31, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt_b31 gs (stepWire_b31 w g) i (by simp [stepWire_b31]; omega)]
        simp [stepWire_b31, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge_b31 w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire_b31 w g) j hj'
      have hl : (stepWire_b31 w g).length = w.length + 1 := by simp [stepWire_b31]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val_b31 (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val_b31 (C : Circuit) (x : List Bool) : C.eval x = val_b31 C x C.output := rfl

lemma gateAt_eq_b31 {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem_b31 {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq_b31 hj]; exact List.getElem_mem hj

lemma val_input_b31 {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val_b31 C x u = x.getD u false := by
  unfold val_b31; rw [wires_eq_foldl_b31]; exact foldl_getD_lt_b31 _ _ _ (by omega)

lemma val_ge_b31 {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val_b31 C x u = false := by
  unfold val_b31; apply getD_ge_b31; rw [wires_eq_foldl_b31, foldl_length_b31]; omega

lemma val_gate_b31 {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val_b31 C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val_b31 C x i else false) := by
  subst hx
  rw [gateAt_eq_b31 hj]
  exact foldl_getD_gate_b31 C.gates x j hj

def OpMono_b31 (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq_b31 : OpMono_b31 Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp_b31 : OpMono_b31 (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or_b31 {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val_b31 C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val_b31 C x i = true := by
  rw [val_gate_b31 hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and_b31 {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val_b31 C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val_b31 C x i = true := by
  rw [val_gate_b31 hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma biclique_star_b31 {n : ℕ} (G : SimpleGraph (Fin n))
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

lemma val_ofFn_b31 {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val_b31 C (List.ofFn x) u.val = x u := by
  rw [val_input_b31 (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def OrStep_b31 (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up_b31 {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep_b31 n C) w w') (hv : val_b31 C x w' = true) :
    val_b31 C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or_b31 hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma reach_var_val_b31 {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep_b31 n C) p t.val) (ht : x t = true) :
    val_b31 C (List.ofFn x) p = true :=
  orStep_up_b31 (n := n) (by simp) hr (by rw [val_ofFn_b31]; exact ht)

open PEqualNP.CleanedNonEdge

lemma orSets_len_b31 (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char_b31 (n : ℕ) (gs : List Gate) :
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
      rw [orSets_len_b31]; simp
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

lemma orReaches_iff_b31 (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char_b31 n C.gates g k
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

lemma orReaches_reach_b31 {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep_b31 n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff_b31 n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach_b31 {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep_b31 n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach_b31 k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma opnd_eq_b31 {n : ℕ} {C : Circuit} (hA : PEqualNP.TopForm.IsAO2 n C) {a : ℕ}
    (ha : a < C.gates.length) :
    (gateAt C a).inputs = [PEqualNP.TopForm.opnd C a 0, PEqualNP.TopForm.opnd C a 1] := by
  have h2 := hA.2.2 _ (gateAt_mem_b31 ha)
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp h2
  simp [PEqualNP.TopForm.opnd, hpq]

lemma nfc_b31 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : PEqualNP.TopForm.NoFourCycle G) :
    ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
  rintro a b c d hac hbd ⟨h1, h2, h3, h4⟩
  have h0 := h a c hac
  have h5 : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj c w).card :=
    Finset.one_lt_card.mpr ⟨b, by simp [h1, h2.symm], d, by simp [h4.symm, h3], hbd⟩
  omega

lemma and_true_b31 {n : ℕ} {C : Circuit} (hA : PEqualNP.TopForm.IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool)
    (u v : Fin n) (hu : u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C j 0))
    (hv : v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C j 1))
    (hxu : x u = true) (hxv : x v = true) :
    val_b31 C (List.ofFn x) (n + j) = true := by
  have hrb := hA.2.1 j hj
  have h0 : PEqualNP.TopForm.opnd C j 0 < n + j := hrb _ (by rw [opnd_eq_b31 hA hj]; simp)
  have h1 : PEqualNP.TopForm.opnd C j 1 < n + j := hrb _ (by rw [opnd_eq_b31 hA hj]; simp)
  rw [val_and_b31 (n := n) (by simp) hj hop]
  intro i hi
  rw [opnd_eq_b31 hA hj] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨h0, reach_var_val_b31 x _ u (mem_orIn_reach_b31 u hu) hxu⟩
  · exact ⟨h1, reach_var_val_b31 x _ v (mem_orIn_reach_b31 v hv) hxv⟩

lemma out_true_b31 {n : ℕ} {C : Circuit} {j : ℕ} (hr : OrReaches n C C.output j)
    (x : Fin n → Bool) (hv : val_b31 C (List.ofFn x) (n + j) = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true := by
  show val_b31 C (List.ofFn x) C.output = true
  exact orStep_up_b31 (n := n) (by simp) (orReaches_reach_b31 j _ hr).1 hv

lemma part1_b31 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (hA : PEqualNP.TopForm.IsAO2 n C)
    (h1 : ∀ a1 : Fin n,
      PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false)
    (h2 : ∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 →
      PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hr : OrReaches n C C.output j) :
    (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 →
      w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧
    (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
      ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧
    ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨
      (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1) := by
  have hd : ∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 →
      w ∉ PEqualNP.TopForm.side (n := n) C j 1 := by
    intro w hw0 hw1
    have h := out_true_b31 hr _
      (and_true_b31 hA hj hop (fun k1 => decide (k1 = w)) w w hw0 hw1 (by simp) (by simp))
    rw [h1 w] at h
    cases h
  have hadj : ∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
      ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v := by
    intro u hu v hv
    by_contra hna
    have hne : u ≠ v := by
      rintro rfl
      exact hd u hu hv
    have h := out_true_b31 hr _
      (and_true_b31 hA hj hop (fun k2 => decide (k2 = u ∨ k2 = v)) u v hu hv (by simp) (by simp))
    rw [h2 u v hne hna] at h
    cases h
  exact ⟨hd, hadj, biclique_star_b31 G (nfc_b31 n G h4) _ _ hadj⟩

lemma part2_b31 {n : ℕ} (C : Circuit) (E : Finset (Fin n × Fin n))
    (hstar : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → OrReaches n C C.output i →
      ((PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1 ∨
        (PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1))
    (F : Finset ℕ)
    (hF : ∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧ (gateAt C i).op = GateOp.and ∧
      OrReaches n C C.output i ∧
      ((e.1 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C i 1) ∨
        (e.2 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧
          e.1 ∈ PEqualNP.TopForm.side (n := n) C i 1))) :
    ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ E, e3.1 ∈ T ∨ e3.2 ∈ T := by
  classical
  have hex : ∀ i : ℕ, ∃ S : Finset (Fin n), S.card ≤ 1 ∧
      (i < C.gates.length → (gateAt C i).op = GateOp.and → OrReaches n C C.output i →
        ∀ u ∈ PEqualNP.TopForm.side (n := n) C i 0,
          ∀ v ∈ PEqualNP.TopForm.side (n := n) C i 1, u ∈ S ∨ v ∈ S) := by
    intro i
    by_cases hP : i < C.gates.length ∧ (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i
    · rcases hstar i hP.1 hP.2.1 hP.2.2 with h | h
      · exact ⟨_, h, fun _ _ _ u hu v hv => Or.inl hu⟩
      · exact ⟨_, h, fun _ _ _ u hu v hv => Or.inr hv⟩
    · exact ⟨∅, by simp, fun a b c => (hP ⟨a, b, c⟩).elim⟩
  choose S hS1 hS2 using hex
  refine ⟨F.biUnion S, ?_, ?_⟩
  · calc (F.biUnion S).card ≤ ∑ i ∈ F, (S i).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ F, 1 := Finset.sum_le_sum (fun i _ => hS1 i)
      _ = F.card := by simp
  · intro e he
    obtain ⟨i, hiF, hi, hop, hr, hc⟩ := hF e he
    rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases hS2 i hi hop hr _ ha _ hb with h | h
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, hiF, h⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hiF, h⟩)
    · rcases hS2 i hi hop hr _ ha _ hb with h | h
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hiF, h⟩)
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, hiF, h⟩)


theorem s2231 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.OrReaches n C C.output j → (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 → w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧ (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 → ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1)) ∧ (∀ F : Finset ℕ, (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), ∃ i ∈ F, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i ∧ ((e.1 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C i 1) ∨ (e.2 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.1 ∈ PEqualNP.TopForm.side (n := n) C i 1))) → ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)), e3.1 ∈ T ∨ e3.2 ∈ T) := by
  intro n G _ C h4 hA h1 h2
  exact ⟨fun j hj hop hr => part1_b31 G C h4 hA h1 h2 j hj hop hr,
    fun F hF => part2_b31 C _
      (fun i hi hop hr => (part1_b31 G C h4 hA h1 h2 i hi hop hr).2.2)
      F hF⟩

end B2231

section B2233
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma split_gates_b33 (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq_b33 (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

open PEqualNP.CleanedNonEdge in
lemma orFold_length_b33 (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last_b33 (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt_b33 (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt_b33 (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt_b33 n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff_b33 (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates_b33 C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq_b33 C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length_b33]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt_b33 n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt_b33 n post _ m (by omega)]
    exact orStep_getD_lt_b33 n _ gk m (by omega)
  have h3 := orStep_mem_last_b33 n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

open PEqualNP.CleanedNonEdge in
lemma mem_le_b33 (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ x, x ∈ (orSets n C).getD k [] → x ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx
    rcases (orSets_mem_iff_b33 n C k x hk).mp hx with h | ⟨_, w, _, hn, hlt, hx2⟩
    · omega
    · have := ih (w - n) (by omega) (by omega) x hx2
      omega

open PEqualNP.CleanedNonEdge in
lemma parent_b33 (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ x, x ∈ (orSets n C).getD k [] → x ≠ k →
      ∃ p, p ∈ (orSets n C).getD k [] ∧ (gateAt C p).op = GateOp.or ∧
        n + x ∈ (gateAt C p).inputs := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx hne
    rcases (orSets_mem_iff_b33 n C k x hk).mp hx with h | ⟨hop, w, hw, hn, hlt, hx2⟩
    · exact absurd h hne
    · by_cases hxw : x = w - n
      · refine ⟨k, (orSets_mem_iff_b33 n C k k hk).mpr (Or.inl rfl), hop, ?_⟩
        have : n + x = w := by omega
        rw [this]; exact hw
      · obtain ⟨p, hp, hpop, hpin⟩ := ih (w - n) (by omega) (by omega) x hx2 hxw
        exact ⟨p, (orSets_mem_iff_b33 n C k p hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hp⟩), hpop, hpin⟩

open PEqualNP.CleanedNonEdge in
lemma orSets_length_b33 (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp [orSets, orFold_length_b33]

open PEqualNP.CleanedNonEdge in
lemma main_b33 (n : ℕ) (C : Circuit) (F : Finset ℕ)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j) :
    F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} + 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty F with hE | ⟨j0, hj0⟩
  · simp [hE]
  obtain ⟨_, _, hno, hj0r⟩ := hF j0 hj0
  have hr : C.output - n < C.gates.length := by
    by_contra hcon
    have : (orSets n C).getD (C.output - n) [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_length_b33]; omega)]
      rfl
    rw [this] at hj0r
    simp at hj0r
  set r := C.output - n with hrdef
  set S : Finset ℕ := ((orSets n C).getD r []).toFinset with hS
  set O : Finset ℕ := S.filter (fun i => (gateAt C i).op = GateOp.or) with hO
  have hT : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = (O : Set ℕ) := by
    ext i
    simp only [Set.mem_setOf_eq, hO, hS, Finset.coe_filter, List.mem_toFinset, OrReaches]
    constructor
    · rintro ⟨_, hop, _, hi⟩
      exact ⟨hi, hop⟩
    · rintro ⟨hi, hop⟩
      have := mem_le_b33 n C r hr i hi
      exact ⟨by omega, hop, hno, hi⟩
  rw [hT, Set.ncard_coe_finset]
  have hOS : O ⊆ S := Finset.filter_subset _ _
  have hFS : F ⊆ S \ O := by
    intro j hj
    obtain ⟨_, hop, _, hjr⟩ := hF j hj
    rw [Finset.mem_sdiff]
    refine ⟨by rw [hS, List.mem_toFinset]; exact hjr, ?_⟩
    rw [hO, Finset.mem_filter]
    rintro ⟨_, hor⟩
    rw [hop] at hor
    cases hor
  have hc1 := Finset.card_le_card hFS
  have hc2 := Finset.card_sdiff_add_card_eq_card hOS
  have hrS : r ∈ S := by
    rw [hS, List.mem_toFinset]
    exact (orSets_mem_iff_b33 n C r r hr).mpr (Or.inl rfl)
  have hsub : S.erase r ⊆ (O ×ˢ Finset.range 2).image
      (fun p : ℕ × ℕ => (gateAt C p.1).inputs.getD p.2 0 - n) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hxr, hxS⟩ := hx
    rw [hS, List.mem_toFinset] at hxS
    obtain ⟨p, hp, hpop, hpin⟩ := parent_b33 n C r hr x hxS hxr
    have hpr := mem_le_b33 n C r hr p hp
    have hplen : p < C.gates.length := by omega
    have hlen : (gateAt C p).inputs.length = 2 := by
      rw [gateAt_eq_b33 C p hplen]
      exact h2 _ (List.getElem_mem hplen)
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hpin
    rw [Finset.mem_image]
    refine ⟨(p, i), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_range, hO, Finset.mem_filter, hS, List.mem_toFinset]
      exact ⟨⟨hp, hpop⟩, by omega⟩
    · show (gateAt C p).inputs.getD i 0 - n = x
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hix]
      omega
  have hc3 := Finset.card_le_card hsub
  have hc4 : ((O ×ˢ Finset.range 2).image
      (fun p : ℕ × ℕ => (gateAt C p.1).inputs.getD p.2 0 - n)).card ≤ O.card * 2 := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_range]
  rw [Finset.card_erase_of_mem hrS] at hc3
  omega


theorem s2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hA hF
  exact main_b33 n C F hA.2.2 hF

end B2233

section B2234
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire_b34 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl_b34 (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire_b34 x := rfl

lemma foldl_stepWire_length_b34 (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire_b34 w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire_b34]
    omega

lemma foldl_stepWire_getD_lt_b34 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire_b34 w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire_b34 w g).length := by simp [stepWire_b34]; omega
    rw [ih (stepWire_b34 w g) hlt]
    simp [stepWire_b34, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length_b34 (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length_b34 (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl_b34, foldl_stepWire_length_b34, List.length_ofFn]

lemma split_gates_b34 (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W_b34 (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq_b34 (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate_b34 (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W_b34 n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W_b34 n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates_b34 C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq_b34 C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire_b34 (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length_b34, hpre_len]
  have hCj : W_b34 n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W_b34]
    rw [wires_eq_foldl_b34, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt_b34 post (stepWire_b34 w0 gj) (n + k) (by simp [stepWire_b34]; omega)]
    simp [stepWire_b34, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W_b34]
    rw [wires_eq_foldl_b34, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt_b34 (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length_b34 w0 i (by omega)

lemma W_input_b34 (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W_b34 n C x u = x ⟨u, hu⟩ := by
  simp only [W_b34]
  rw [wires_eq_foldl_b34, foldl_stepWire_getD_lt_b34 C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or_b34 (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W_b34 n C x (n + k) = (W_b34 n C x a || W_b34 n C x b) := by
  rw [W_gate_b34 n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and_b34 (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W_b34 n C x (n + k) = (W_b34 n C x a && W_b34 n C x b) := by
  rw [W_gate_b34 n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

def AO_b34 (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

def OrStep_b34 (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs

def OrR_b34 (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep_b34 n C)

lemma orStep_lt_b34 (n : ℕ) (C : Circuit) (hA : AO_b34 n C) (u v : ℕ) (h : OrStep_b34 n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

lemma orR_le_b34 (n : ℕ) (C : Circuit) (hA : AO_b34 n C) (u v : ℕ) (h : OrR_b34 n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt_b34 n C hA _ _ h2; omega

lemma orStep_mono_b34 (n : ℕ) (C : Circuit) (hA : AO_b34 n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep_b34 n C u v) (hv : W_b34 n C x v = true) : W_b34 n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or_b34 n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]

lemma orR_mono_b34 (n : ℕ) (C : Circuit) (hA : AO_b34 n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR_b34 n C u v) (hv : W_b34 n C x v = true) : W_b34 n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono_b34 n C hA x _ _ h1 ih

open PEqualNP.CleanedNonEdge in
lemma cnFold_length_b34 (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma cnStep_mem_last_b34 (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
      true_and]
    constructor
    · rintro (h | ⟨w, ⟨hw, hn, hlt⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, hw, hn, hlt, h⟩
    · rintro (h | ⟨w, hw, hn, hlt, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, h⟩
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.not_mem_nil, or_false, false_and]

open PEqualNP.CleanedNonEdge in
lemma cnStep_getD_lt_b34 (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma cnFold_getD_lt_b34 (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact cnStep_getD_lt_b34 n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_iff_b34 (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    g ∈ (orSets n C).getD k [] ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ g ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates_b34 C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq_b34 C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [cnFold_length_b34]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, cnFold_getD_lt_b34 n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, cnFold_getD_lt_b34 n post _ m (by omega)]
    exact cnStep_getD_lt_b34 n _ gk m (by omega)
  have h3 := cnStep_mem_last_b34 n (pre.foldl (orStep n) []) gk g
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact h⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact h⟩

open PEqualNP.CleanedNonEdge in
lemma orSets_len_b34 (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [cnFold_length_b34]
  simp

open PEqualNP.CleanedNonEdge in
lemma reaches_to_b34 (n : ℕ) (C : Circuit) :
    ∀ k g, g ∈ (orSets n C).getD k [] → g < C.gates.length ∧ OrR_b34 n C (n + k) (n + g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    have hk : k < C.gates.length := by
      by_contra hk
      have hnone : (orSets n C)[k]? = none :=
        List.getElem?_eq_none (by rw [orSets_len_b34]; omega)
      rw [List.getD_eq_getElem?_getD, hnone] at hg
      simp at hg
    rw [orSets_iff_b34 n C g k hk] at hg
    rcases hg with rfl | ⟨hop, w, hw, hn, hlt, h⟩
    · exact ⟨hk, Relation.ReflTransGen.refl⟩
    · obtain ⟨h4, h5⟩ := ih (w - n) (by omega) g h
      have hw' : n + (w - n) = w := by omega
      rw [hw'] at h5
      exact ⟨h4, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hw⟩ h5⟩

open PEqualNP.CleanedNonEdge in
lemma orReaches_iff_b34 (n : ℕ) (C : Circuit) (hA : AO_b34 n C) (w g : ℕ) :
    OrReaches n C w g ↔ (n ≤ w ∧ g < C.gates.length ∧ OrR_b34 n C w (n + g)) := by
  constructor
  · rintro ⟨hn, h⟩
    obtain ⟨h1, h2⟩ := reaches_to_b34 n C (w - n) g h
    have hw' : n + (w - n) = w := by omega
    rw [hw'] at h2
    exact ⟨hn, h1, h2⟩
  · rintro ⟨hn, hg, h⟩
    refine ⟨hn, ?_⟩
    clear hn
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have he : n + g - n = g := by omega
      rw [he, orSets_iff_b34 n C g g hg]
      exact Or.inl rfl
    | head h1 h2 ih =>
      rename_i u c
      have hle := orR_le_b34 n C hA _ _ h2
      have hlt := orStep_lt_b34 n C hA _ _ h1
      obtain ⟨k, rfl, hk, hop, hin⟩ := h1
      have he : n + k - n = k := by omega
      rw [he, orSets_iff_b34 n C g k hk]
      exact Or.inr ⟨hop, c, hin, by omega, hlt, ih⟩

lemma orIn_iff_b34 (n : ℕ) (C : Circuit) (hA : AO_b34 n C) (w : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C w ↔ OrR_b34 n C w u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hin⟩)
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail ((orReaches_iff_b34 n C hA w k).mp hr).2.2 ⟨k, rfl, hk, hop, hin⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, h1, ⟨k, rfl, hk, hop, hin⟩⟩
    · exact Or.inl h1
    · have hle := orR_le_b34 n C hA _ _ h1
      exact Or.inr ⟨k, hk, (orReaches_iff_b34 n C hA w k).mpr ⟨by omega, hk, h1⟩, hop, hin⟩

lemma ao_of_b34 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO_b34 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq_b34 C k hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h3 _ hmem)
  refine ⟨h1 _ hmem, a, b, hab, ?_, ?_⟩
  · exact h2 k hk a (by rw [hab]; simp)
  · exact h2 k hk b (by rw [hab]; simp)

theorem cone_count_b34 {α : Type*} [DecidableEq α] (n : ℕ) (S : ℕ → Finset α) (Rc : ℕ → ℕ → Prop)
    (h1 : ∀ w < n, (S w).card ≤ 1)
    (h2 : ∀ t, 2 ≤ (S (n + t)).card → ∃ p q, p < n + t ∧ q < n + t ∧ S (n + t) ⊆ S p ∪ S q ∧
      Rc (n + t) t ∧ ∀ g, Rc p g ∨ Rc q g → Rc (n + t) g) :
    ∀ t (W_b34 : Finset ℕ), (∀ w ∈ W_b34, w < n + t) → ∀ R : Finset ℕ,
      (∀ g < t, 2 ≤ (S (n + g)).card → (∃ w ∈ W_b34, Rc w g) → g ∈ R) →
      (W_b34.biUnion S).card ≤ R.card + W_b34.card := by
  intro t
  induction t with
  | zero =>
    intro W_b34 hW R _
    have e1 : (W_b34.biUnion S).card ≤ ∑ w ∈ W_b34, (S w).card := Finset.card_biUnion_le
    have e2 : ∑ w ∈ W_b34, (S w).card ≤ ∑ w ∈ W_b34, 1 :=
      Finset.sum_le_sum (fun w hw => h1 w (by have := hW w hw; omega))
    have e3 : ∑ w ∈ W_b34, 1 = W_b34.card := by simp
    omega
  | succ t ih =>
    intro W_b34 hW R hR
    by_cases hmem : n + t ∈ W_b34
    · have hpos : 0 < W_b34.card := Finset.card_pos.mpr ⟨_, hmem⟩
      have e3 := Finset.card_erase_of_mem hmem
      by_cases hc : 2 ≤ (S (n + t)).card
      · obtain ⟨p, q, hp, hq, hsub, hself, hreach⟩ := h2 t hc
        have htR : t ∈ R := hR t (by omega) hc ⟨n + t, hmem, hself⟩
        have hW2 : ∀ w ∈ insert p (insert q (W_b34.erase (n + t))), w < n + t := by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_erase] at hw
          rcases hw with rfl | rfl | ⟨hne, hw⟩
          · exact hp
          · exact hq
          · have := hW w hw
            omega
        have hR2 : ∀ g < t, 2 ≤ (S (n + g)).card →
            (∃ w ∈ insert p (insert q (W_b34.erase (n + t))), Rc w g) → g ∈ R.erase t := by
          intro g hg hcg hex
          obtain ⟨w, hw, hr⟩ := hex
          rw [Finset.mem_erase]
          refine ⟨by omega, hR g (by omega) hcg ?_⟩
          simp only [Finset.mem_insert, Finset.mem_erase] at hw
          rcases hw with rfl | rfl | ⟨hne, hw⟩
          · exact ⟨n + t, hmem, hreach g (Or.inl hr)⟩
          · exact ⟨n + t, hmem, hreach g (Or.inr hr)⟩
          · exact ⟨w, hw, hr⟩
        have key := ih (insert p (insert q (W_b34.erase (n + t)))) hW2 (R.erase t) hR2
        have hU : W_b34.biUnion S ⊆ (insert p (insert q (W_b34.erase (n + t)))).biUnion S := by
          intro x hx
          rw [Finset.mem_biUnion] at hx ⊢
          obtain ⟨w, hw, hxw⟩ := hx
          by_cases hwt : w = n + t
          · subst hwt
            rcases Finset.mem_union.mp (hsub hxw) with h | h
            · exact ⟨p, by simp, h⟩
            · exact ⟨q, by simp, h⟩
          · exact ⟨w, by simp [hwt, hw], hxw⟩
        have e1 := Finset.card_insert_le p (insert q (W_b34.erase (n + t)))
        have e2 := Finset.card_insert_le q (W_b34.erase (n + t))
        have hc2 : (R.erase t).card + 1 = R.card := Finset.card_erase_add_one htR
        have e4 := Finset.card_le_card hU
        omega
      · have hW2 : ∀ w ∈ W_b34.erase (n + t), w < n + t := by
          intro w hw
          have h5 := hW w (Finset.mem_of_mem_erase hw)
          have h6 := Finset.ne_of_mem_erase hw
          omega
        have hR2 : ∀ g < t, 2 ≤ (S (n + g)).card → (∃ w ∈ W_b34.erase (n + t), Rc w g) → g ∈ R := by
          intro g hg hcg hex
          obtain ⟨w, hw, hr⟩ := hex
          exact hR g (by omega) hcg ⟨w, Finset.mem_of_mem_erase hw, hr⟩
        have key := ih (W_b34.erase (n + t)) hW2 R hR2
        have hU : W_b34.biUnion S ⊆ (W_b34.erase (n + t)).biUnion S ∪ S (n + t) := by
          intro x hx
          rw [Finset.mem_biUnion] at hx
          obtain ⟨w, hw, hxw⟩ := hx
          rw [Finset.mem_union, Finset.mem_biUnion]
          by_cases hwt : w = n + t
          · subst hwt
            exact Or.inr hxw
          · exact Or.inl ⟨w, Finset.mem_erase.mpr ⟨hwt, hw⟩, hxw⟩
        have e4 := Finset.card_le_card hU
        have e5 := Finset.card_union_le ((W_b34.erase (n + t)).biUnion S) (S (n + t))
        omega
    · have hW2 : ∀ w ∈ W_b34, w < n + t := by
        intro w hw
        have h5 := hW w hw
        have h6 : w ≠ n + t := fun h => hmem (h ▸ hw)
        omega
      exact ih W_b34 hW2 R (fun g hg hcg hex => hR g (by omega) hcg hex)

lemma orIn_small_b34 (n : ℕ) (C : Circuit) (hA : AO_b34 n C) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h : ∀ u : Fin n, u ∈ PEqualNP.TopForm.orIn n C w → u.val = w := by
    intro u hu
    rcases Relation.ReflTransGen.cases_head ((orIn_iff_b34 n C hA w u).mp hu) with h | ⟨c, ⟨k, hk, _⟩, _⟩
    · exact h.symm
    · omega
  exact Fin.ext ((h a ha).trans (h b hb).symm)

lemma orIn_big_b34 (n : ℕ) (C : Circuit) (hA : AO_b34 n C) (t : ℕ)
    (hc : 2 ≤ (PEqualNP.TopForm.orIn n C (n + t)).card) :
    t < C.gates.length ∧ (gateAt C t).op = GateOp.or ∧ ∃ p q, p < n + t ∧ q < n + t ∧
      PEqualNP.TopForm.orIn n C (n + t) ⊆
        PEqualNP.TopForm.orIn n C p ∪ PEqualNP.TopForm.orIn n C q ∧
      PEqualNP.CleanedNonEdge.OrReaches n C (n + t) t ∧
      ∀ g, PEqualNP.CleanedNonEdge.OrReaches n C p g ∨ PEqualNP.CleanedNonEdge.OrReaches n C q g →
        PEqualNP.CleanedNonEdge.OrReaches n C (n + t) g := by
  obtain ⟨u, hu⟩ : (PEqualNP.TopForm.orIn n C (n + t)).Nonempty := Finset.card_pos.mp (by omega)
  have hstep : ∀ v : Fin n, OrR_b34 n C (n + t) v.val →
      ∃ c, OrStep_b34 n C (n + t) c ∧ OrR_b34 n C c v.val := by
    intro v hv
    rcases Relation.ReflTransGen.cases_head hv with h | h
    · have := v.isLt
      omega
    · exact h
  obtain ⟨c0, ⟨k, hk, hklen, hop, hin0⟩, _⟩ := hstep u ((orIn_iff_b34 n C hA _ u).mp hu)
  have hkt : k = t := by omega
  rw [hkt] at hklen hop
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA t hklen
  refine ⟨hklen, hop, a, b, ha, hb, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨c, ⟨k2, hk2, _, _, hin⟩, hr⟩ := hstep v ((orIn_iff_b34 n C hA _ v).mp hv)
    have hk2t : k2 = t := by omega
    rw [hk2t, hab] at hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rw [Finset.mem_union]
    rcases hin with rfl | rfl
    · exact Or.inl ((orIn_iff_b34 n C hA _ v).mpr hr)
    · exact Or.inr ((orIn_iff_b34 n C hA _ v).mpr hr)
  · exact (orReaches_iff_b34 n C hA _ _).mpr ⟨by omega, hklen, Relation.ReflTransGen.refl⟩
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨_, hgl, hr⟩ := (orReaches_iff_b34 n C hA _ _).mp hg
      exact (orReaches_iff_b34 n C hA _ _).mpr ⟨by omega, hgl,
        Relation.ReflTransGen.head ⟨t, rfl, hklen, hop, by rw [hab]; simp⟩ hr⟩
    · obtain ⟨_, hgl, hr⟩ := (orReaches_iff_b34 n C hA _ _).mp hg
      exact (orReaches_iff_b34 n C hA _ _).mpr ⟨by omega, hgl,
        Relation.ReflTransGen.head ⟨t, rfl, hklen, hop, by rw [hab]; simp⟩ hr⟩

lemma orIn_sub_b34 (n : ℕ) (C : Circuit) (hA : AO_b34 n C) (w g : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C w g) :
    PEqualNP.TopForm.orIn n C (n + g) ⊆ PEqualNP.TopForm.orIn n C w := by
  intro u hu
  obtain ⟨_, _, hr⟩ := (orReaches_iff_b34 n C hA w g).mp h
  exact (orIn_iff_b34 n C hA w u).mpr
    (Relation.ReflTransGen.trans hr ((orIn_iff_b34 n C hA _ u).mp hu))

lemma out_true_b34 (n : ℕ) (C : Circuit) (hA : AO_b34 n C) (i : ℕ) (b : Fin n)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C C.output i)
    (hb : b ∈ PEqualNP.TopForm.orIn n C (n + i)) :
    PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = b)) = true := by
  have h1 := orIn_sub_b34 n C hA _ _ hr hb
  have h2 := (orIn_iff_b34 n C hA _ b).mp h1
  have h3 := orR_mono_b34 n C hA (fun k1 => decide (k1 = b)) _ _ h2
    (by rw [W_input_b34 n C _ b.val b.isLt]; simp)
  exact h3

theorem part2_b34 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (F : Finset ℕ)
    (ctr : ℕ → Fin n) (lf : ℕ → ℕ) (hN : PEqualNP.TopForm.NoFourCycle G)
    (hI : PEqualNP.TopForm.IsAO2 n C)
    (hlf : ∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b)
    (U : Fin n → Finset (Fin n))
    (hU : ∀ c b, b ∈ U c → ∃ j ∈ F, ctr j = c ∧ b ∈ PEqualNP.TopForm.orIn n C (lf j)) :
    ∑ c : Fin n, (U c).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧
      (gateAt C i2).op = GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧
      ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  classical
  have hA := ao_of_b34 n C hI
  obtain ⟨T, hT⟩ : ∃ T, T = F.sup lf + 1 := ⟨_, rfl⟩
  obtain ⟨Rs, hRs⟩ : ∃ Rs : Fin n → Finset ℕ, ∀ c g, g ∈ Rs c ↔
      (g < T ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + g)).card ∧
        ∃ w ∈ (F.filter (fun j => ctr j = c)).image lf,
          PEqualNP.CleanedNonEdge.OrReaches n C w g) :=
    ⟨fun c => (Finset.range T).filter (fun g =>
      2 ≤ (PEqualNP.TopForm.orIn n C (n + g)).card ∧
        ∃ w ∈ (F.filter (fun j => ctr j = c)).image lf,
          PEqualNP.CleanedNonEdge.OrReaches n C w g),
      fun c g => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hper : ∀ c, (U c).card ≤ (Rs c).card + (F.filter (fun j => ctr j = c)).card := by
    intro c
    have hW : ∀ w ∈ (F.filter (fun j => ctr j = c)).image lf, w < n + T := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      have h5 := Finset.le_sup (f := lf) (Finset.mem_filter.mp hj).1
      omega
    have hR : ∀ g < T, 2 ≤ (PEqualNP.TopForm.orIn n C (n + g)).card →
        (∃ w ∈ (F.filter (fun j => ctr j = c)).image lf,
          PEqualNP.CleanedNonEdge.OrReaches n C w g) → g ∈ Rs c := by
      intro g hg hcg hex
      exact (hRs c g).mpr ⟨hg, hcg, hex⟩
    have hcc := cone_count_b34 n (PEqualNP.TopForm.orIn n C) (PEqualNP.CleanedNonEdge.OrReaches n C)
      (fun w hw => orIn_small_b34 n C hA w hw)
      (fun t hc => (orIn_big_b34 n C hA t hc).2.2) T
      ((F.filter (fun j => ctr j = c)).image lf) hW (Rs c) hR
    have hsub : U c ⊆ ((F.filter (fun j => ctr j = c)).image lf).biUnion
        (PEqualNP.TopForm.orIn n C) := by
      intro b hb
      obtain ⟨j, hj, hcj, hbj⟩ := hU c b hb
      exact Finset.mem_biUnion.mpr
        ⟨lf j, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hcj⟩, rfl⟩, hbj⟩
    have h3 := Finset.card_le_card hsub
    have h4 : ((F.filter (fun j => ctr j = c)).image lf).card ≤
        (F.filter (fun j => ctr j = c)).card := Finset.card_image_le
    omega
  have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint Rs := by
    intro c _ c2 _ hne
    show Disjoint (Rs c) (Rs c2)
    rw [Finset.disjoint_left]
    intro g hg hg2
    obtain ⟨_, hcg, w, hw, hr⟩ := (hRs c g).mp hg
    obtain ⟨_, _, w2, hw2, hr2⟩ := (hRs c2 g).mp hg2
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨j2, hj2, rfl⟩ := Finset.mem_image.mp hw2
    obtain ⟨hjF, hjc⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjF2, hjc2⟩ := Finset.mem_filter.mp hj2
    have hadj : ∀ b ∈ PEqualNP.TopForm.orIn n C (n + g), G.Adj c b ∧ G.Adj c2 b := by
      intro b hb
      have h5 := hlf j hjF b (orIn_sub_b34 n C hA _ _ hr hb)
      have h6 := hlf j2 hjF2 b (orIn_sub_b34 n C hA _ _ hr2 hb)
      rw [hjc] at h5
      rw [hjc2] at h6
      exact ⟨h5, h6⟩
    have h7 : (PEqualNP.TopForm.orIn n C (n + g)).card ≤ 1 :=
      le_trans (Finset.card_le_card (fun b hb =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj b hb⟩)) (hN c c2 hne)
    omega
  have hsumR : ∑ c : Fin n, (Rs c).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧
      (gateAt C i2).op = GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧
      ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} := by
    rw [← Finset.card_biUnion hdisj, ← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard
    · intro g hg
      rw [Finset.mem_coe, Finset.mem_biUnion] at hg
      obtain ⟨c, _, hg⟩ := hg
      obtain ⟨_, hcg, w, hw, hr⟩ := (hRs c g).mp hg
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hl, hop, _⟩ := orIn_big_b34 n C hA g hcg
      rw [Set.mem_setOf_eq]
      exact ⟨hl, hop, hcg, j, (Finset.mem_filter.mp hj).1, hr⟩
    · exact (Set.finite_lt_nat C.gates.length).subset (fun i hi => hi.1)
  have hsumF : ∑ c : Fin n, (F.filter (fun j => ctr j = c)).card = F.card :=
    (Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
  have hsum : ∑ c : Fin n, (U c).card ≤
      ∑ c : Fin n, ((Rs c).card + (F.filter (fun j => ctr j = c)).card) :=
    Finset.sum_le_sum (fun c _ => hper c)
  rw [Finset.sum_add_distrib, hsumF] at hsum
  omega


theorem s2234 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  intro n G _ C F ctr lf hN hI h1 hlf
  refine ⟨fun i _ _ hc _ hout => ?_, ?_⟩
  · obtain ⟨b, hb⟩ : (PEqualNP.TopForm.orIn n C (n + i)).Nonempty :=
      Finset.card_pos.mp (by omega)
    exact Bool.false_ne_true ((h1 b).symm.trans
      (out_true_b34 n C (ao_of_b34 n C hI) i b hout hb))
  · exact part2_b34 n G C F ctr lf hN hI hlf _
      (fun c b hb => (Finset.mem_filter.mp hb).2)

end B2234

section B2230

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
  PEqualNP.ReadK

lemma mem_insertNew_x (A : List (List ℕ)) (x v : List ℕ) (h : v ∈ insertNew A x) :
    v ∈ A ∨ v = x := by
  unfold insertNew at h
  split_ifs at h with hx
  · exact Or.inl h
  · rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)

lemma mem_foldl_insertNew_x (A : List (List ℕ)) :
    ∀ (acc : List (List ℕ)) (v : List ℕ), v ∈ A.foldl insertNew acc → v ∈ acc ∨ v ∈ A := by
  induction A with
  | nil => intro acc v h; exact Or.inl h
  | cons x A ih =>
    intro acc v h
    rw [List.foldl_cons] at h
    rcases ih _ v h with h | h
    · rcases mem_insertNew_x acc x v h with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
    · exact Or.inr (List.mem_cons_of_mem _ h)

lemma mem_andStep_x (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ t ∈ B, v = capAdd k u t := by
  unfold andStep at h
  rcases mem_foldl_insertNew_x _ _ _ h with h | h
  · simp at h
  · rw [List.mem_flatMap] at h
    obtain ⟨u, hu, h⟩ := h
    rw [List.mem_map] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨u, hu, t, ht, rfl⟩

lemma rv_snoc_and_x (gs : List Gate) (ins : List ℕ) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors ⟨gs ++ [⟨GateOp.and, ins⟩], 0⟩ n S k = readVectors ⟨gs, 0⟩ n S k ++
      [(ins.map fun i => (readVectors ⟨gs, 0⟩ n S k).getD i []).foldl (andStep k)
        [S.map fun _ => 0]] := by
  show List.foldl _ _ (gs ++ [_]) = _
  rw [List.foldl_append]
  rfl

lemma rv_snoc_or_x (gs : List Gate) (ins : List ℕ) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors ⟨gs ++ [⟨GateOp.or, ins⟩], 0⟩ n S k = readVectors ⟨gs, 0⟩ n S k ++
      [(ins.map fun i => (readVectors ⟨gs, 0⟩ n S k).getD i []).foldl
        (fun acc A => A.foldl insertNew acc) []] := by
  show List.foldl _ _ (gs ++ [_]) = _
  rw [List.foldl_append]
  rfl

lemma getD_snoc_x {α : Type} (R : List α) (X d : α) (w : ℕ) :
    (R ++ [X]).getD w d = if w < R.length then R.getD w d else if w = R.length then X else d := by
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

lemma getD_mid_x (gs : List Gate) (g : Gate) (rest : List Gate) (d : Gate) :
    (gs ++ [g] ++ rest).getD gs.length d = g := by
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (le_refl _)]
  simp

lemma getD_mem_lt_x {α : Type} (R : List (List α)) (i : ℕ) (v : α) (hv : v ∈ R.getD i []) :
    i < R.length := by
  by_contra h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hv
  simp at hv

def Good_x (n : ℕ) (C : Circuit) (a b : Fin n) (w : ℕ) (v : List ℕ) : Prop :=
  ∃ x y : ℕ, v = [x, y] ∧ 1 ≤ x + y ∧
    (x = 1 → y = 0 → a ∈ PEqualNP.TopForm.orIn n C w) ∧
    (x = 0 → y = 1 → b ∈ PEqualNP.TopForm.orIn n C w) ∧
    (x = 1 → y = 1 → ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C w j ∧
      ((a ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ b ∈ PEqualNP.TopForm.side (n := n) C j 1) ∨
        (b ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ a ∈ PEqualNP.TopForm.side (n := n) C j 1)))

lemma orIn_up_x {n : ℕ} {C : Circuit} {j i : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (u : Fin n) (hu : u ∈ PEqualNP.TopForm.orIn n C i) : u ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with h | ⟨k, hk, hr, hopk, hin⟩
  · right
    exact ⟨j, hj, (orReaches_iff_b31 n C j j).mpr ⟨hj, Or.inl rfl⟩, hop, by rw [h]; exact hi⟩
  · right
    exact ⟨k, hk, (orReaches_iff_b31 n C j k).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, hr⟩⟩, hopk, hin⟩

lemma good_up_x {n : ℕ} {C : Circuit} {a b : Fin n} {j i : ℕ} {v : List ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j) (h : Good_x n C a b i v) :
    Good_x n C a b (n + j) v := by
  obtain ⟨x, y, rfl, hxy, ha, hb, hc⟩ := h
  refine ⟨x, y, rfl, hxy, fun h1 h2 => orIn_up_x hj hop hi hlt _ (ha h1 h2),
    fun h1 h2 => orIn_up_x hj hop hi hlt _ (hb h1 h2), fun h1 h2 => ?_⟩
  obtain ⟨j', hj', hand, hr, hs⟩ := hc h1 h2
  exact ⟨j', hj', hand, (orReaches_iff_b31 n C j j').mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, hr⟩⟩, hs⟩

lemma inv_x (n : ℕ) (C : Circuit) (hA : PEqualNP.TopForm.IsAO2 n C) (a b : Fin n) (hab : a < b) :
    ∀ (gs rest : List Gate), C.gates = gs ++ rest →
      (readVectors ⟨gs, 0⟩ n [a.val, b.val] 1).length = n + gs.length ∧
      ∀ w v, v ∈ (readVectors ⟨gs, 0⟩ n [a.val, b.val] 1).getD w [] → Good_x n C a b w v := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro rest _
    have hR : readVectors ⟨[], 0⟩ n [a.val, b.val] 1 =
        (List.range n).map (leafVectors [a.val, b.val] 1) := rfl
    refine ⟨by rw [hR]; simp, ?_⟩
    intro w v hv
    rw [hR] at hv
    have hlt : w < n := by
      have := getD_mem_lt_x _ _ _ hv
      simpa using this
    have e : ((List.range n).map (leafVectors [a.val, b.val] 1)).getD w [] =
        leafVectors [a.val, b.val] 1 w := by
      simp [List.getD_eq_getElem?_getD, hlt]
    rw [e] at hv
    unfold leafVectors at hv
    have hne : a.val ≠ b.val := by
      have := Fin.lt_def.mp hab
      omega
    have hne' : a ≠ b := ne_of_lt hab
    split_ifs at hv with hm
    · simp only [List.mem_singleton] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · refine ⟨1, 0, ?_, by omega, fun _ _ => ?_, fun h _ => by omega, fun _ h => by omega⟩
        · rw [hv]; simp [hne, hne.symm, hne', hne'.symm]
        · simp [PEqualNP.TopForm.orIn]
      · refine ⟨0, 1, ?_, by omega, fun h _ => by omega, fun _ _ => ?_, fun h _ => by omega⟩
        · rw [hv]; simp [hne, hne.symm, hne', hne'.symm]
        · simp [PEqualNP.TopForm.orIn]
    · simp at hv
  | append_singleton gs g ih =>
    intro rest hC
    obtain ⟨hlen, ih2⟩ := ih (g :: rest) (by rw [hC]; simp)
    have hj : gs.length < C.gates.length := by rw [hC]; simp
    have hg : gateAt C gs.length = g := by
      show C.gates.getD gs.length _ = g
      rw [hC]
      exact getD_mid_x gs g rest _
    have hin := opnd_eq_b31 hA hj
    have hgm : g ∈ C.gates := by rw [hC]; simp
    have hs0 : ∀ u : Fin n, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C gs.length 0) →
        u ∈ PEqualNP.TopForm.side (n := n) C gs.length 0 := fun u hu => hu
    have hs1 : ∀ u : Fin n, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C gs.length 1) →
        u ∈ PEqualNP.TopForm.side (n := n) C gs.length 1 := fun u hu => hu
    generalize PEqualNP.TopForm.opnd C gs.length 0 = p at hin hs0
    generalize PEqualNP.TopForm.opnd C gs.length 1 = q at hin hs1
    have hopC : (gateAt C gs.length).op = g.op := by rw [hg]
    rw [hg] at hin
    obtain ⟨op, ins⟩ := g
    dsimp only at hin hopC
    subst hin
    rcases hA.1 _ hgm with hop | hop
    · dsimp only at hop
      subst hop
      have hsn := rv_snoc_and_x gs [p, q] n [a.val, b.val] 1
      refine ⟨by rw [hsn]; simp [hlen, Nat.add_assoc], ?_⟩
      intro w v hv
      rw [hsn, getD_snoc_x, hlen] at hv
      split_ifs at hv with h1 h2
      · exact ih2 w v hv
      · subst h2
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hv
        obtain ⟨u', hu', t, ht, rfl⟩ := mem_andStep_x _ _ _ _ hv
        obtain ⟨z, hz, u, hu, rfl⟩ := mem_andStep_x _ _ _ _ hu'
        simp only [List.mem_singleton] at hz
        subst hz
        obtain ⟨x, y, rfl, hxy, ha1, hb1, -⟩ := ih2 p u hu
        obtain ⟨x2, y2, rfl, hxy2, ha2, hb2, -⟩ := ih2 q t ht
        have hcap : capAdd 1 (capAdd 1 [0, 0] [x, y]) [x2, y2] =
            [min (min (0 + x) 2 + x2) 2, min (min (0 + y) 2 + y2) 2] := rfl
        rw [hcap]
        refine ⟨_, _, rfl, by omega, ?_, ?_, ?_⟩
        · intro e1 e2; exfalso; omega
        · intro e1 e2; exfalso; omega
        · intro e1 e2
          have hcase : (x = 1 ∧ y = 0 ∧ x2 = 0 ∧ y2 = 1) ∨ (x = 0 ∧ y = 1 ∧ x2 = 1 ∧ y2 = 0) := by
            omega
          refine ⟨gs.length, hj, hopC, (orReaches_iff_b31 n C gs.length gs.length).mpr
            ⟨hj, Or.inl rfl⟩, ?_⟩
          rcases hcase with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩
          · exact Or.inl ⟨hs0 _ (ha1 c1 c2), hs1 _ (hb2 c3 c4)⟩
          · exact Or.inr ⟨hs0 _ (hb1 c1 c2), hs1 _ (ha2 c3 c4)⟩
      · simp at hv
    · dsimp only at hop
      subst hop
      have hsn := rv_snoc_or_x gs [p, q] n [a.val, b.val] 1
      refine ⟨by rw [hsn]; simp [hlen, Nat.add_assoc], ?_⟩
      intro w v hv
      rw [hsn, getD_snoc_x, hlen] at hv
      split_ifs at hv with h1 h2
      · exact ih2 w v hv
      · subst h2
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hv
        have hinp : (gateAt C gs.length).inputs = [p, q] := by rw [hg]
        rcases mem_foldl_insertNew_x _ _ _ hv with h | h
        · rcases mem_foldl_insertNew_x _ _ _ h with h | h
          · simp at h
          · have hlt := getD_mem_lt_x _ _ _ h
            rw [hlen] at hlt
            exact good_up_x hj hopC (by rw [hinp]; simp) hlt (ih2 p v h)
        · have hlt := getD_mem_lt_x _ _ _ h
          rw [hlen] at hlt
          exact good_up_x hj hopC (by rw [hinp]; simp) hlt (ih2 q v h)
      · simp at hv

theorem s2230 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin n), PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → a < b → PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true → ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧ ((a ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ b ∈ PEqualNP.TopForm.side (n := n) C j 1) ∨ (b ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ a ∈ PEqualNP.TopForm.side (n := n) C j 1)) := by
  intro n C a b hA h1 hab hr
  obtain ⟨-, hinv⟩ := inv_x n C hA a b hab C.gates [] (by simp)
  unfold readsAtMost at hr
  rw [List.any_eq_true] at hr
  obtain ⟨v, hv, hall⟩ := hr
  have hv' : v ∈ (readVectors ⟨C.gates, 0⟩ n [a.val, b.val] 1).getD C.output [] := hv
  obtain ⟨x, y, rfl, hxy, ha, hb, hc⟩ := hinv C.output v hv'
  simp at hall
  obtain ⟨hx, hy⟩ := hall
  have hcase : (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1) := by omega
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exfalso
    have ht := reach_var_val_b31 (C := C) (fun k1 => decide (k1 = a)) C.output a
      (mem_orIn_reach_b31 a (ha e1 e2)) (by simp)
    have h1a := h1 a
    change val_b31 C (List.ofFn fun k1 => decide (k1 = a)) C.output = false at h1a
    rw [ht] at h1a
    cases h1a
  · exfalso
    have ht := reach_var_val_b31 (C := C) (fun k1 => decide (k1 = b)) C.output b
      (mem_orIn_reach_b31 b (hb e1 e2)) (by simp)
    have h1b := h1 b
    change val_b31 C (List.ofFn fun k1 => decide (k1 = b)) C.output = false at h1b
    rw [ht] at h1b
    cases h1b
  · exact hc e1 e2

end B2230

theorem glue (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (E : Finset (Fin n × Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2)
    (W : ∀ e ∈ E, ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧ ((e.1 ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C j 1) ∨ (e.2 ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ e.1 ∈ PEqualNP.TopForm.side (n := n) C j 1)))
    (S : ∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.OrReaches n C C.output j → (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 → w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧ (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 → ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1))
    (Cov : ∀ F : Finset ℕ, (∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i ∧ ((e.1 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C i 1) ∨ (e.2 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.1 ∈ PEqualNP.TopForm.side (n := n) C i 1))) → ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ E, e3.1 ∈ T ∨ e3.2 ∈ T)
    (Cnt : ∀ F : Finset ℕ, (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1)
    (Srv : ∀ (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card) :
    ∃ T : Finset (Fin n), (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧ E.card + T.card ≤ C.size + 1 := by
  classical
  rcases E.eq_empty_or_nonempty with hE | ⟨e0, he0⟩
  · subst hE
    exact ⟨∅, by simp, by simp⟩
  have : Nonempty (Fin n) := ⟨e0.1⟩
  choose! w hwlt hwand hwreach hwside using W
  have hFmem : ∀ j ∈ E.image w, ∃ e ∈ E, w e = j := fun j hj => by
    simpa using hj
  have key : ∀ j ∈ E.image w, ∃ c : Fin n, ∃ l : ℕ,
      (∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C l → G.Adj c b) ∧
      (∀ e ∈ E, w e = j → (e.1 = c ∧ e.2 ∈ PEqualNP.TopForm.orIn n C l) ∨
        (e.2 = c ∧ e.1 ∈ PEqualNP.TopForm.orIn n C l)) := by
    intro j hj
    obtain ⟨e1, he1, rfl⟩ := hFmem j hj
    obtain ⟨hdis, hadj, hcard⟩ := S (w e1) (hwlt e1 he1) (hwand e1 he1) (hwreach e1 he1)
    have hne0 : ∃ c, c ∈ PEqualNP.TopForm.side (n := n) C (w e1) 0 := by
      rcases hwside e1 he1 with h | h
      · exact ⟨_, h.1⟩
      · exact ⟨_, h.1⟩
    have hne1 : ∃ c, c ∈ PEqualNP.TopForm.side (n := n) C (w e1) 1 := by
      rcases hwside e1 he1 with h | h
      · exact ⟨_, h.2⟩
      · exact ⟨_, h.2⟩
    rcases hcard with hc | hc
    · obtain ⟨c, hcm⟩ := hne0
      have huniq := Finset.card_le_one.mp hc
      refine ⟨c, PEqualNP.TopForm.opnd C (w e1) 1, fun b hb => hadj c hcm b hb, ?_⟩
      intro e he hwe
      have hs := hwside e he
      rw [hwe] at hs
      rcases hs with h | h
      · exact Or.inl ⟨huniq _ h.1 _ hcm, h.2⟩
      · exact Or.inr ⟨huniq _ h.1 _ hcm, h.2⟩
    · obtain ⟨c, hcm⟩ := hne1
      have huniq := Finset.card_le_one.mp hc
      refine ⟨c, PEqualNP.TopForm.opnd C (w e1) 0, fun b hb => (hadj b hb c hcm).symm, ?_⟩
      intro e he hwe
      have hs := hwside e he
      rw [hwe] at hs
      rcases hs with h | h
      · exact Or.inr ⟨huniq _ h.2 _ hcm, h.1⟩
      · exact Or.inl ⟨huniq _ h.2 _ hcm, h.1⟩
  choose! ctr lf hadj hcov using key
  have hFprop : ∀ j ∈ E.image w, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j := by
    intro j hj
    obtain ⟨e1, he1, rfl⟩ := hFmem j hj
    exact ⟨hwlt e1 he1, hwand e1 he1, hwreach e1 he1⟩
  obtain ⟨T, hTc, hTcov⟩ := Cov (E.image w) (fun e he =>
    ⟨w e, Finset.mem_image_of_mem w he, hwlt e he, hwand e he, hwreach e he, hwside e he⟩)
  have hcnt := Cnt (E.image w) hFprop
  obtain ⟨hs1, hs2⟩ := Srv (E.image w) ctr lf hadj
  refine ⟨T, hTcov, ?_⟩
  have hinj : E.card ≤ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ E.image w, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn
      (fun e : Fin n × Fin n => if e.1 = ctr (w e) ∧ e.2 ∈ PEqualNP.TopForm.orIn n C (lf (w e))
        then (⟨e.1, e.2⟩ : (_ : Fin n) × Fin n) else ⟨e.2, e.1⟩) ?_ ?_
    · intro e he
      have he' : e ∈ E := he
      have hm : w e ∈ E.image w := Finset.mem_image_of_mem w he'
      show (if e.1 = ctr (w e) ∧ e.2 ∈ PEqualNP.TopForm.orIn n C (lf (w e))
        then (⟨e.1, e.2⟩ : (_ : Fin n) × Fin n) else ⟨e.2, e.1⟩) ∈ _
      split_ifs with h
      · simp only [Finset.coe_sigma, Finset.coe_univ, Set.mem_sigma_iff, Set.mem_univ, true_and,
          Finset.mem_coe, Finset.mem_filter, Finset.mem_univ]
        exact ⟨w e, hm, h.1.symm, h.2⟩
      · rcases hcov (w e) hm e he' rfl with h' | h'
        · exact absurd h' h
        · simp only [Finset.coe_sigma, Finset.coe_univ, Set.mem_sigma_iff, Set.mem_univ, true_and,
            Finset.mem_coe, Finset.mem_filter, Finset.mem_univ]
          exact ⟨w e, hm, h'.1.symm, h'.2⟩
    · intro e he e' he' heq
      have h1 := hlt e he
      have h2 := hlt e' he'
      simp only at heq
      split_ifs at heq with ha hb hb
      · simp only [Sigma.mk.injEq, heq_eq_eq] at heq
        exact Prod.ext heq.1 heq.2
      · simp only [Sigma.mk.injEq, heq_eq_eq] at heq
        rw [heq.1, heq.2] at h1
        exact absurd h1 (lt_asymm h2)
      · simp only [Sigma.mk.injEq, heq_eq_eq] at heq
        rw [heq.1, heq.2] at h1
        exact absurd h1 (lt_asymm h2)
      · simp only [Sigma.mk.injEq, heq_eq_eq] at heq
        exact Prod.ext heq.2 heq.1
  have hfinR : ((Finset.range C.gates.length : Finset ℕ) : Set ℕ).Finite := Finset.finite_toSet _
  have hsubO : {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} ⊆ ((Finset.range C.gates.length : Finset ℕ) : Set ℕ) := by
    intro i hi
    simpa using hi.1
  have hsubS : {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ E.image w, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} ⊆ ((Finset.range C.gates.length : Finset ℕ) : Set ℕ) := by
    intro i hi
    simpa using hi.1
  have hfinO := hfinR.subset hsubO
  have hfinS := hfinR.subset hsubS
  have hd1 : Disjoint {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ E.image w, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} := by
    rw [Set.disjoint_left]
    intro i hO hS
    exact hs1 i hS.1 hS.2.1 hS.2.2.1 hS.2.2.2 hO.2.2
  have hd2 : Disjoint ({i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} ∪ {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ E.image w, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2}) ((E.image w : Finset ℕ) : Set ℕ) := by
    rw [Set.disjoint_left]
    intro i hOS hF
    have hand := (hFprop i (Finset.mem_coe.mp hF)).2.1
    rcases hOS with h | h
    · have hor := h.2.1
      rw [hand] at hor
      cases hor
    · have hor := h.2.1
      rw [hand] at hor
      cases hor
  have hsubU : ({i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} ∪ {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ E.image w, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2}) ∪ ((E.image w : Finset ℕ) : Set ℕ) ⊆ ((Finset.range C.gates.length : Finset ℕ) : Set ℕ) := by
    intro i hi
    rcases hi with (h | h) | h
    · exact hsubO h
    · exact hsubS h
    · simpa using (hFprop i (Finset.mem_coe.mp h)).1
  have htot := Set.ncard_le_ncard hsubU hfinR
  rw [Set.ncard_union_eq hd2 (hfinO.union hfinS) (Finset.finite_toSet _),
    Set.ncard_union_eq hd1 hfinO hfinS, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Finset.card_range] at htot
  have hsz : C.size = C.gates.length := rfl
  omega

end PEqualNP.Outside.L_meta_2235

theorem PEqualNP.Outside.L_meta_2235 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → ∃ T : Finset (Fin n), (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), e.1 ∈ T ∨ e.2 ∈ T) ∧ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 hA h1 h2
  have h31 := PEqualNP.Outside.L_meta_2235.s2231 n G C h4 hA h1 h2
  exact PEqualNP.Outside.L_meta_2235.glue n G C _ (fun e he => (Finset.mem_filter.mp he).2.1)
    (fun e he => PEqualNP.Outside.L_meta_2235.s2230 n C e.1 e.2 hA h1 (Finset.mem_filter.mp he).2.1
      (Finset.mem_filter.mp he).2.2.2)
    h31.1 h31.2
    (fun F hF => PEqualNP.Outside.L_meta_2235.s2233 n C F hA hF)
    (fun F ctr lf h => PEqualNP.Outside.L_meta_2235.s2234 n G C F ctr lf h4 hA h1 h)
