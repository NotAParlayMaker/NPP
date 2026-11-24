import Mathlib
import PEqualNP.Defs

-- Counting and equality lemmas adapted from 1213420484's PR 5102 for L-meta-2069.
-- The final argument adapts these lemmas to the exact statement of L-meta-2613.

namespace PEqualNP.Outside.L_meta_2613_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

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

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

lemma isAnd_iff (op : GateOp) : isAnd op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAnd]

lemma isOr_iff (op : GateOp) : isOr op = true ↔ op = GateOp.or := by
  cases op <;> simp [isOr]

def val (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wires_len (C : Circuit) (x : Fin 26 → Bool) :
    (C.wires (List.ofFn x)).length = 26 + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma val_input (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) (hw : w < 26) :
    val C x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn]

def op0 (C : Circuit) (k : ℕ) : ℕ := (gateAt C k).inputs.getD 0 0
def op1 (C : Circuit) (k : ℕ) : ℕ := (gateAt C k).inputs.getD 1 0

def ValidGates (C : Circuit) : Prop :=
  ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ (a b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + k ∧ b < 26 + k

def D13 : Finset (Fin 13) :=
  {(0 : Fin 13), (1 : Fin 13), (3 : Fin 13), (9 : Fin 13)}

def Good (C : Circuit) : Prop :=
  C.gates.length ≤ 64 ∧
  ValidGates C ∧
  (∀ x : Fin 26 → Bool, val C x C.output = true ↔
    ∃ p l : Fin 13, p - l ∈ D13 ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) ∧
  (∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
    ∀ x : Fin 26 → Bool, val C x (26 + k) = true → val C x C.output = true)

lemma gateAt_some {C : Circuit} {k : ℕ} {g : Gate} (h : C.gates[k]? = some g) :
    gateAt C k = g := by
  simp [gateAt, List.getD_eq_getElem?_getD, h]

lemma gate_spec {C : Circuit} (hV : ValidGates C) {k : ℕ} (hk : k < C.gates.length) :
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    (gateAt C k).inputs = [op0 C k, op1 C k] ∧
    op0 C k ≠ op1 C k ∧ op0 C k < 26 + k ∧ op1 C k < 26 + k := by
  have hg : C.gates[k]? = some (C.gates[k]) := List.getElem?_eq_getElem hk
  obtain ⟨hop, a, b, hin, hne, ha, hb⟩ := hV k _ hg
  have hgk : gateAt C k = C.gates[k] := gateAt_some hg
  have h0 : op0 C k = a := by simp [op0, hgk, hin]
  have h1 : op1 C k = b := by simp [op1, hgk, hin]
  rw [h0, h1, hgk]
  exact ⟨hop, hin, hne, ha, hb⟩

lemma val_gate {C : Circuit} (hV : ValidGates C) (x : Fin 26 → Bool) {k : ℕ}
    (hk : k < C.gates.length) :
    val C x (26 + k) = (gateAt C k).op.eval [val C x (op0 C k), val C x (op1 C k)] := by
  obtain ⟨_, hin, _, h0, h1⟩ := gate_spec hV hk
  have h := foldl_char C.gates (List.ofFn x) k hk
  simp only [List.length_ofFn] at h
  unfold val gateAt at *
  rw [wires_eq, h, hin]
  simp [h0, h1]

lemma val_and {C : Circuit} (hV : ValidGates C) (x : Fin 26 → Bool) {k : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) :
    val C x (26 + k) = (val C x (op0 C k) && val C x (op1 C k)) := by
  rw [val_gate hV x hk, hop]
  simp [GateOp.eval]

lemma val_or {C : Circuit} (hV : ValidGates C) (x : Fin 26 → Bool) {k : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) :
    val C x (26 + k) = (val C x (op0 C k) || val C x (op1 C k)) := by
  rw [val_gate hV x hk, hop]
  simp [GateOp.eval]

def pgAdj (u v : Fin 26) : Bool :=
  if hu : u.val < 13 then
    if hv : 13 ≤ v.val then
      decide ((⟨u.val, hu⟩ : Fin 13) - ⟨v.val - 13, by omega⟩ ∈ D13)
    else false
  else
    if hv : v.val < 13 then
      decide ((⟨v.val, hv⟩ : Fin 13) - ⟨u.val - 13, by omega⟩ ∈ D13)
    else false

def nbr (u : Fin 26) : Finset (Fin 26) :=
  Finset.univ.filter (fun v => pgAdj u v = true)

def E52 : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter (fun pl => pl.1 - pl.2 ∈ D13)

def toEdge (u v : Fin 26) : Fin 13 × Fin 13 :=
  if hu : u.val < 13 then
    (⟨u.val, hu⟩, ⟨(v.val - 13) % 13, Nat.mod_lt _ (by omega)⟩)
  else
    (⟨v.val % 13, Nat.mod_lt _ (by omega)⟩, ⟨(u.val - 13) % 13, Nat.mod_lt _ (by omega)⟩)

lemma pgAdj_symm : ∀ u v : Fin 26, pgAdj u v = pgAdj v u := by decide
lemma pgAdj_irrefl : ∀ u : Fin 26, pgAdj u u = false := by decide
lemma nbr_card : ∀ u : Fin 26, (nbr u).card = 4 := by decide
lemma c4_free : ∀ u v : Fin 26, u ≠ v → (nbr u ∩ nbr v).card ≤ 1 := by decide
lemma E52_card : E52.card = 52 := by decide
lemma toEdge_symm : ∀ u v : Fin 26, pgAdj u v = true → toEdge u v = toEdge v u := by decide
lemma toEdge_mem : ∀ u v : Fin 26, pgAdj u v = true → toEdge u v ∈ E52 := by decide
lemma toEdge_castAdd_natAdd : ∀ p l : Fin 13,
    toEdge (Fin.castAdd 13 p) (Fin.natAdd 13 l) = (p, l) := by decide
lemma toEdge_natAdd_castAdd : ∀ p l : Fin 13,
    toEdge (Fin.natAdd 13 l) (Fin.castAdd 13 p) = (p, l) := by decide
lemma pgAdj_castAdd_natAdd : ∀ p l : Fin 13,
    pgAdj (Fin.castAdd 13 p) (Fin.natAdd 13 l) = decide (p - l ∈ D13) := by decide

lemma pgAdj_iff (u v : Fin 26) :
    pgAdj u v = true ↔
      ∃ p l : Fin 13, p - l ∈ D13 ∧
        ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨
         (u = Fin.natAdd 13 l ∧ v = Fin.castAdd 13 p)) := by
  constructor
  · intro h
    unfold pgAdj at h
    split_ifs at h with hu hv hv2
    · refine ⟨⟨u.val, hu⟩, ⟨v.val - 13, by omega⟩, of_decide_eq_true h, Or.inl ⟨?_, ?_⟩⟩
      · ext; simp
      · ext; simp; omega
    · refine ⟨⟨v.val, hv2⟩, ⟨u.val - 13, by omega⟩, of_decide_eq_true h, Or.inr ⟨?_, ?_⟩⟩
      · ext; simp; omega
      · ext; simp
  · rintro ⟨p, l, hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · rw [pgAdj_castAdd_natAdd]; exact decide_eq_true hpl
    · rw [pgAdj_symm, pgAdj_castAdd_natAdd]; exact decide_eq_true hpl

def one (v : Fin 26) : Fin 26 → Bool := fun i => decide (i = v)
def pair (u v : Fin 26) : Fin 26 → Bool := fun i => decide (i = u ∨ i = v)

def supp (C : Circuit) (w : ℕ) : Finset (Fin 26) :=
  Finset.univ.filter (fun v => val C (one v) w = true)

lemma val_one_out {C : Circuit} (hG : Good C) (v : Fin 26) :
    val C (one v) C.output = false := by
  by_contra h
  have ht : val C (one v) C.output = true := Bool.eq_true_of_not_eq_false h
  obtain ⟨p, l, _, hp, hl⟩ := (hG.2.2.1 (one v)).1 ht
  simp only [one, decide_eq_true_eq] at hp hl
  have heq := congrArg Fin.val (hp.trans hl.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
  have := p.isLt
  omega

lemma val_pair_out {C : Circuit} (hG : Good C) (u v : Fin 26) :
    val C (pair u v) C.output = pgAdj u v := by
  rw [Bool.eq_iff_iff, hG.2.2.1 (pair u v), pgAdj_iff]
  constructor
  · rintro ⟨p, l, hpl, hp, hl⟩
    simp only [pair, decide_eq_true_eq] at hp hl
    rcases hp with hp | hp <;> rcases hl with hl | hl
    · have heq := congrArg Fin.val (hp.trans hl.symm)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
      have := p.isLt; omega
    · exact ⟨p, l, hpl, Or.inl ⟨hp.symm, hl.symm⟩⟩
    · exact ⟨p, l, hpl, Or.inr ⟨hl.symm, hp.symm⟩⟩
    · have heq := congrArg Fin.val (hp.trans hl.symm)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
      have := p.isLt; omega
  · rintro ⟨p, l, hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨p, l, hpl, by simp [pair], by simp [pair]⟩
    · exact ⟨p, l, hpl, by simp [pair], by simp [pair]⟩

lemma out_bounds {C : Circuit} (hG : Good C) :
    26 ≤ C.output ∧ C.output < 26 + C.gates.length := by
  constructor
  · by_contra hlt
    push Not at hlt
    have hv := val_one_out hG ⟨C.output, hlt⟩
    rw [val_input C (one ⟨C.output, hlt⟩) C.output hlt] at hv
    simp [one] at hv
  · by_contra hge
    push Not at hge
    have hp : val C (pair 0 13) C.output = true := by
      rw [val_pair_out hG 0 13]; decide
    unfold val at hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at hp
    simp at hp

lemma supp_out {C : Circuit} (hG : Good C) : supp C C.output = ∅ := by
  ext v
  simp [supp, val_one_out hG v]

lemma supp_input (C : Circuit) {w : ℕ} (hw : w < 26) :
    supp C w = {⟨w, hw⟩} := by
  ext v
  simp [supp, val_input C _ w hw, one, eq_comm]

lemma supp_and {C : Circuit} (hG : Good C) {k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) :
    supp C (26 + k) = ∅ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro h
  have := hG.2.2.2 k hk hop (one v) h
  rw [val_one_out hG v] at this
  exact Bool.false_ne_true this

lemma supp_or {C : Circuit} (hV : ValidGates C) {k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) :
    supp C (26 + k) = supp C (op0 C k) ∪ supp C (op1 C k) := by
  ext v
  simp [supp, val_or hV (one v) hk hop]

lemma val_of_eval_false {C : Circuit} (hG : Good C) (x : Fin 26 → Bool)
    (hx : val C x C.output = false) :
    ∀ w < 26 + C.gates.length, val C x w = true ↔ ∃ v ∈ supp C w, x v = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    rcases Nat.lt_or_ge w 26 with hlt | hge
    · rw [val_input C x w hlt, supp_input C hlt]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, _, _, h0, h1⟩ := gate_spec hG.2.1 hk
      rcases hop with hop | hop
      · rw [supp_and hG hk hop]
        simp only [Finset.notMem_empty, false_and, exists_false, iff_false]
        intro h
        have := hG.2.2.2 k hk hop x h
        rw [hx] at this
        exact Bool.false_ne_true this
      · rw [val_or hG.2.1 x hk hop, supp_or hG.2.1 hk hop, Bool.or_eq_true,
            ih (op0 C k) h0 (by omega), ih (op1 C k) h1 (by omega)]
        constructor
        · rintro (⟨v, hv, hxv⟩ | ⟨v, hv, hxv⟩)
          · exact ⟨v, Finset.mem_union_left _ hv, hxv⟩
          · exact ⟨v, Finset.mem_union_right _ hv, hxv⟩
        · rintro ⟨v, hv, hxv⟩
          rcases Finset.mem_union.1 hv with hv | hv
          · exact Or.inl ⟨v, hv, hxv⟩
          · exact Or.inr ⟨v, hv, hxv⟩

lemma and_adj {C : Circuit} (hG : Good C) {k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) {u v : Fin 26}
    (hu : u ∈ supp C (op0 C k)) (hv : v ∈ supp C (op1 C k)) :
    pgAdj u v = true := by
  by_contra h
  have hf : pgAdj u v = false := Bool.eq_false_iff.2 h
  have hout : val C (pair u v) C.output = false := by
    rw [val_pair_out hG u v, hf]
  obtain ⟨_, _, _, h0, h1⟩ := gate_spec hG.2.1 hk
  have ha : val C (pair u v) (op0 C k) = true :=
    (val_of_eval_false hG (pair u v) hout (op0 C k) (by omega)).2 ⟨u, hu, by simp [pair]⟩
  have hb : val C (pair u v) (op1 C k) = true :=
    (val_of_eval_false hG (pair u v) hout (op1 C k) (by omega)).2 ⟨v, hv, by simp [pair]⟩
  have hkv : val C (pair u v) (26 + k) = true := by
    rw [val_and hG.2.1 (pair u v) hk hop, ha, hb]; rfl
  have := hG.2.2.2 k hk hop (pair u v) hkv
  rw [hout] at this
  exact Bool.false_ne_true this

def outG (C : Circuit) : ℕ := C.output - 26

def Used (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k => k = outG C ∨ InCone 26 C k (outG C))

def Mset (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k =>
    isAnd (gateAt C k).op = true ∧ (supp C (op0 C k)).Nonempty ∧ (supp C (op1 C k)).Nonempty)

def Aless (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k =>
    isAnd (gateAt C k).op = true ∧ (supp C (op0 C k) = ∅ ∨ supp C (op1 C k) = ∅))

def Oclean (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k =>
    isOr (gateAt C k).op = true ∧ supp C (op0 C k) = ∅ ∧ supp C (op1 C k) = ∅)

def Omix (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k =>
    isOr (gateAt C k).op = true ∧
      ((supp C (op0 C k) = ∅ ∧ (supp C (op1 C k)).Nonempty) ∨
       ((supp C (op0 C k)).Nonempty ∧ supp C (op1 C k) = ∅)))

def Opure (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k =>
    isOr (gateAt C k).op = true ∧ (supp C (op0 C k)).Nonempty ∧ (supp C (op1 C k)).Nonempty)

def Mused (C : Circuit) : Finset ℕ := Mset C ∩ Used C
def AlessU (C : Circuit) : Finset ℕ := Aless C ∩ Used C
def OcleanU (C : Circuit) : Finset ℕ := Oclean C ∩ Used C
def OmixU (C : Circuit) : Finset ℕ := Omix C ∩ Used C
def OpureU (C : Circuit) : Finset ℕ := Opure C ∩ Used C
def CleanUsed (C : Circuit) : Finset ℕ := (Used C).filter (fun k => supp C (26 + k) = ∅)

def cw (C : Circuit) (j : ℕ) : ℕ :=
  if (supp C (op0 C j)).card = 1 then op0 C j else op1 C j

def lw (C : Circuit) (j : ℕ) : ℕ :=
  if (supp C (op0 C j)).card = 1 then op1 C j else op0 C j

def center (C : Circuit) (j : ℕ) : Fin 26 :=
  if h : (supp C (cw C j)).Nonempty then (supp C (cw C j)).min' h else 0

def Mc (C : Circuit) (c : Fin 26) : Finset ℕ :=
  (Mused C).filter (fun j => center C j = c)

def Uc (C : Circuit) (c : Fin 26) : Finset (Fin 26) :=
  (Mc C c).biUnion (fun j => supp C (lw C j))

def Hc (C : Circuit) (c : Fin 26) : Finset ℕ :=
  (Opure C).filter (fun k => supp C (26 + k) ⊆ nbr c ∧ 2 ≤ (supp C (26 + k)).card)

def readersUsed (C : Circuit) (k : ℕ) : Finset ℕ :=
  (Used C).filter (fun q => 26 + k ∈ (gateAt C q).inputs)

def cleanSlots (C : Circuit) (q : ℕ) : Finset ℕ :=
  ((CleanUsed C).erase (outG C)).filter (fun k => 26 + k ∈ (gateAt C q).inputs)

def cleanIn (C : Circuit) (q : ℕ) : ℕ :=
  (if supp C (op0 C q) = ∅ then 1 else 0) + (if supp C (op1 C q) = ∅ then 1 else 0)

lemma and_star {C : Circuit} (hG : Good C) {j : ℕ} (hj : j ∈ Mset C) :
    (supp C (op0 C j)).card = 1 ∨ (supp C (op1 C j)).card = 1 := by
  simp only [Mset, Finset.mem_filter, Finset.mem_range, isAnd_iff] at hj
  obtain ⟨hjl, hop, h0ne, h1ne⟩ := hj
  by_contra h
  push Not at h
  have h0gt : 1 < (supp C (op0 C j)).card := by
    have := Finset.card_pos.2 h0ne; omega
  have h1gt : 1 < (supp C (op1 C j)).card := by
    have := Finset.card_pos.2 h1ne; omega
  obtain ⟨u₁, hu₁, u₂, hu₂, hune⟩ := Finset.one_lt_card.1 h0gt
  obtain ⟨v₁, hv₁, v₂, hv₂, hvne⟩ := Finset.one_lt_card.1 h1gt
  have hmem1 : v₁ ∈ nbr u₁ ∩ nbr u₂ := by
    simp only [Finset.mem_inter, nbr, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨and_adj hG hjl hop hu₁ hv₁, and_adj hG hjl hop hu₂ hv₁⟩
  have hmem2 : v₂ ∈ nbr u₁ ∩ nbr u₂ := by
    simp only [Finset.mem_inter, nbr, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨and_adj hG hjl hop hu₁ hv₂, and_adj hG hjl hop hu₂ hv₂⟩
  have hlt : 1 < (nbr u₁ ∩ nbr u₂).card := Finset.one_lt_card.2 ⟨v₁, hmem1, v₂, hmem2, hvne⟩
  have hle := c4_free u₁ u₂ hune
  omega

lemma cw_lw_spec {C : Circuit} (hG : Good C) {j : ℕ} (hj : j ∈ Mset C) :
    supp C (cw C j) = {center C j} ∧
    supp C (lw C j) ⊆ nbr (center C j) ∧
    ((cw C j = op0 C j ∧ lw C j = op1 C j) ∨ (cw C j = op1 C j ∧ lw C j = op0 C j)) := by
  have hst := and_star hG hj
  simp only [Mset, Finset.mem_filter, Finset.mem_range, isAnd_iff] at hj
  obtain ⟨hjl, hop, _, _⟩ := hj
  have hcard1 : (supp C (cw C j)).card = 1 := by
    unfold cw
    split_ifs with h
    · exact h
    · exact hst.resolve_left h
  have hne : (supp C (cw C j)).Nonempty := Finset.card_pos.1 (by omega)
  have hsing : supp C (cw C j) = {center C j} := by
    obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hcard1
    have hce : center C j = c := by
      unfold center
      rw [dite_eq_left hne]
      have hmem : (supp C (cw C j)).min' hne ∈ ({c} : Finset (Fin 26)) :=
        hc ▸ Finset.min'_mem _ hne
      exact Finset.mem_singleton.1 hmem
    rw [hc, hce]
  have hpair : (cw C j = op0 C j ∧ lw C j = op1 C j) ∨ (cw C j = op1 C j ∧ lw C j = op0 C j) := by
    unfold cw lw
    split_ifs <;> simp
  have hsub : supp C (lw C j) ⊆ nbr (center C j) := by
    intro v hv
    simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and]
    have hc : center C j ∈ supp C (cw C j) := by rw [hsing]; simp
    rcases hpair with ⟨hcw, hlw⟩ | ⟨hcw, hlw⟩
    · rw [hcw] at hc; rw [hlw] at hv
      exact and_adj hG hjl hop hc hv
    · rw [hcw] at hc; rw [hlw] at hv
      rw [pgAdj_symm]
      exact and_adj hG hjl hop hv hc
  exact ⟨hsing, hsub, hpair⟩

lemma outG_spec {C : Circuit} (hG : Good C) :
    26 + outG C = C.output ∧ outG C < C.gates.length ∧ outG C ∈ Used C := by
  have ⟨h1, h2⟩ := out_bounds hG
  have heq : 26 + outG C = C.output := by unfold outG; omega
  have hlt : outG C < C.gates.length := by omega
  have hmem : outG C ∈ Used C := by
    simp [Used, hlt]
  exact ⟨heq, hlt, hmem⟩

lemma used_le_outG {C : Circuit} {q : ℕ} (hq : q ∈ Used C) : q ≤ outG C := by
  simp only [Used, Finset.mem_filter, Finset.mem_range] at hq
  rcases hq.2 with rfl | hc
  · exact le_rfl
  · exact Nat.le_of_lt (inCone_lt 26 C q (outG C) hc).1

lemma used_closed {C : Circuit} (hG : Good C) {k : ℕ} (hk : k ∈ Used C)
    {w : ℕ} (hw : w ∈ (gateAt C k).inputs) :
    w < 26 ∨ (26 ≤ w ∧ w - 26 ∈ Used C) := by
  rcases Nat.lt_or_ge w 26 with hlt | hge
  · exact Or.inl hlt
  · right
    refine ⟨hge, ?_⟩
    simp only [Used, Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨hkl, hko⟩ := hk
    obtain ⟨_, hin, _, h0, h1⟩ := gate_spec hG.2.1 hkl
    have hwlt : w < 26 + k := by
      rw [hin] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    have hsub : 26 + (w - 26) = w := by omega
    have hic : InCone 26 C (w - 26) k := by
      rw [inCone_iff]
      exact ⟨hkl, w - 26, by omega, by rwa [hsub], Or.inl rfl⟩
    refine ⟨by omega, Or.inr ?_⟩
    rcases hko with rfl | hko
    · exact hic
    · exact inCone_trans 26 C (w - 26) k hic (outG C) hko

lemma used_has_reader_aux {C : Circuit} (k : ℕ) :
    ∀ j, InCone 26 C k j → (j = outG C ∨ InCone 26 C j (outG C)) →
      ∃ q ∈ Used C, 26 + k ∈ (gateAt C q).inputs := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hkj hjout
    rw [inCone_iff] at hkj
    obtain ⟨hjl, r, hrj, hrin, rfl | hkr⟩ := hkj
    · exact ⟨j, by simp [Used, hjl, hjout], hrin⟩
    · have hric : InCone 26 C r j := by
        rw [inCone_iff]
        exact ⟨hjl, r, hrj, hrin, Or.inl rfl⟩
      have hrout : r = outG C ∨ InCone 26 C r (outG C) := by
        right
        rcases hjout with rfl | hjout
        · exact hric
        · exact inCone_trans 26 C r j hric (outG C) hjout
      exact ih r hrj hkr hrout

lemma used_has_reader {C : Circuit} {k : ℕ} (hk : k ∈ Used C) (hne : k ≠ outG C) :
    (readersUsed C k).Nonempty := by
  simp only [Used, Finset.mem_filter, Finset.mem_range] at hk
  have hic : InCone 26 C k (outG C) := hk.2.resolve_left hne
  obtain ⟨q, hq, hin⟩ := used_has_reader_aux k (outG C) hic (Or.inl rfl)
  exact ⟨q, by simp [readersUsed, hq, hin]⟩

lemma val_pair_before_and {C : Circuit} (hG : Good C) (u v : Fin 26) (bound : ℕ)
    (hno : ∀ k ∈ Used C, k < bound → (gateAt C k).op = GateOp.and →
      val C (pair u v) (26 + k) = false) :
    ∀ w < 26 + bound, w < 26 + C.gates.length →
      (w < 26 ∨ (26 ≤ w ∧ w - 26 ∈ Used C)) →
      val C (pair u v) w = true → u ∈ supp C w ∨ v ∈ supp C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwb hwl hwu hval
    rcases Nat.lt_or_ge w 26 with hlt | hge
    · rw [val_input C (pair u v) w hlt] at hval
      simp only [pair, decide_eq_true_eq] at hval
      rw [supp_input C hlt]
      rcases hval with hval | hval
      · exact Or.inl (by simp [hval])
      · exact Or.inr (by simp [hval])
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hkU : k ∈ Used C := by
        rcases hwu with hwu | ⟨_, hwu⟩
        · omega
        · simpa using hwu
      have hkl : k < C.gates.length := by omega
      obtain ⟨hop, hin, _, h0, h1⟩ := gate_spec hG.2.1 hkl
      rcases hop with hop | hop
      · have hf := hno k hkU (by omega) hop
        rw [hf] at hval
        exact absurd hval Bool.false_ne_true
      · rw [val_or hG.2.1 (pair u v) hkl hop, Bool.or_eq_true] at hval
        rw [supp_or hG.2.1 hkl hop]
        have h0in : op0 C k ∈ (gateAt C k).inputs := by rw [hin]; simp
        have h1in : op1 C k ∈ (gateAt C k).inputs := by rw [hin]; simp
        rcases hval with hval | hval
        · rcases ih (op0 C k) h0 (by omega) (by omega) (used_closed hG hkU h0in) hval with h | h
          · exact Or.inl (Finset.mem_union_left _ h)
          · exact Or.inr (Finset.mem_union_left _ h)
        · rcases ih (op1 C k) h1 (by omega) (by omega) (used_closed hG hkU h1in) hval with h | h
          · exact Or.inl (Finset.mem_union_right _ h)
          · exact Or.inr (Finset.mem_union_right _ h)

lemma edge_covered {C : Circuit} (hG : Good C) {u v : Fin 26} (huv : pgAdj u v = true) :
    ∃ j ∈ Mused C,
      (center C j = u ∧ v ∈ supp C (lw C j)) ∨ (center C j = v ∧ u ∈ supp C (lw C j)) := by
  let Sact := (Used C).filter (fun k =>
    isAnd (gateAt C k).op = true ∧ val C (pair u v) (26 + k) = true)
  have hSne : Sact.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hno : ∀ k ∈ Used C, k < C.gates.length → (gateAt C k).op = GateOp.and →
        val C (pair u v) (26 + k) = false := by
      intro k hk _ hop
      by_contra hnt
      have ht : val C (pair u v) (26 + k) = true := Bool.eq_true_of_not_eq_false hnt
      have hmem : k ∈ Sact := by
        simp [Sact, hk, isAnd_iff, hop, ht]
      rw [h] at hmem
      exact Finset.notMem_empty k hmem
    obtain ⟨houtEq, houtLt, houtU⟩ := outG_spec hG
    have houtVal : val C (pair u v) C.output = true := by
      rw [val_pair_out hG u v, huv]
    have hsup := val_pair_before_and hG u v C.gates.length hno C.output
      (by omega) (by omega) (Or.inr ⟨by omega, by simpa [outG] using houtU⟩) houtVal
    rw [supp_out hG] at hsup
    simp at hsup
  let j := Sact.min' hSne
  have hjmem : j ∈ Sact := Finset.min'_mem Sact hSne
  have hjU : j ∈ Used C := (Finset.mem_filter.1 hjmem).1
  have hjAnd : (gateAt C j).op = GateOp.and :=
    (isAnd_iff _).1 (Finset.mem_filter.1 hjmem).2.1
  have hjVal : val C (pair u v) (26 + j) = true := (Finset.mem_filter.1 hjmem).2.2
  have hjl : j < C.gates.length := (Finset.mem_range.1 (Finset.mem_filter.1 hjU).1)
  have hno : ∀ k ∈ Used C, k < j → (gateAt C k).op = GateOp.and →
      val C (pair u v) (26 + k) = false := by
    intro k hk hkj hop
    by_contra hnt
    have ht : val C (pair u v) (26 + k) = true := Bool.eq_true_of_not_eq_false hnt
    have hkmem : k ∈ Sact := by simp [Sact, hk, isAnd_iff, hop, ht]
    have hle : j ≤ k := Finset.min'_le Sact k hkmem
    omega
  obtain ⟨_, hin, _, h0, h1⟩ := gate_spec hG.2.1 hjl
  rw [val_and hG.2.1 (pair u v) hjl hjAnd, Bool.and_eq_true] at hjVal
  have h0in : op0 C j ∈ (gateAt C j).inputs := by rw [hin]; simp
  have h1in : op1 C j ∈ (gateAt C j).inputs := by rw [hin]; simp
  have hs0 := val_pair_before_and hG u v j hno (op0 C j) h0 (by omega)
    (used_closed hG hjU h0in) hjVal.1
  have hs1 := val_pair_before_and hG u v j hno (op1 C j) h1 (by omega)
    (used_closed hG hjU h1in) hjVal.2
  have hcross : (u ∈ supp C (op0 C j) ∧ v ∈ supp C (op1 C j)) ∨
      (v ∈ supp C (op0 C j) ∧ u ∈ supp C (op1 C j)) := by
    rcases hs0 with hu0 | hv0 <;> rcases hs1 with hu1 | hv1
    · have := and_adj hG hjl hjAnd hu0 hu1
      rw [pgAdj_irrefl] at this; exact absurd this Bool.false_ne_true
    · exact Or.inl ⟨hu0, hv1⟩
    · exact Or.inr ⟨hv0, hu1⟩
    · have := and_adj hG hjl hjAnd hv0 hv1
      rw [pgAdj_irrefl] at this; exact absurd this Bool.false_ne_true
  have hjM : j ∈ Mset C := by
    simp only [Mset, Finset.mem_filter, Finset.mem_range, isAnd_iff]
    rcases hcross with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact ⟨hjl, hjAnd, ⟨u, h1'⟩, ⟨v, h2'⟩⟩
    · exact ⟨hjl, hjAnd, ⟨v, h1'⟩, ⟨u, h2'⟩⟩
  have hjMU : j ∈ Mused C := Finset.mem_inter.2 ⟨hjM, hjU⟩
  obtain ⟨hcw, _, hpair⟩ := cw_lw_spec hG hjM
  refine ⟨j, hjMU, ?_⟩
  rcases hpair with ⟨hcw0, hlw1⟩ | ⟨hcw1, hlw0⟩
  · rcases hcross with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
    · rw [← hcw0, hcw, Finset.mem_singleton] at hu0
      rw [← hlw1] at hv1
      exact Or.inl ⟨hu0.symm, hv1⟩
    · rw [← hcw0, hcw, Finset.mem_singleton] at hv0
      rw [← hlw1] at hu1
      exact Or.inr ⟨hv0.symm, hu1⟩
  · rcases hcross with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
    · rw [← hcw1, hcw, Finset.mem_singleton] at hv1
      rw [← hlw0] at hu0
      exact Or.inr ⟨hv1.symm, hu0⟩
    · rw [← hcw1, hcw, Finset.mem_singleton] at hu1
      rw [← hlw0] at hv0
      exact Or.inl ⟨hu1.symm, hv0⟩

lemma edge_in_Uc {C : Circuit} (hG : Good C) {p l : Fin 13} (hpl : (p, l) ∈ E52) :
    Fin.natAdd 13 l ∈ Uc C (Fin.castAdd 13 p) ∨ Fin.castAdd 13 p ∈ Uc C (Fin.natAdd 13 l) := by
  have hadj : pgAdj (Fin.castAdd 13 p) (Fin.natAdd 13 l) = true := by
    rw [pgAdj_castAdd_natAdd]
    simp only [E52, Finset.mem_filter, Finset.mem_univ, true_and] at hpl
    exact decide_eq_true hpl
  obtain ⟨j, hjMU, ⟨hc, hl⟩ | ⟨hc, hp⟩⟩ := edge_covered hG hadj
  · left
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨hjMU, hc⟩, hl⟩
  · right
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨hjMU, hc⟩, hp⟩

lemma sum_Mc_card (C : Circuit) :
    ∑ c : Fin 26, (Mc C c).card = (Mused C).card := by
  simpa [Mc] using (Finset.card_eq_sum_card_fiberwise (f := center C)
    (s := Mused C) (t := (Finset.univ : Finset (Fin 26))) (fun _ _ => Finset.mem_univ _)).symm

lemma sum_Uc_ge_52 {C : Circuit} (hG : Good C) :
    52 ≤ ∑ c : Fin 26, (Uc C c).card := by
  let T : Finset (Σ _ : Fin 26, Fin 26) := Finset.univ.sigma (Uc C)
  let f : (Σ _ : Fin 26, Fin 26) → Fin 13 × Fin 13 := fun p => toEdge p.1 p.2
  have hsub : E52 ⊆ T.image f := by
    intro e he
    rcases e with ⟨p, l⟩
    rw [Finset.mem_image]
    rcases edge_in_Uc hG he with h | h
    · exact ⟨⟨Fin.castAdd 13 p, Fin.natAdd 13 l⟩,
        Finset.mem_sigma.2 ⟨Finset.mem_univ _, h⟩, toEdge_castAdd_natAdd p l⟩
    · exact ⟨⟨Fin.natAdd 13 l, Fin.castAdd 13 p⟩,
        Finset.mem_sigma.2 ⟨Finset.mem_univ _, h⟩, toEdge_natAdd_castAdd p l⟩
  calc 52 = E52.card := E52_card.symm
    _ ≤ (T.image f).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le
    _ = ∑ c : Fin 26, (Uc C c).card := Finset.card_sigma _ _

lemma Uc_sub_nbr {C : Circuit} (hG : Good C) (c : Fin 26) : Uc C c ⊆ nbr c := by
  intro v hv
  obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.1 hv
  simp only [Mc, Finset.mem_filter] at hj
  have hsub := (cw_lw_spec hG (Finset.mem_inter.1 hj.1).1).2.1
  rw [hj.2] at hsub
  exact hsub hvj

lemma Uc_le_sum_lw {C : Circuit} (c : Fin 26) :
    (Uc C c).card ≤ ∑ j ∈ Mc C c, (supp C (lw C j)).card :=
  Finset.card_biUnion_le

lemma sum_lw_le_4 {C : Circuit} (hG : Good C) (c : Fin 26) :
    ∑ j ∈ Mc C c, (supp C (lw C j)).card ≤ 4 * (Mc C c).card := by
  calc ∑ j ∈ Mc C c, (supp C (lw C j)).card
      ≤ ∑ _j ∈ Mc C c, 4 := by
        apply Finset.sum_le_sum
        intro j hj
        have hM : j ∈ Mset C := (Finset.mem_inter.1 (Finset.mem_filter.1 hj).1).1
        have hsub := (cw_lw_spec hG hM).2.1
        exact (Finset.card_le_card hsub).trans (le_of_eq (nbr_card (center C j)))
    _ = 4 * (Mc C c).card := by simp [Nat.mul_comm]

lemma Mused_ge_13 {C : Circuit} (hG : Good C) : 13 ≤ (Mused C).card := by
  have h52 := sum_Uc_ge_52 hG
  have hle : ∑ c : Fin 26, (Uc C c).card ≤ 4 * (Mused C).card := by
    calc ∑ c : Fin 26, (Uc C c).card
        ≤ ∑ c : Fin 26, 4 * (Mc C c).card :=
          Finset.sum_le_sum (fun c _ => (Uc_le_sum_lw c).trans (sum_lw_le_4 hG c))
      _ = 4 * ∑ c : Fin 26, (Mc C c).card := (Finset.mul_sum _ _ _).symm
      _ = 4 * (Mused C).card := by rw [sum_Mc_card]
  omega

lemma Hc_disjoint (C : Circuit) {c₁ c₂ : Fin 26} (hne : c₁ ≠ c₂) :
    Disjoint (Hc C c₁) (Hc C c₂) := by
  rw [Finset.disjoint_left]
  intro k hk₁ hk₂
  simp only [Hc, Finset.mem_filter] at hk₁ hk₂
  have hsub : supp C (26 + k) ⊆ nbr c₁ ∩ nbr c₂ := Finset.subset_inter hk₁.2.1 hk₂.2.1
  have hle : (supp C (26 + k)).card ≤ (nbr c₁ ∩ nbr c₂).card := Finset.card_le_card hsub
  have hc4 := c4_free c₁ c₂ hne
  omega

lemma sum_Hc_le_Opure (C : Circuit) :
    ∑ c : Fin 26, (Hc C c).card ≤ (Opure C).card := by
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 26)) (Hc C) :=
    fun c₁ _ c₂ _ hne => Hc_disjoint C hne
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro k hk
  obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.1 hk
  exact (Finset.mem_filter.1 hkc).1

lemma biUnion_supp_le {C : Circuit} (hG : Good C) (c : Fin 26) :
    ∀ m ≤ C.gates.length, ∀ W : Finset ℕ,
      (∀ w ∈ W, w < 26 + m ∧ supp C w ⊆ nbr c) →
      (W.biUnion (supp C)).card ≤ W.card + ((Hc C c).filter (· < m)).card := by
  intro m
  induction m with
  | zero =>
    intro _ W hW
    calc (W.biUnion (supp C)).card
        ≤ ∑ w ∈ W, (supp C w).card := Finset.card_biUnion_le
      _ = ∑ _w ∈ W, 1 := by
        apply Finset.sum_congr rfl
        intro w hw
        have hwlt : w < 26 := (hW w hw).1
        rw [supp_input C hwlt, Finset.card_singleton]
      _ = W.card := by simp
      _ ≤ W.card + ((Hc C c).filter (· < 0)).card := Nat.le_add_right _ _
  | succ m ih =>
    intro hm W hW
    by_cases hmem : 26 + m ∈ W
    · let W' := W.erase (26 + m)
      have hWcard : W.card = W'.card + 1 := (Finset.card_erase_add_one hmem).symm
      have hW' : ∀ w ∈ W', w < 26 + m ∧ supp C w ⊆ nbr c := by
        intro w hw
        have hwW : w ∈ W := Finset.mem_of_mem_erase hw
        have hwne : w ≠ 26 + m := (Finset.mem_erase.1 hw).1
        exact ⟨by have := (hW w hwW).1; omega, (hW w hwW).2⟩
      have hWunion : W.biUnion (supp C) = supp C (26 + m) ∪ W'.biUnion (supp C) := by
        have hWin : insert (26 + m) W' = W := Finset.insert_erase hmem
        rw [← hWin, Finset.biUnion_insert]
      have hfil : ((Hc C c).filter (· < m)).card ≤ ((Hc C c).filter (· < m + 1)).card :=
        Finset.card_le_card (fun x hx => by
          simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩)
      by_cases hle1 : (supp C (26 + m)).card ≤ 1
      · have hih := ih (by omega) W' hW'
        calc (W.biUnion (supp C)).card
            = (supp C (26 + m) ∪ W'.biUnion (supp C)).card := by rw [hWunion]
          _ ≤ (supp C (26 + m)).card + (W'.biUnion (supp C)).card := Finset.card_union_le _ _
          _ ≤ 1 + (W'.card + ((Hc C c).filter (· < m)).card) := Nat.add_le_add hle1 hih
          _ ≤ W.card + ((Hc C c).filter (· < m + 1)).card := by omega
      · push Not at hle1
        have hmlt : m < C.gates.length := by omega
        obtain ⟨hop, _, _, h0lt, h1lt⟩ := gate_spec hG.2.1 hmlt
        have hor : (gateAt C m).op = GateOp.or := by
          rcases hop with hand | hor
          · rw [supp_and hG hmlt hand, Finset.card_empty] at hle1; omega
          · exact hor
        have hsor : supp C (26 + m) = supp C (op0 C m) ∪ supp C (op1 C m) :=
          supp_or hG.2.1 hmlt hor
        have hsubm : supp C (26 + m) ⊆ nbr c := (hW (26 + m) hmem).2
        have hsub0 : supp C (op0 C m) ⊆ nbr c :=
          (hsor ▸ Finset.subset_union_left).trans hsubm
        have hsub1 : supp C (op1 C m) ⊆ nbr c :=
          (hsor ▸ Finset.subset_union_right).trans hsubm
        by_cases h0e : supp C (op0 C m) = ∅
        · let W₁ := insert (op1 C m) W'
          have hW₁ : ∀ w ∈ W₁, w < 26 + m ∧ supp C w ⊆ nbr c := by
            intro w hw
            rcases Finset.mem_insert.1 hw with rfl | hw'
            · exact ⟨h1lt, hsub1⟩
            · exact hW' w hw'
          have hbi : W.biUnion (supp C) = W₁.biUnion (supp C) := by
            rw [hWunion, hsor, h0e, Finset.empty_union, Finset.biUnion_insert]
          have hcard1 : W₁.card ≤ W.card := by
            have := Finset.card_insert_le (op1 C m) W'
            dsimp only [W₁]
            omega
          have hih := ih (by omega) W₁ hW₁
          rw [hbi]
          omega
        · by_cases h1e : supp C (op1 C m) = ∅
          · let W₁ := insert (op0 C m) W'
            have hW₁ : ∀ w ∈ W₁, w < 26 + m ∧ supp C w ⊆ nbr c := by
              intro w hw
              rcases Finset.mem_insert.1 hw with rfl | hw'
              · exact ⟨h0lt, hsub0⟩
              · exact hW' w hw'
            have hbi : W.biUnion (supp C) = W₁.biUnion (supp C) := by
              rw [hWunion, hsor, h1e, Finset.union_empty, Finset.biUnion_insert]
            have hcard1 : W₁.card ≤ W.card := by
              have := Finset.card_insert_le (op0 C m) W'
              dsimp only [W₁]
              omega
            have hih := ih (by omega) W₁ hW₁
            rw [hbi]
            omega
          · have hmHc : m ∈ Hc C c := by
              simp only [Hc, Opure, Finset.mem_filter, Finset.mem_range, isOr_iff]
              exact ⟨⟨hmlt, hor, Finset.nonempty_iff_ne_empty.2 h0e,
                Finset.nonempty_iff_ne_empty.2 h1e⟩, hsubm, by omega⟩
            have hfilEq : (Hc C c).filter (· < m + 1) = insert m ((Hc C c).filter (· < m)) := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_insert]
              constructor
              · rintro ⟨hx, hxlt⟩
                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hxlt) with hlt | rfl
                · exact Or.inr ⟨hx, hlt⟩
                · exact Or.inl rfl
              · rintro (rfl | ⟨hx, hlt⟩)
                · exact ⟨hmHc, by omega⟩
                · exact ⟨hx, by omega⟩
            have hnotmem : m ∉ (Hc C c).filter (· < m) := by simp
            have hfilCard : ((Hc C c).filter (· < m + 1)).card =
                ((Hc C c).filter (· < m)).card + 1 := by
              rw [hfilEq, Finset.card_insert_of_notMem hnotmem]
            let W₁ := insert (op0 C m) (insert (op1 C m) W')
            have hW₁ : ∀ w ∈ W₁, w < 26 + m ∧ supp C w ⊆ nbr c := by
              intro w hw
              rcases Finset.mem_insert.1 hw with rfl | hw
              · exact ⟨h0lt, hsub0⟩
              · rcases Finset.mem_insert.1 hw with rfl | hw'
                · exact ⟨h1lt, hsub1⟩
                · exact hW' w hw'
            have hbi : W.biUnion (supp C) = W₁.biUnion (supp C) := by
              rw [hWunion, hsor, Finset.biUnion_insert, Finset.biUnion_insert, Finset.union_assoc]
            have hcard1 : W₁.card ≤ W.card + 1 := by
              have c1 := Finset.card_insert_le (op0 C m) (insert (op1 C m) W')
              have c2 := Finset.card_insert_le (op1 C m) W'
              dsimp only [W₁]
              omega
            have hih := ih (by omega) W₁ hW₁
            rw [hbi, hfilCard]
            omega
    · have hW' : ∀ w ∈ W, w < 26 + m ∧ supp C w ⊆ nbr c := by
        intro w hw
        have hne : w ≠ 26 + m := fun heq => hmem (heq ▸ hw)
        exact ⟨by have := (hW w hw).1; omega, (hW w hw).2⟩
      have hfil : ((Hc C c).filter (· < m)).card ≤ ((Hc C c).filter (· < m + 1)).card :=
        Finset.card_le_card (fun x hx => by
          simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩)
      have hih := ih (by omega) W hW'
      omega

lemma Uc_le_Mc_add_Hc {C : Circuit} (hG : Good C) (c : Fin 26) :
    (Uc C c).card ≤ (Mc C c).card + (Hc C c).card := by
  let W := (Mc C c).image (lw C)
  have hW : ∀ w ∈ W, w < 26 + C.gates.length ∧ supp C w ⊆ nbr c := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
    have hjM : j ∈ Mset C := (Finset.mem_inter.1 (Finset.mem_filter.1 hj).1).1
    have hjc : center C j = c := (Finset.mem_filter.1 hj).2
    have hjl : j < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hjM).1
    obtain ⟨_, hsub, hpair⟩ := cw_lw_spec hG hjM
    obtain ⟨_, _, _, h0, h1⟩ := gate_spec hG.2.1 hjl
    rw [hjc] at hsub
    refine ⟨?_, hsub⟩
    rcases hpair with ⟨_, hlw⟩ | ⟨_, hlw⟩ <;> rw [hlw] <;> omega
  have hbi : W.biUnion (supp C) = Uc C c := by
    ext x
    simp [W, Uc]
  have hfil : (Hc C c).filter (· < C.gates.length) = Hc C c := by
    ext k
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hk
    exact Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).1
  have hmain := biUnion_supp_le hG c C.gates.length le_rfl W hW
  rw [hbi, hfil] at hmain
  have hWcard : W.card ≤ (Mc C c).card := Finset.card_image_le
  omega

lemma bound1 {C : Circuit} (hG : Good C) :
    52 ≤ (Mused C).card + (Opure C).card := by
  calc 52 ≤ ∑ c : Fin 26, (Uc C c).card := sum_Uc_ge_52 hG
    _ ≤ ∑ c : Fin 26, ((Mc C c).card + (Hc C c).card) :=
        Finset.sum_le_sum (fun c _ => Uc_le_Mc_add_Hc hG c)
    _ = ∑ c : Fin 26, (Mc C c).card + ∑ c : Fin 26, (Hc C c).card := Finset.sum_add_distrib
    _ ≤ (Mused C).card + (Opure C).card := by
        rw [sum_Mc_card]
        exact Nat.add_le_add_left (sum_Hc_le_Opure C) _

lemma gate_partition_card {C : Circuit} (hV : ValidGates C) :
    C.gates.length =
      (Mset C).card + (Aless C).card + (Oclean C).card + (Omix C).card + (Opure C).card := by
  have dMA : Disjoint (Mset C) (Aless C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Mset, Aless, Finset.mem_filter] at h1 h2
    rcases h2.2.2 with h | h
    · exact (Finset.nonempty_iff_ne_empty.1 h1.2.2.1) h
    · exact (Finset.nonempty_iff_ne_empty.1 h1.2.2.2) h
  have dAO : ∀ s, s = Oclean C ∨ s = Omix C ∨ s = Opure C →
      Disjoint (Mset C ∪ Aless C) s := by
    intro s hs
    rw [Finset.disjoint_left]; intro k h1 h2
    have hand : isAnd (gateAt C k).op = true := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact (Finset.mem_filter.1 h).2.1
      · exact (Finset.mem_filter.1 h).2.1
    have hor : isOr (gateAt C k).op = true := by
      rcases hs with rfl | rfl | rfl
      · exact (Finset.mem_filter.1 h2).2.1
      · exact (Finset.mem_filter.1 h2).2.1
      · exact (Finset.mem_filter.1 h2).2.1
    rw [isAnd_iff] at hand; rw [isOr_iff] at hor
    rw [hand] at hor; cases hor
  have dOcOm : Disjoint (Oclean C) (Omix C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Oclean, Omix, Finset.mem_filter] at h1 h2
    rcases h2.2.2 with ⟨_, h⟩ | ⟨h, _⟩
    · exact (Finset.nonempty_iff_ne_empty.1 h) h1.2.2.2
    · exact (Finset.nonempty_iff_ne_empty.1 h) h1.2.2.1
  have dOcOp : Disjoint (Oclean C) (Opure C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Oclean, Opure, Finset.mem_filter] at h1 h2
    exact (Finset.nonempty_iff_ne_empty.1 h2.2.2.1) h1.2.2.1
  have dOmOp : Disjoint (Omix C) (Opure C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Omix, Opure, Finset.mem_filter] at h1 h2
    rcases h1.2.2 with ⟨h, _⟩ | ⟨_, h⟩
    · exact (Finset.nonempty_iff_ne_empty.1 h2.2.2.1) h
    · exact (Finset.nonempty_iff_ne_empty.1 h2.2.2.2) h
  have hunion : Finset.range C.gates.length =
      (((Mset C ∪ Aless C) ∪ Oclean C) ∪ Omix C) ∪ Opure C := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range]
    constructor
    · intro hkl
      obtain ⟨hop, _, _, _, _⟩ := gate_spec hV hkl
      rcases hop with hand | hor
      · by_cases h0 : supp C (op0 C k) = ∅
        · left; left; left; right
          simp [Aless, hkl, isAnd_iff, hand, h0]
        · by_cases h1 : supp C (op1 C k) = ∅
          · left; left; left; right
            simp [Aless, hkl, isAnd_iff, hand, h1]
          · left; left; left; left
            simp [Mset, hkl, isAnd_iff, hand, Finset.nonempty_iff_ne_empty.2 h0,
              Finset.nonempty_iff_ne_empty.2 h1]
      · by_cases h0 : supp C (op0 C k) = ∅
        · by_cases h1 : supp C (op1 C k) = ∅
          · left; left; right
            simp [Oclean, hkl, isOr_iff, hor, h0, h1]
          · left; right
            simp [Omix, hkl, isOr_iff, hor, h0, Finset.nonempty_iff_ne_empty.2 h1]
        · by_cases h1 : supp C (op1 C k) = ∅
          · left; right
            simp [Omix, hkl, isOr_iff, hor, h1, Finset.nonempty_iff_ne_empty.2 h0]
          · right
            simp [Opure, hkl, isOr_iff, hor, Finset.nonempty_iff_ne_empty.2 h0,
              Finset.nonempty_iff_ne_empty.2 h1]
    · rintro ((((h | h) | h) | h) | h) <;> exact Finset.mem_range.1 (Finset.mem_filter.1 h).1
  have hc := congrArg Finset.card hunion
  rw [Finset.card_range] at hc
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint, Finset.card_union_of_disjoint] at hc
  · exact hc
  · exact dMA
  · exact dAO _ (Or.inl rfl)
  · exact Finset.disjoint_union_left.2 ⟨dAO _ (Or.inr (Or.inl rfl)), dOcOm⟩
  · exact Finset.disjoint_union_left.2
      ⟨Finset.disjoint_union_left.2 ⟨dAO _ (Or.inr (Or.inr rfl)), dOcOp⟩, dOmOp⟩

lemma cleanUsed_eq {C : Circuit} (hG : Good C) :
    CleanUsed C = (Mused C ∪ AlessU C) ∪ OcleanU C := by
  ext k
  simp only [CleanUsed, Mused, AlessU, OcleanU, Finset.mem_filter, Finset.mem_union,
    Finset.mem_inter, Mset, Aless, Oclean, Finset.mem_range]
  constructor
  · rintro ⟨hkU, hclean⟩
    have hkl : k < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hkU).1
    obtain ⟨hop, _, _, _, _⟩ := gate_spec hG.2.1 hkl
    rcases hop with hand | hor
    · by_cases h0 : supp C (op0 C k) = ∅
      · left; right; exact ⟨⟨hkl, (isAnd_iff _).2 hand, Or.inl h0⟩, hkU⟩
      · by_cases h1 : supp C (op1 C k) = ∅
        · left; right; exact ⟨⟨hkl, (isAnd_iff _).2 hand, Or.inr h1⟩, hkU⟩
        · left; left
          exact ⟨⟨hkl, (isAnd_iff _).2 hand, Finset.nonempty_iff_ne_empty.2 h0,
            Finset.nonempty_iff_ne_empty.2 h1⟩, hkU⟩
    · rw [supp_or hG.2.1 hkl hor, Finset.union_eq_empty] at hclean
      right; exact ⟨⟨hkl, (isOr_iff _).2 hor, hclean.1, hclean.2⟩, hkU⟩
  · rintro ((⟨⟨hkl, hand, _, _⟩, hkU⟩ | ⟨⟨hkl, hand, _⟩, hkU⟩) | ⟨⟨hkl, hor, h0, h1⟩, hkU⟩)
    · exact ⟨hkU, supp_and hG hkl ((isAnd_iff _).1 hand)⟩
    · exact ⟨hkU, supp_and hG hkl ((isAnd_iff _).1 hand)⟩
    · exact ⟨hkU, by rw [supp_or hG.2.1 hkl ((isOr_iff _).1 hor), h0, h1, Finset.union_empty]⟩

lemma cleanUsed_card {C : Circuit} (hG : Good C) :
    (CleanUsed C).card = (Mused C).card + (AlessU C).card + (OcleanU C).card := by
  rw [cleanUsed_eq hG]
  have d1 : Disjoint (Mused C) (AlessU C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Mused, AlessU, Mset, Aless, Finset.mem_inter, Finset.mem_filter] at h1 h2
    rcases h2.1.2.2 with h | h
    · exact (Finset.nonempty_iff_ne_empty.1 h1.1.2.2.1) h
    · exact (Finset.nonempty_iff_ne_empty.1 h1.1.2.2.2) h
  have d2 : Disjoint (Mused C ∪ AlessU C) (OcleanU C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    have hor : (gateAt C k).op = GateOp.or :=
      (isOr_iff _).1 (Finset.mem_filter.1 (Finset.mem_inter.1 h2).1).2.1
    have hand : (gateAt C k).op = GateOp.and := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact (isAnd_iff _).1 (Finset.mem_filter.1 (Finset.mem_inter.1 h).1).2.1
      · exact (isAnd_iff _).1 (Finset.mem_filter.1 (Finset.mem_inter.1 h).1).2.1
    rw [hand] at hor; cases hor
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1]

lemma outG_mem_cleanUsed {C : Circuit} (hG : Good C) : outG C ∈ CleanUsed C := by
  obtain ⟨heq, _, hU⟩ := outG_spec hG
  simp only [CleanUsed, Finset.mem_filter]
  exact ⟨hU, by rw [heq, supp_out hG]⟩

lemma sum_readers_eq_sum_cleanSlots (C : Circuit) :
    ∑ k ∈ (CleanUsed C).erase (outG C), (readersUsed C k).card =
      ∑ q ∈ Used C, (cleanSlots C q).card := by
  have h1 : ∀ k ∈ (CleanUsed C).erase (outG C),
      (readersUsed C k).card = ∑ q ∈ Used C, if 26 + k ∈ (gateAt C q).inputs then 1 else 0 := by
    intro k _
    rw [readersUsed, Finset.card_filter]
  have h2 : ∀ q ∈ Used C,
      (cleanSlots C q).card =
        ∑ k ∈ (CleanUsed C).erase (outG C), if 26 + k ∈ (gateAt C q).inputs then 1 else 0 := by
    intro q _
    rw [cleanSlots, Finset.card_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_comm]

lemma cleanSlots_le_cleanIn {C : Circuit} (hG : Good C) {q : ℕ} (hq : q ∈ Used C) :
    (cleanSlots C q).card ≤ cleanIn C q := by
  have hql : q < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hq).1
  obtain ⟨_, hin, hne, _, _⟩ := gate_spec hG.2.1 hql
  let S2 : Finset ℕ := ({op0 C q, op1 C q} : Finset ℕ).filter (fun w => supp C w = ∅)
  have hcard : S2.card = cleanIn C q := by
    unfold S2 cleanIn
    rw [Finset.filter_insert, Finset.filter_singleton]
    split_ifs with h0 h1 h1
    · rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    · simp
    · simp
    · simp
  rw [← hcard]
  have hinj : Set.InjOn (fun k => 26 + k) (cleanSlots C q) := by
    intro a _ b _ hab
    dsimp only at hab
    omega
  calc (cleanSlots C q).card
      = ((cleanSlots C q).image (fun k => 26 + k)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ S2.card := by
        apply Finset.card_le_card
        intro w hw
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
        simp only [cleanSlots, Finset.mem_filter, Finset.mem_erase, CleanUsed] at hk
        simp only [S2, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        rw [hin] at hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        exact ⟨hk.2, hk.1.2.2⟩

lemma used_partition_sum_cleanIn {C : Circuit} (hV : ValidGates C) :
    ∑ q ∈ Used C, cleanIn C q =
      2 * (OcleanU C).card + (OmixU C).card + ∑ q ∈ AlessU C, cleanIn C q := by
  have hU : Used C = (((Mused C ∪ AlessU C) ∪ OcleanU C) ∪ OmixU C) ∪ OpureU C := by
    ext k
    simp only [Mused, AlessU, OcleanU, OmixU, OpureU, Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hkU
      have hkl : k < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hkU).1
      obtain ⟨hop, _, _, _, _⟩ := gate_spec hV hkl
      rcases hop with hand | hor
      · by_cases h0 : supp C (op0 C k) = ∅
        · left; left; left; right
          exact ⟨by simp [Aless, hkl, isAnd_iff, hand, h0], hkU⟩
        · by_cases h1 : supp C (op1 C k) = ∅
          · left; left; left; right
            exact ⟨by simp [Aless, hkl, isAnd_iff, hand, h1], hkU⟩
          · left; left; left; left
            exact ⟨by simp [Mset, hkl, isAnd_iff, hand, Finset.nonempty_iff_ne_empty.2 h0,
              Finset.nonempty_iff_ne_empty.2 h1], hkU⟩
      · by_cases h0 : supp C (op0 C k) = ∅
        · by_cases h1 : supp C (op1 C k) = ∅
          · left; left; right
            exact ⟨by simp [Oclean, hkl, isOr_iff, hor, h0, h1], hkU⟩
          · left; right
            exact ⟨by simp [Omix, hkl, isOr_iff, hor, h0, Finset.nonempty_iff_ne_empty.2 h1], hkU⟩
        · by_cases h1 : supp C (op1 C k) = ∅
          · left; right
            exact ⟨by simp [Omix, hkl, isOr_iff, hor, h1, Finset.nonempty_iff_ne_empty.2 h0], hkU⟩
          · right
            exact ⟨by simp [Opure, hkl, isOr_iff, hor, Finset.nonempty_iff_ne_empty.2 h0,
              Finset.nonempty_iff_ne_empty.2 h1], hkU⟩
    · rintro ((((h | h) | h) | h) | h) <;> exact h.2
  have dMA : Disjoint (Mused C) (AlessU C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Mused, AlessU, Mset, Aless, Finset.mem_inter, Finset.mem_filter] at h1 h2
    rcases h2.1.2.2 with h | h
    · exact (Finset.nonempty_iff_ne_empty.1 h1.1.2.2.1) h
    · exact (Finset.nonempty_iff_ne_empty.1 h1.1.2.2.2) h
  have dAO : ∀ s, s = OcleanU C ∨ s = OmixU C ∨ s = OpureU C →
      Disjoint (Mused C ∪ AlessU C) s := by
    intro s hs
    rw [Finset.disjoint_left]; intro k h1 h2
    have hand : (gateAt C k).op = GateOp.and := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact (isAnd_iff _).1 (Finset.mem_filter.1 (Finset.mem_inter.1 h).1).2.1
      · exact (isAnd_iff _).1 (Finset.mem_filter.1 (Finset.mem_inter.1 h).1).2.1
    have hor : (gateAt C k).op = GateOp.or := by
      rcases hs with rfl | rfl | rfl
      · exact (isOr_iff _).1 (Finset.mem_filter.1 (Finset.mem_inter.1 h2).1).2.1
      · exact (isOr_iff _).1 (Finset.mem_filter.1 (Finset.mem_inter.1 h2).1).2.1
      · exact (isOr_iff _).1 (Finset.mem_filter.1 (Finset.mem_inter.1 h2).1).2.1
    rw [hand] at hor; cases hor
  have dOcOm : Disjoint (OcleanU C) (OmixU C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [OcleanU, OmixU, Oclean, Omix, Finset.mem_inter, Finset.mem_filter] at h1 h2
    rcases h2.1.2.2 with ⟨_, h⟩ | ⟨h, _⟩
    · exact (Finset.nonempty_iff_ne_empty.1 h) h1.1.2.2.2
    · exact (Finset.nonempty_iff_ne_empty.1 h) h1.1.2.2.1
  have dOcOp : Disjoint (OcleanU C) (OpureU C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [OcleanU, OpureU, Oclean, Opure, Finset.mem_inter, Finset.mem_filter] at h1 h2
    exact (Finset.nonempty_iff_ne_empty.1 h2.1.2.2.1) h1.1.2.2.1
  have dOmOp : Disjoint (OmixU C) (OpureU C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [OmixU, OpureU, Omix, Opure, Finset.mem_inter, Finset.mem_filter] at h1 h2
    rcases h1.1.2.2 with ⟨h, _⟩ | ⟨_, h⟩
    · exact (Finset.nonempty_iff_ne_empty.1 h2.1.2.2.1) h
    · exact (Finset.nonempty_iff_ne_empty.1 h2.1.2.2.2) h
  rw [hU]
  rw [Finset.sum_union (Finset.disjoint_union_left.2
      ⟨Finset.disjoint_union_left.2 ⟨dAO _ (Or.inr (Or.inr rfl)), dOcOp⟩, dOmOp⟩)]
  rw [Finset.sum_union (Finset.disjoint_union_left.2 ⟨dAO _ (Or.inr (Or.inl rfl)), dOcOm⟩)]
  rw [Finset.sum_union (dAO _ (Or.inl rfl))]
  rw [Finset.sum_union dMA]
  have sM : ∑ q ∈ Mused C, cleanIn C q = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp only [Mused, Mset, Finset.mem_inter, Finset.mem_filter] at hq
    simp [cleanIn, Finset.nonempty_iff_ne_empty.1 hq.1.2.2.1,
      Finset.nonempty_iff_ne_empty.1 hq.1.2.2.2]
  have sOp : ∑ q ∈ OpureU C, cleanIn C q = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp only [OpureU, Opure, Finset.mem_inter, Finset.mem_filter] at hq
    simp [cleanIn, Finset.nonempty_iff_ne_empty.1 hq.1.2.2.1,
      Finset.nonempty_iff_ne_empty.1 hq.1.2.2.2]
  have sOc : ∑ q ∈ OcleanU C, cleanIn C q = 2 * (OcleanU C).card := by
    calc ∑ q ∈ OcleanU C, cleanIn C q
        = ∑ _q ∈ OcleanU C, 2 := by
          apply Finset.sum_congr rfl
          intro q hq
          simp only [OcleanU, Oclean, Finset.mem_inter, Finset.mem_filter] at hq
          simp [cleanIn, hq.1.2.2.1, hq.1.2.2.2]
      _ = 2 * (OcleanU C).card := by simp [Nat.mul_comm]
  have sOm : ∑ q ∈ OmixU C, cleanIn C q = (OmixU C).card := by
    calc ∑ q ∈ OmixU C, cleanIn C q
        = ∑ _q ∈ OmixU C, 1 := by
          apply Finset.sum_congr rfl
          intro q hq
          simp only [OmixU, Omix, Finset.mem_inter, Finset.mem_filter] at hq
          rcases hq.1.2.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
          · simp [cleanIn, h0, Finset.nonempty_iff_ne_empty.1 h1]
          · simp [cleanIn, h1, Finset.nonempty_iff_ne_empty.1 h0]
      _ = (OmixU C).card := by simp
  rw [sM, sOp, sOc, sOm]
  omega

lemma cleanIn_le_two (C : Circuit) (q : ℕ) : cleanIn C q ≤ 2 := by
  unfold cleanIn
  split_ifs <;> omega

lemma exact_equalities {C : Circuit} (hG : Good C) :
    Mused C = Mset C ∧
    (Mset C).card = 13 ∧
    AlessU C = Aless C ∧
    OcleanU C = Oclean C ∧
    OmixU C = Omix C ∧
    (∀ k ∈ (CleanUsed C).erase (outG C), (readersUsed C k).card = 1) ∧
    (∀ q ∈ Aless C, supp C (op0 C q) = ∅ ∧ supp C (op1 C q) = ∅) ∧
    (∀ j ∈ Mset C, supp C (lw C j) = nbr (center C j)) ∧
    (∀ j₁ ∈ Mset C, ∀ j₂ ∈ Mset C, center C j₁ = center C j₂ → j₁ = j₂) ∧
    (∀ j₁ ∈ Mset C, ∀ j₂ ∈ Mset C, pgAdj (center C j₁) (center C j₂) = false) := by
  have h13 := Mused_ge_13 hG
  have hb1 := bound1 hG
  have hlen := gate_partition_card hG.2.1
  have hlen64 : C.gates.length ≤ 64 := hG.1
  have hCUc := cleanUsed_card hG
  have houtCU := outG_mem_cleanUsed hG
  have herase : ((CleanUsed C).erase (outG C)).card = (CleanUsed C).card - 1 :=
    Finset.card_erase_of_mem houtCU
  have hread_ge : ((CleanUsed C).erase (outG C)).card ≤
      ∑ k ∈ (CleanUsed C).erase (outG C), (readersUsed C k).card := by
    calc ((CleanUsed C).erase (outG C)).card
        = ∑ _k ∈ (CleanUsed C).erase (outG C), 1 := by simp
      _ ≤ ∑ k ∈ (CleanUsed C).erase (outG C), (readersUsed C k).card := by
          apply Finset.sum_le_sum
          intro k hk
          have hne : k ≠ outG C := (Finset.mem_erase.1 hk).1
          have hkU : k ∈ Used C := (Finset.mem_filter.1 (Finset.mem_erase.1 hk).2).1
          exact Finset.card_pos.2 (used_has_reader hkU hne)
  have hslots_le : ∑ q ∈ Used C, (cleanSlots C q).card ≤ ∑ q ∈ Used C, cleanIn C q :=
    Finset.sum_le_sum (fun q hq => cleanSlots_le_cleanIn hG hq)
  have hsum_clean := used_partition_sum_cleanIn hG.2.1
  have hA_le : ∑ q ∈ AlessU C, cleanIn C q ≤ 2 * (AlessU C).card := by
    calc ∑ q ∈ AlessU C, cleanIn C q
        ≤ ∑ _q ∈ AlessU C, 2 := Finset.sum_le_sum (fun q _ => cleanIn_le_two C q)
      _ = 2 * (AlessU C).card := by simp [Nat.mul_comm]
  have hsubM : (Mused C).card ≤ (Mset C).card := Finset.card_le_card Finset.inter_subset_left
  have hsubA : (AlessU C).card ≤ (Aless C).card := Finset.card_le_card Finset.inter_subset_left
  have hsubOc : (OcleanU C).card ≤ (Oclean C).card := Finset.card_le_card Finset.inter_subset_left
  have hsubOm : (OmixU C).card ≤ (Omix C).card := Finset.card_le_card Finset.inter_subset_left
  have hsw := sum_readers_eq_sum_cleanSlots C
  have hMcard : (Mused C).card = 13 := by omega
  have hMeq : Mused C = Mset C :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hAeq : AlessU C = Aless C :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hOce : OcleanU C = Oclean C :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hOme : OmixU C = Omix C :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hread_eq : ∀ k ∈ (CleanUsed C).erase (outG C), (readersUsed C k).card = 1 := by
    have heq : ∑ _k ∈ (CleanUsed C).erase (outG C), 1 =
        ∑ k ∈ (CleanUsed C).erase (outG C), (readersUsed C k).card := by
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
      omega
    intro k hk
    have h := (Finset.sum_eq_sum_iff_of_le (fun x hx => by
      have hne : x ≠ outG C := (Finset.mem_erase.1 hx).1
      have hxU : x ∈ Used C := (Finset.mem_filter.1 (Finset.mem_erase.1 hx).2).1
      exact Finset.card_pos.2 (used_has_reader hxU hne))).1 heq k hk
    exact h.symm
  have hA2 : ∀ q ∈ Aless C, supp C (op0 C q) = ∅ ∧ supp C (op1 C q) = ∅ := by
    have heq : ∑ q ∈ AlessU C, cleanIn C q = ∑ _q ∈ AlessU C, 2 := by
      simp only [Finset.sum_const, smul_eq_mul]
      omega
    intro q hq
    rw [← hAeq] at hq
    have h2 := (Finset.sum_eq_sum_iff_of_le (fun x _ => cleanIn_le_two C x)).1 heq q hq
    unfold cleanIn at h2
    split_ifs at h2 with h0 h1 h1
    · exact ⟨h0, h1⟩
    · omega
    · omega
    · omega
  have hsum52 : ∑ c : Fin 26, (Uc C c).card = 52 := by
    have h1 := sum_Uc_ge_52 hG
    have h2 : ∑ c : Fin 26, (Uc C c).card ≤ 4 * (Mused C).card := by
      calc ∑ c : Fin 26, (Uc C c).card
          ≤ ∑ c : Fin 26, 4 * (Mc C c).card :=
            Finset.sum_le_sum (fun c _ => (Uc_le_sum_lw c).trans (sum_lw_le_4 hG c))
        _ = 4 * ∑ c : Fin 26, (Mc C c).card := (Finset.mul_sum _ _ _).symm
        _ = 4 * (Mused C).card := by rw [sum_Mc_card]
    omega
  have hUc_eq_4Mc : ∀ c : Fin 26, (Uc C c).card = 4 * (Mc C c).card := by
    have heq : ∑ c : Fin 26, (Uc C c).card = ∑ c : Fin 26, 4 * (Mc C c).card := by
      rw [hsum52, ← Finset.mul_sum, sum_Mc_card, hMcard]
      rfl
    intro c
    exact (Finset.sum_eq_sum_iff_of_le
      (fun x _ => (Uc_le_sum_lw x).trans (sum_lw_le_4 hG x))).1 heq c (Finset.mem_univ c)
  have hlw_full : ∀ j ∈ Mset C, supp C (lw C j) = nbr (center C j) := by
    intro j hj
    have hjMU : j ∈ Mused C := hMeq ▸ hj
    let c := center C j
    have hjMc : j ∈ Mc C c := Finset.mem_filter.2 ⟨hjMU, rfl⟩
    have hsum_eq : ∑ x ∈ Mc C c, (supp C (lw C x)).card = ∑ _x ∈ Mc C c, 4 := by
      have h1 := Uc_le_sum_lw (C := C) c
      have h2 := sum_lw_le_4 hG c
      have h3 := hUc_eq_4Mc c
      simp only [Finset.sum_const, smul_eq_mul]
      omega
    have hcard4 : (supp C (lw C j)).card = 4 :=
      (Finset.sum_eq_sum_iff_of_le (fun x hx => by
        have hxM : x ∈ Mset C := (Finset.mem_inter.1 (Finset.mem_filter.1 hx).1).1
        exact (Finset.card_le_card (cw_lw_spec hG hxM).2.1).trans
          (le_of_eq (nbr_card (center C x))))).1 hsum_eq j hjMc
    exact Finset.eq_of_subset_of_card_le (cw_lw_spec hG hj).2.1
      (by rw [nbr_card, hcard4])
  have hcinj : ∀ j₁ ∈ Mset C, ∀ j₂ ∈ Mset C, center C j₁ = center C j₂ → j₁ = j₂ := by
    intro j₁ hj₁ j₂ hj₂ hce
    let c := center C j₁
    have h1 : j₁ ∈ Mc C c := Finset.mem_filter.2 ⟨hMeq ▸ hj₁, rfl⟩
    have h2 : j₂ ∈ Mc C c := Finset.mem_filter.2 ⟨hMeq ▸ hj₂, hce.symm⟩
    have hle1 : (Mc C c).card ≤ 1 := by
      have h4 := hUc_eq_4Mc c
      have hsub : (Uc C c).card ≤ 4 :=
        (Finset.card_le_card (Uc_sub_nbr hG c)).trans (le_of_eq (nbr_card c))
      omega
    exact Finset.card_le_one.1 hle1 j₁ h1 j₂ h2
  have hindep : ∀ j₁ ∈ Mset C, ∀ j₂ ∈ Mset C, pgAdj (center C j₁) (center C j₂) = false := by
    let T : Finset (Σ _ : Fin 26, Fin 26) := Finset.univ.sigma (Uc C)
    let f : (Σ _ : Fin 26, Fin 26) → Fin 13 × Fin 13 := fun p => toEdge p.1 p.2
    have hsub : E52 ⊆ T.image f := by
      intro e he
      rcases e with ⟨p, l⟩
      rw [Finset.mem_image]
      rcases edge_in_Uc hG he with h | h
      · exact ⟨⟨Fin.castAdd 13 p, Fin.natAdd 13 l⟩,
          Finset.mem_sigma.2 ⟨Finset.mem_univ _, h⟩, toEdge_castAdd_natAdd p l⟩
      · exact ⟨⟨Fin.natAdd 13 l, Fin.castAdd 13 p⟩,
          Finset.mem_sigma.2 ⟨Finset.mem_univ _, h⟩, toEdge_natAdd_castAdd p l⟩
    have hTcard : T.card = 52 := by rw [Finset.card_sigma, hsum52]
    have himgcard : (T.image f).card = T.card := by
      have h1 : 52 ≤ (T.image f).card := by rw [← E52_card]; exact Finset.card_le_card hsub
      have h2 : (T.image f).card ≤ T.card := Finset.card_image_le
      omega
    have hinj : Set.InjOn f T := Finset.card_image_iff.1 himgcard
    intro j₁ hj₁ j₂ hj₂
    by_contra hnt
    have hadj : pgAdj (center C j₁) (center C j₂) = true := Bool.eq_true_of_not_eq_false hnt
    have hc₂mem : center C j₂ ∈ Uc C (center C j₁) := by
      apply Finset.mem_biUnion.2
      refine ⟨j₁, Finset.mem_filter.2 ⟨hMeq ▸ hj₁, rfl⟩, ?_⟩
      rw [hlw_full j₁ hj₁]
      simp [nbr, hadj]
    have hc₁mem : center C j₁ ∈ Uc C (center C j₂) := by
      apply Finset.mem_biUnion.2
      refine ⟨j₂, Finset.mem_filter.2 ⟨hMeq ▸ hj₂, rfl⟩, ?_⟩
      rw [hlw_full j₂ hj₂]
      simp [nbr, pgAdj_symm, hadj]
    have hp1 : (⟨center C j₁, center C j₂⟩ : Σ _ : Fin 26, Fin 26) ∈ T :=
      Finset.mem_sigma.2 ⟨Finset.mem_univ _, hc₂mem⟩
    have hp2 : (⟨center C j₂, center C j₁⟩ : Σ _ : Fin 26, Fin 26) ∈ T :=
      Finset.mem_sigma.2 ⟨Finset.mem_univ _, hc₁mem⟩
    have hfeq : f ⟨center C j₁, center C j₂⟩ = f ⟨center C j₂, center C j₁⟩ :=
      toEdge_symm _ _ hadj
    have hpeq := hinj hp1 hp2 hfeq
    have hceq : center C j₁ = center C j₂ := congrArg Sigma.fst hpeq
    rw [hceq, pgAdj_irrefl] at hadj
    exact Bool.false_ne_true hadj
  exact ⟨hMeq, by omega, hAeq, hOce, hOme, hread_eq, hA2, hlw_full, hcinj, hindep⟩

def CleanEdge (C : Circuit) (k₁ k₂ : ℕ) : Prop :=
  k₁ ∈ CleanUsed C ∧ k₂ ∈ CleanUsed C ∧ 26 + k₁ ∈ (gateAt C k₂).inputs

def CleanReach (C : Circuit) (k r : ℕ) : Prop :=
  Relation.ReflTransGen (CleanEdge C) k r

lemma clean_wire_spec {C : Circuit} (hG : Good C) {k w : ℕ} (hk : k ∈ Used C)
    (hw : w ∈ (gateAt C k).inputs) (hcl : supp C w = ∅) :
    26 ≤ w ∧ w - 26 ∈ CleanUsed C ∧ w - 26 < k ∧ 26 + (w - 26) = w := by
  have hge : 26 ≤ w := by
    by_contra hlt
    push Not at hlt
    have hs := supp_input C hlt
    rw [hcl] at hs
    exact Finset.singleton_ne_empty (⟨w, hlt⟩ : Fin 26) hs.symm
  have hkl : k < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
  obtain ⟨_, hin, _, h0, h1⟩ := gate_spec hG.2.1 hkl
  have hwlt : w < 26 + k := by
    rw [hin] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> omega
  have hU : w - 26 ∈ Used C := by
    rcases used_closed hG hk hw with hlt | ⟨_, hU⟩
    · omega
    · exact hU
  have heq : 26 + (w - 26) = w := by omega
  have hCU : w - 26 ∈ CleanUsed C := by
    simp only [CleanUsed, Finset.mem_filter]
    exact ⟨hU, by rwa [heq]⟩
  exact ⟨hge, hCU, by omega, heq⟩

lemma cleanReach_le_and_mem {C : Circuit} (hG : Good C) {k r : ℕ}
    (hr : r ∈ CleanUsed C) (h : CleanReach C k r) :
    k ≤ r ∧ k ∈ CleanUsed C := by
  induction h with
  | refl => exact ⟨le_rfl, hr⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hbCU, hcCU, hbcIn⟩ := hbc
    have hcl : c < C.gates.length :=
      Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hcCU).1).1
    obtain ⟨_, hin, _, h0, h1⟩ := gate_spec hG.2.1 hcl
    have hblt : 26 + b < 26 + c := by
      rw [hin] at hbcIn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbcIn
      rcases hbcIn with heq | heq <;> omega
    have hih := ih hbCU
    exact ⟨by omega, hih.2⟩

lemma unique_reader {C : Circuit} (hG : Good C)
    (hread : ∀ k ∈ (CleanUsed C).erase (outG C), (readersUsed C k).card = 1)
    {x q₁ q₂ : ℕ} (hx : x ∈ CleanUsed C) (hq₁ : q₁ ∈ Used C) (hq₂ : q₂ ∈ Used C)
    (h1 : 26 + x ∈ (gateAt C q₁).inputs) (h2 : 26 + x ∈ (gateAt C q₂).inputs) :
    q₁ = q₂ := by
  have hql : q₁ < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hq₁).1
  obtain ⟨_, hin, _, h0, h1lt⟩ := gate_spec hG.2.1 hql
  have hxlt : 26 + x < 26 + q₁ := by
    rw [hin] at h1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with heq | heq <;> omega
  have hqle := used_le_outG hq₁
  have hxne : x ≠ outG C := by omega
  have hxE : x ∈ (CleanUsed C).erase (outG C) := Finset.mem_erase.2 ⟨hxne, hx⟩
  have hcard1 : (readersUsed C x).card = 1 := hread x hxE
  have hm1 : q₁ ∈ readersUsed C x := Finset.mem_filter.2 ⟨hq₁, h1⟩
  have hm2 : q₂ ∈ readersUsed C x := Finset.mem_filter.2 ⟨hq₂, h2⟩
  exact Finset.card_le_one.1 (le_of_eq hcard1) q₁ hm1 q₂ hm2

lemma cleanReach_reader {C : Circuit} (hG : Good C)
    (hread : ∀ k ∈ (CleanUsed C).erase (outG C), (readersUsed C k).card = 1)
    {r p : ℕ} (hr : r ∈ CleanUsed C) (hp : p ∈ Used C) (hrp : 26 + r ∈ (gateAt C p).inputs)
    {k q : ℕ} (hkr : CleanReach C k r) (hq : q ∈ Used C) (hkq : 26 + k ∈ (gateAt C q).inputs) :
    q = p ∨ CleanReach C q r := by
  have hkCU : k ∈ CleanUsed C := (cleanReach_le_and_mem hG hr hkr).2
  rcases Relation.ReflTransGen.cases_head hkr with rfl | ⟨b, hkb, hbr⟩
  · exact Or.inl (unique_reader hG hread hr hq hp hkq hrp)
  · have hbU : b ∈ Used C := (Finset.mem_filter.1 hkb.2.1).1
    have hqb : q = b := unique_reader hG hread hkCU hq hbU hkq hkb.2.2
    rw [hqb]
    exact Or.inr hbr

lemma cleanReach_has_M {C : Circuit} (hG : Good C) :
    ∀ r, r ∈ CleanUsed C → (∀ k, CleanReach C k r → k ∉ Aless C) →
      ∃ g ∈ Mset C, CleanReach C g r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr hnoA
    have hcu := cleanUsed_eq hG
    rw [hcu] at hr
    rcases Finset.mem_union.1 hr with hMA | hOc
    · rcases Finset.mem_union.1 hMA with hM | hA
      · exact ⟨r, (Finset.mem_inter.1 hM).1, Relation.ReflTransGen.refl⟩
      · exact absurd (Finset.mem_inter.1 hA).1 (hnoA r Relation.ReflTransGen.refl)
    · have hrU : r ∈ Used C := (Finset.mem_inter.1 hOc).2
      have hrOc : r ∈ Oclean C := (Finset.mem_inter.1 hOc).1
      have hrl : r < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hrOc).1
      have h0e : supp C (op0 C r) = ∅ := (Finset.mem_filter.1 hrOc).2.2.1
      obtain ⟨_, hin, _, _, _⟩ := gate_spec hG.2.1 hrl
      have h0in : op0 C r ∈ (gateAt C r).inputs := by rw [hin]; simp
      obtain ⟨_, hr'CU, hr'lt, hr'eq⟩ := clean_wire_spec hG hrU h0in h0e
      have hrCU : r ∈ CleanUsed C := by
        rw [hcu]; exact Finset.mem_union_right _ hOc
      have hedge : CleanEdge C (op0 C r - 26) r := ⟨hr'CU, hrCU, by rwa [hr'eq]⟩
      have hnoA' : ∀ k, CleanReach C k (op0 C r - 26) → k ∉ Aless C :=
        fun k hk => hnoA k (Relation.ReflTransGen.tail hk hedge)
      obtain ⟨g, hgM, hgr'⟩ := ih (op0 C r - 26) hr'lt hr'CU hnoA'
      exact ⟨g, hgM, Relation.ReflTransGen.tail hgr' hedge⟩

lemma Aless_empty {C : Circuit} (hG : Good C) : Aless C = ∅ := by
  by_contra hne
  have hAne : (Aless C).Nonempty := Finset.nonempty_iff_ne_empty.2 hne
  obtain ⟨hMeq, _, hAeq, _, _, hread, hA2, _, hcinj, hindep⟩ := exact_equalities hG
  let j := (Aless C).min' hAne
  have hjA : j ∈ Aless C := Finset.min'_mem _ hAne
  have hjmin : ∀ k ∈ Aless C, j ≤ k := fun k hk => Finset.min'_le _ k hk
  have hjU : j ∈ Used C := (Finset.mem_inter.1 (hAeq ▸ hjA)).2
  have hjl : j < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hjA).1
  have hjAnd : (gateAt C j).op = GateOp.and :=
    (isAnd_iff _).1 (Finset.mem_filter.1 hjA).2.1
  obtain ⟨_, hinj, hnej, _, _⟩ := gate_spec hG.2.1 hjl
  have h0in : op0 C j ∈ (gateAt C j).inputs := by rw [hinj]; simp
  have h1in : op1 C j ∈ (gateAt C j).inputs := by rw [hinj]; simp
  obtain ⟨h0e, h1e⟩ := hA2 j hjA
  obtain ⟨_, hraCU, hralt, hraeq⟩ := clean_wire_spec hG hjU h0in h0e
  obtain ⟨_, hrbCU, hrblt, hrbeq⟩ := clean_wire_spec hG hjU h1in h1e
  let ra := op0 C j - 26
  let rb := op1 C j - 26
  have hrab_ne : rb ≠ ra := by
    intro heq
    have : op1 C j = op0 C j := by rw [← hrbeq, ← hraeq]; exact congrArg (26 + ·) heq
    exact hnej this.symm
  have hrb_not : ¬ CleanReach C rb ra := by
    intro hcr
    rcases Relation.ReflTransGen.cases_head hcr with heq | ⟨b, hrb_b, hb_ra⟩
    · exact hrab_ne heq
    · have hbU : b ∈ Used C := (Finset.mem_filter.1 hrb_b.2.1).1
      have hjb : j = b := unique_reader hG hread hrbCU hjU hbU (by rwa [hrbeq]) hrb_b.2.2
      rw [← hjb] at hb_ra
      have hjle := (cleanReach_le_and_mem hG hraCU hb_ra).1
      omega
  have hnoA_ra : ∀ k, CleanReach C k ra → k ∉ Aless C := by
    intro k hkr hkA
    have hkle := (cleanReach_le_and_mem hG hraCU hkr).1
    have hjle := hjmin k hkA
    omega
  obtain ⟨g₁, hg₁M, hg₁ra⟩ := cleanReach_has_M hG ra hraCU hnoA_ra
  let c₁ := center C g₁
  obtain ⟨l, hlmem⟩ := Finset.card_pos.1 (by rw [nbr_card c₁]; omega)
  have hadj_c₁l : pgAdj c₁ l = true := (Finset.mem_filter.1 hlmem).2
  have hind : ∀ w < 26 + C.gates.length,
      (w < 26 ∨ (26 ≤ w ∧ w - 26 ∈ Used C)) →
      (supp C w = ∅ → ¬ CleanReach C (w - 26) ra → val C (pair c₁ l) w = false) ∧
      (supp C w ≠ ∅ → (val C (pair c₁ l) w = true ↔ c₁ ∈ supp C w ∨ l ∈ supp C w)) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hwl hwu
      rcases Nat.lt_or_ge w 26 with hlt | hge
      · have hne_s : supp C w ≠ ∅ := by
          rw [supp_input C hlt]; exact Finset.singleton_ne_empty _
        refine ⟨fun he => absurd he hne_s, fun _ => ?_⟩
        rw [val_input C (pair c₁ l) w hlt, supp_input C hlt]
        simp only [pair, decide_eq_true_eq, Finset.mem_singleton]
        exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
      · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
        have hkU : k ∈ Used C := by
          rcases hwu with hlt | ⟨_, hkU⟩
          · omega
          · simpa using hkU
        have hkl : k < C.gates.length := by omega
        obtain ⟨hop, hink, _, h0lt, h1lt⟩ := gate_spec hG.2.1 hkl
        have hk0in : op0 C k ∈ (gateAt C k).inputs := by rw [hink]; simp
        have hk1in : op1 C k ∈ (gateAt C k).inputs := by rw [hink]; simp
        have ih0 := ih (op0 C k) h0lt (by omega) (used_closed hG hkU hk0in)
        have ih1 := ih (op1 C k) h1lt (by omega) (used_closed hG hkU hk1in)
        rcases hop with hand | hor
        · have hsk : supp C (26 + k) = ∅ := supp_and hG hkl hand
          refine ⟨fun _ hnr => ?_, fun hne_s => absurd hsk hne_s⟩
          have hnrk : ¬ CleanReach C k ra := by simpa using hnr
          by_cases hkM : k ∈ Mset C
          · have hkneg₁ : k ≠ g₁ := fun heq => hnrk (heq ▸ hg₁ra)
            have hcne : center C k ≠ c₁ := fun heq => hkneg₁ (hcinj k hkM g₁ hg₁M heq)
            have hnotadj : pgAdj c₁ (center C k) = false := hindep g₁ hg₁M k hkM
            have hclne : center C k ≠ l := by
              intro heq
              rw [heq, hadj_c₁l] at hnotadj
              exact Bool.false_ne_true hnotadj.symm
            obtain ⟨hcw, _, hpair⟩ := cw_lw_spec hG hkM
            have hcw_ne : supp C (cw C k) ≠ ∅ := by
              rw [hcw]; exact Finset.singleton_ne_empty _
            have hcw_f : val C (pair c₁ l) (cw C k) = false := by
              have hiff : val C (pair c₁ l) (cw C k) = true ↔
                  c₁ ∈ supp C (cw C k) ∨ l ∈ supp C (cw C k) := by
                rcases hpair with ⟨hcw0, _⟩ | ⟨hcw1, _⟩
                · rw [hcw0]; exact ih0.2 (by rwa [← hcw0])
                · rw [hcw1]; exact ih1.2 (by rwa [← hcw1])
              rw [hcw] at hiff
              simp only [Finset.mem_singleton] at hiff
              rw [Bool.eq_false_iff]
              intro ht
              rcases hiff.1 ht with h | h
              · exact hcne h.symm
              · exact hclne h.symm
            rw [val_and hG.2.1 (pair c₁ l) hkl hand]
            rcases hpair with ⟨hcw0, _⟩ | ⟨hcw1, _⟩
            · rw [← hcw0, hcw_f]; simp
            · rw [← hcw1, hcw_f]; simp
          · have hkA : k ∈ Aless C := by
              simp only [Mset, Finset.mem_filter, Finset.mem_range, isAnd_iff] at hkM
              simp only [Aless, Finset.mem_filter, Finset.mem_range, isAnd_iff]
              refine ⟨hkl, hand, ?_⟩
              by_contra hboth
              push Not at hboth
              exact hkM ⟨hkl, hand, hboth.1, hboth.2⟩
            by_cases hkj : k = j
            · subst hkj
              have h1f : val C (pair c₁ l) (op1 C j) = false :=
                ih1.1 h1e hrb_not
              rw [val_and hG.2.1 (pair c₁ l) hkl hand, h1f]; simp
            · have hk0e : supp C (op0 C k) = ∅ := (hA2 k hkA).1
              obtain ⟨_, hruCU, _, hrueq⟩ := clean_wire_spec hG hkU hk0in hk0e
              have hru_not : ¬ CleanReach C (op0 C k - 26) ra := by
                intro hcr
                rcases cleanReach_reader hG hread hraCU hjU (by rwa [hraeq]) hcr hkU
                  (by rwa [hrueq]) with h | h
                · exact hkj h
                · exact hnrk h
              have h0f : val C (pair c₁ l) (op0 C k) = false := ih0.1 hk0e hru_not
              rw [val_and hG.2.1 (pair c₁ l) hkl hand, h0f]; simp
        · have hsor : supp C (26 + k) = supp C (op0 C k) ∪ supp C (op1 C k) :=
            supp_or hG.2.1 hkl hor
          have hkj : k ≠ j := by
            intro heq; subst heq; rw [hjAnd] at hor; cases hor
          by_cases h0e : supp C (op0 C k) = ∅
          · by_cases h1e' : supp C (op1 C k) = ∅
            · have hsk : supp C (26 + k) = ∅ := by rw [hsor, h0e, h1e', Finset.union_empty]
              refine ⟨fun _ hnr => ?_, fun hne_s => absurd hsk hne_s⟩
              have hnrk : ¬ CleanReach C k ra := by simpa using hnr
              obtain ⟨_, _, _, h0eq⟩ := clean_wire_spec hG hkU hk0in h0e
              obtain ⟨_, _, _, h1eq⟩ := clean_wire_spec hG hkU hk1in h1e'
              have h0not : ¬ CleanReach C (op0 C k - 26) ra := by
                intro hcr
                rcases cleanReach_reader hG hread hraCU hjU (by rwa [hraeq]) hcr hkU
                  (by rwa [h0eq]) with h | h
                · exact hkj h
                · exact hnrk h
              have h1not : ¬ CleanReach C (op1 C k - 26) ra := by
                intro hcr
                rcases cleanReach_reader hG hread hraCU hjU (by rwa [hraeq]) hcr hkU
                  (by rwa [h1eq]) with h | h
                · exact hkj h
                · exact hnrk h
              rw [val_or hG.2.1 (pair c₁ l) hkl hor, ih0.1 h0e h0not, ih1.1 h1e' h1not]; rfl
            · have hsk : supp C (26 + k) = supp C (op1 C k) := by
                rw [hsor, h0e, Finset.empty_union]
              refine ⟨fun he => absurd (hsk.symm.trans he) h1e', fun _ => ?_⟩
              obtain ⟨_, _, _, h0eq⟩ := clean_wire_spec hG hkU hk0in h0e
              have hnrk : ¬ CleanReach C k ra := by
                intro hcr
                have hkCU := (cleanReach_le_and_mem hG hraCU hcr).2
                have hke : supp C (26 + k) = ∅ := (Finset.mem_filter.1 hkCU).2
                exact h1e' (hsk.symm.trans hke)
              have h0not : ¬ CleanReach C (op0 C k - 26) ra := by
                intro hcr
                rcases cleanReach_reader hG hread hraCU hjU (by rwa [hraeq]) hcr hkU
                  (by rwa [h0eq]) with h | h
                · exact hkj h
                · exact hnrk h
              rw [val_or hG.2.1 (pair c₁ l) hkl hor, ih0.1 h0e h0not, Bool.false_or, hsk]
              exact ih1.2 h1e'
          · by_cases h1e' : supp C (op1 C k) = ∅
            · have hsk : supp C (26 + k) = supp C (op0 C k) := by
                rw [hsor, h1e', Finset.union_empty]
              refine ⟨fun he => absurd (hsk.symm.trans he) h0e, fun _ => ?_⟩
              obtain ⟨_, _, _, h1eq⟩ := clean_wire_spec hG hkU hk1in h1e'
              have hnrk : ¬ CleanReach C k ra := by
                intro hcr
                have hkCU := (cleanReach_le_and_mem hG hraCU hcr).2
                have hke : supp C (26 + k) = ∅ := (Finset.mem_filter.1 hkCU).2
                exact h0e (hsk.symm.trans hke)
              have h1not : ¬ CleanReach C (op1 C k - 26) ra := by
                intro hcr
                rcases cleanReach_reader hG hread hraCU hjU (by rwa [hraeq]) hcr hkU
                  (by rwa [h1eq]) with h | h
                · exact hkj h
                · exact hnrk h
              rw [val_or hG.2.1 (pair c₁ l) hkl hor, ih1.1 h1e' h1not, Bool.or_false, hsk]
              exact ih0.2 h0e
            · have hskne : supp C (26 + k) ≠ ∅ := by
                intro he
                rw [hsor, Finset.union_eq_empty] at he
                exact h0e he.1
              refine ⟨fun he => absurd he hskne, fun _ => ?_⟩
              rw [val_or hG.2.1 (pair c₁ l) hkl hor, Bool.or_eq_true, ih0.2 h0e, ih1.2 h1e', hsor]
              simp only [Finset.mem_union]
              constructor
              · rintro ((h | h) | (h | h))
                · exact Or.inl (Or.inl h)
                · exact Or.inr (Or.inl h)
                · exact Or.inl (Or.inr h)
                · exact Or.inr (Or.inr h)
              · rintro ((h | h) | (h | h))
                · exact Or.inl (Or.inl h)
                · exact Or.inr (Or.inl h)
                · exact Or.inl (Or.inr h)
                · exact Or.inr (Or.inr h)
  obtain ⟨houtEq, houtLt, houtU⟩ := outG_spec hG
  have hout_not : ¬ CleanReach C (outG C) ra := by
    intro hcr
    have hle := (cleanReach_le_and_mem hG hraCU hcr).1
    have hjle := used_le_outG hjU
    omega
  have hout_f : val C (pair c₁ l) C.output = false :=
    (hind C.output (by omega) (Or.inr ⟨by omega, by simpa [outG] using houtU⟩)).1
      (supp_out hG) hout_not
  rw [val_pair_out hG c₁ l, hadj_c₁l] at hout_f
  exact Bool.false_ne_true hout_f.symm

lemma Omix_empty {C : Circuit} (hG : Good C) : Omix C = ∅ := by
  have hAe := Aless_empty hG
  by_contra hne
  obtain ⟨m, hmOm⟩ := Finset.nonempty_iff_ne_empty.2 hne
  obtain ⟨hMeq, _, hAeq, _, hOme, hread, _, hlw_full, hcinj, hindep⟩ := exact_equalities hG
  have hmU : m ∈ Used C := (Finset.mem_inter.1 (hOme ▸ hmOm)).2
  have hml : m < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hmOm).1
  have hmOr : (gateAt C m).op = GateOp.or := (isOr_iff _).1 (Finset.mem_filter.1 hmOm).2.1
  have hmSides := (Finset.mem_filter.1 hmOm).2.2
  obtain ⟨_, hinm, _, _, _⟩ := gate_spec hG.2.1 hml
  have hm_ne : supp C (26 + m) ≠ ∅ := by
    rw [supp_or hG.2.1 hml hmOr]
    intro he
    rw [Finset.union_eq_empty] at he
    rcases hmSides with ⟨_, h1⟩ | ⟨h0, _⟩
    · exact (Finset.nonempty_iff_ne_empty.1 h1) he.2
    · exact (Finset.nonempty_iff_ne_empty.1 h0) he.1
  have ham_ex : ∃ am ∈ (gateAt C m).inputs, supp C am = ∅ := by
    rcases hmSides with ⟨h0, _⟩ | ⟨_, h1⟩
    · exact ⟨op0 C m, by rw [hinm]; simp, h0⟩
    · exact ⟨op1 C m, by rw [hinm]; simp, h1⟩
  obtain ⟨am, hamin, hame⟩ := ham_ex
  obtain ⟨_, hraCU, hralt, hraeq⟩ := clean_wire_spec hG hmU hamin hame
  let ra := am - 26
  have hnoA_ra : ∀ k, CleanReach C k ra → k ∉ Aless C := by
    intro k _ hkA
    rw [hAe] at hkA
    exact Finset.notMem_empty k hkA
  obtain ⟨g₁, hg₁M, hg₁ra⟩ := cleanReach_has_M hG ra hraCU hnoA_ra
  let c₁ := center C g₁
  have hl_ex : ∃ l ∈ nbr c₁, ∀ c₂ : Fin 26, c₂ ≠ c₁ → supp C (26 + m) = {c₂} → l ∉ nbr c₂ := by
    by_cases hex : ∃ c₂ : Fin 26, c₂ ≠ c₁ ∧ supp C (26 + m) = {c₂}
    · obtain ⟨c₂, hne2, hsing⟩ := hex
      have hcard : 0 < (nbr c₁ \ nbr c₂).card := by
        have h1 := nbr_card c₁
        have h2 := c4_free c₁ c₂ hne2.symm
        have h3 := Finset.card_sdiff_add_card_inter (nbr c₁) (nbr c₂)
        omega
      obtain ⟨l, hl⟩ := Finset.card_pos.1 hcard
      rw [Finset.mem_sdiff] at hl
      refine ⟨l, hl.1, ?_⟩
      intro c₃ _ hsing₃
      have heq : c₃ = c₂ := Finset.singleton_injective (hsing₃.symm.trans hsing)
      subst heq
      exact hl.2
    · push Not at hex
      obtain ⟨l, hl⟩ := Finset.card_pos.1 (by rw [nbr_card c₁]; omega)
      exact ⟨l, hl, fun c₂ hne2 hsing => absurd hsing (hex c₂ hne2)⟩
  obtain ⟨l, hlmem, hl_avoid⟩ := hl_ex
  have hadj_c₁l : pgAdj c₁ l = true := (Finset.mem_filter.1 hlmem).2
  have hind : ∀ w < 26 + C.gates.length,
      (w < 26 ∨ (26 ≤ w ∧ w - 26 ∈ Used C)) →
      (supp C w = ∅ → ¬ CleanReach C (w - 26) ra → val C (pair c₁ l) w = false) ∧
      (supp C w ≠ ∅ → val C (pair c₁ l) w = true →
        c₁ ∈ supp C w ∨ l ∈ supp C w ∨ supp C (26 + m) ⊆ supp C w) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hwl hwu
      rcases Nat.lt_or_ge w 26 with hlt | hge
      · have hne_s : supp C w ≠ ∅ := by
          rw [supp_input C hlt]; exact Finset.singleton_ne_empty _
        refine ⟨fun he => absurd he hne_s, fun _ hv => ?_⟩
        rw [val_input C (pair c₁ l) w hlt] at hv
        simp only [pair, decide_eq_true_eq] at hv
        rw [supp_input C hlt]
        rcases hv with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr (Or.inl (by simp [h]))
      · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
        have hkU : k ∈ Used C := by
          rcases hwu with hlt | ⟨_, hkU⟩
          · omega
          · simpa using hkU
        have hkl : k < C.gates.length := by omega
        obtain ⟨hop, hink, _, h0lt, h1lt⟩ := gate_spec hG.2.1 hkl
        have hk0in : op0 C k ∈ (gateAt C k).inputs := by rw [hink]; simp
        have hk1in : op1 C k ∈ (gateAt C k).inputs := by rw [hink]; simp
        have ih0 := ih (op0 C k) h0lt (by omega) (used_closed hG hkU hk0in)
        have ih1 := ih (op1 C k) h1lt (by omega) (used_closed hG hkU hk1in)
        rcases hop with hand | hor
        · have hsk : supp C (26 + k) = ∅ := supp_and hG hkl hand
          refine ⟨fun _ hnr => ?_, fun hne_s => absurd hsk hne_s⟩
          have hnrk : ¬ CleanReach C k ra := by simpa using hnr
          have hkM : k ∈ Mset C := by
            simp only [Mset, Finset.mem_filter, Finset.mem_range, isAnd_iff]
            refine ⟨hkl, hand, ?_⟩
            by_contra hnot
            push Not at hnot
            have hkA : k ∈ Aless C := by
              simp only [Aless, Finset.mem_filter, Finset.mem_range, isAnd_iff]
              by_cases h0e : supp C (op0 C k) = ∅
              · exact ⟨hkl, hand, Or.inl h0e⟩
              · have h1e : supp C (op1 C k) = ∅ :=
                  hnot (Finset.nonempty_iff_ne_empty.2 h0e)
                exact ⟨hkl, hand, Or.inr h1e⟩
            rw [hAe] at hkA
            exact Finset.notMem_empty k hkA
          have hkneg₁ : k ≠ g₁ := fun heq => hnrk (heq ▸ hg₁ra)
          let c₂ := center C k
          have hcne : c₂ ≠ c₁ := fun heq => hkneg₁ (hcinj k hkM g₁ hg₁M heq)
          have hnotadj : pgAdj c₁ c₂ = false := hindep g₁ hg₁M k hkM
          have hclne : c₂ ≠ l := by
            intro heq
            rw [heq, hadj_c₁l] at hnotadj
            exact Bool.false_ne_true hnotadj.symm
          obtain ⟨hcw, _, hpair⟩ := cw_lw_spec hG hkM
          have hlw : supp C (lw C k) = nbr c₂ := hlw_full k hkM
          rw [Bool.eq_false_iff]
          intro hkt
          rw [val_and hG.2.1 (pair c₁ l) hkl hand, Bool.and_eq_true] at hkt
          have hcw_t : val C (pair c₁ l) (cw C k) = true := by
            rcases hpair with ⟨hcw0, _⟩ | ⟨hcw1, _⟩
            · rw [hcw0]; exact hkt.1
            · rw [hcw1]; exact hkt.2
          have hlw_t : val C (pair c₁ l) (lw C k) = true := by
            rcases hpair with ⟨_, hlw1⟩ | ⟨_, hlw0⟩
            · rw [hlw1]; exact hkt.2
            · rw [hlw0]; exact hkt.1
          have hcw_ne : supp C (cw C k) ≠ ∅ := by
            rw [hcw]; exact Finset.singleton_ne_empty _
          have hlw_ne : supp C (lw C k) ≠ ∅ := by
            rw [hlw]; exact Finset.nonempty_iff_ne_empty.1 (Finset.card_pos.1 (by rw [nbr_card c₂]; omega))
          have hcw_res : c₁ ∈ supp C (cw C k) ∨ l ∈ supp C (cw C k) ∨
              supp C (26 + m) ⊆ supp C (cw C k) := by
            rcases hpair with ⟨hcw0, _⟩ | ⟨hcw1, _⟩
            · rw [hcw0] at hcw_ne hcw_t ⊢; exact ih0.2 hcw_ne hcw_t
            · rw [hcw1] at hcw_ne hcw_t ⊢; exact ih1.2 hcw_ne hcw_t
          rw [hcw] at hcw_res
          have hsub_sing : supp C (26 + m) ⊆ {c₂} := by
            rcases hcw_res with h | h | h
            · exact absurd (Finset.mem_singleton.1 h).symm hcne
            · exact absurd (Finset.mem_singleton.1 h).symm hclne
            · exact h
          have hsing_m : supp C (26 + m) = {c₂} :=
            (Finset.subset_singleton_iff.1 hsub_sing).resolve_left hm_ne
          have hlw_res : c₁ ∈ supp C (lw C k) ∨ l ∈ supp C (lw C k) ∨
              supp C (26 + m) ⊆ supp C (lw C k) := by
            rcases hpair with ⟨_, hlw1⟩ | ⟨_, hlw0⟩
            · rw [hlw1] at hlw_ne hlw_t ⊢; exact ih1.2 hlw_ne hlw_t
            · rw [hlw0] at hlw_ne hlw_t ⊢; exact ih0.2 hlw_ne hlw_t
          rw [hlw] at hlw_res
          rcases hlw_res with h | h | h
          · have h1 : pgAdj c₂ c₁ = true := (Finset.mem_filter.1 h).2
            rw [pgAdj_symm, hnotadj] at h1
            exact Bool.false_ne_true h1
          · exact hl_avoid c₂ hcne hsing_m h
          · have hmem : c₂ ∈ nbr c₂ := h (by rw [hsing_m]; simp)
            have hloop : pgAdj c₂ c₂ = true := (Finset.mem_filter.1 hmem).2
            rw [pgAdj_irrefl] at hloop
            exact Bool.false_ne_true hloop
        · have hsor : supp C (26 + k) = supp C (op0 C k) ∪ supp C (op1 C k) :=
            supp_or hG.2.1 hkl hor
          by_cases h0e : supp C (op0 C k) = ∅
          · by_cases h1e : supp C (op1 C k) = ∅
            · have hsk : supp C (26 + k) = ∅ := by rw [hsor, h0e, h1e, Finset.union_empty]
              refine ⟨fun _ hnr => ?_, fun hne_s => absurd hsk hne_s⟩
              have hnrk : ¬ CleanReach C k ra := by simpa using hnr
              have hkm : k ≠ m := fun heq => hm_ne (heq ▸ hsk)
              obtain ⟨_, _, _, h0eq⟩ := clean_wire_spec hG hkU hk0in h0e
              obtain ⟨_, _, _, h1eq⟩ := clean_wire_spec hG hkU hk1in h1e
              have h0not : ¬ CleanReach C (op0 C k - 26) ra := by
                intro hcr
                rcases cleanReach_reader hG hread hraCU hmU (by rwa [hraeq]) hcr hkU
                  (by rwa [h0eq]) with h | h
                · exact hkm h
                · exact hnrk h
              have h1not : ¬ CleanReach C (op1 C k - 26) ra := by
                intro hcr
                rcases cleanReach_reader hG hread hraCU hmU (by rwa [hraeq]) hcr hkU
                  (by rwa [h1eq]) with h | h
                · exact hkm h
                · exact hnrk h
              rw [val_or hG.2.1 (pair c₁ l) hkl hor, ih0.1 h0e h0not, ih1.1 h1e h1not]; rfl
            · have hsk : supp C (26 + k) = supp C (op1 C k) := by
                rw [hsor, h0e, Finset.empty_union]
              refine ⟨fun he => absurd (hsk.symm.trans he) h1e, fun _ hv => ?_⟩
              by_cases hkm : k = m
              · subst hkm; exact Or.inr (Or.inr Finset.Subset.rfl)
              · obtain ⟨_, _, _, h0eq⟩ := clean_wire_spec hG hkU hk0in h0e
                have hnrk : ¬ CleanReach C k ra := by
                  intro hcr
                  have hkCU := (cleanReach_le_and_mem hG hraCU hcr).2
                  exact h1e (hsk.symm.trans (Finset.mem_filter.1 hkCU).2)
                have h0not : ¬ CleanReach C (op0 C k - 26) ra := by
                  intro hcr
                  rcases cleanReach_reader hG hread hraCU hmU (by rwa [hraeq]) hcr hkU
                    (by rwa [h0eq]) with h | h
                  · exact hkm h
                  · exact hnrk h
                rw [val_or hG.2.1 (pair c₁ l) hkl hor, ih0.1 h0e h0not, Bool.false_or] at hv
                rw [hsk]
                exact ih1.2 h1e hv
          · by_cases h1e : supp C (op1 C k) = ∅
            · have hsk : supp C (26 + k) = supp C (op0 C k) := by
                rw [hsor, h1e, Finset.union_empty]
              refine ⟨fun he => absurd (hsk.symm.trans he) h0e, fun _ hv => ?_⟩
              by_cases hkm : k = m
              · subst hkm; exact Or.inr (Or.inr Finset.Subset.rfl)
              · obtain ⟨_, _, _, h1eq⟩ := clean_wire_spec hG hkU hk1in h1e
                have hnrk : ¬ CleanReach C k ra := by
                  intro hcr
                  have hkCU := (cleanReach_le_and_mem hG hraCU hcr).2
                  exact h0e (hsk.symm.trans (Finset.mem_filter.1 hkCU).2)
                have h1not : ¬ CleanReach C (op1 C k - 26) ra := by
                  intro hcr
                  rcases cleanReach_reader hG hread hraCU hmU (by rwa [hraeq]) hcr hkU
                    (by rwa [h1eq]) with h | h
                  · exact hkm h
                  · exact hnrk h
                rw [val_or hG.2.1 (pair c₁ l) hkl hor, ih1.1 h1e h1not, Bool.or_false] at hv
                rw [hsk]
                exact ih0.2 h0e hv
            · have hskne : supp C (26 + k) ≠ ∅ := by
                intro he
                rw [hsor, Finset.union_eq_empty] at he
                exact h0e he.1
              refine ⟨fun he => absurd he hskne, fun _ hv => ?_⟩
              rw [val_or hG.2.1 (pair c₁ l) hkl hor, Bool.or_eq_true] at hv
              rw [hsor]
              rcases hv with h0t | h1t
              · rcases ih0.2 h0e h0t with h | h | h
                · exact Or.inl (Finset.mem_union_left _ h)
                · exact Or.inr (Or.inl (Finset.mem_union_left _ h))
                · exact Or.inr (Or.inr (h.trans Finset.subset_union_left))
              · rcases ih1.2 h1e h1t with h | h | h
                · exact Or.inl (Finset.mem_union_right _ h)
                · exact Or.inr (Or.inl (Finset.mem_union_right _ h))
                · exact Or.inr (Or.inr (h.trans Finset.subset_union_right))
  obtain ⟨houtEq, houtLt, houtU⟩ := outG_spec hG
  have hout_not : ¬ CleanReach C (outG C) ra := by
    intro hcr
    have hle := (cleanReach_le_and_mem hG hraCU hcr).1
    have hmle := used_le_outG hmU
    omega
  have hout_f : val C (pair c₁ l) C.output = false :=
    (hind C.output (by omega) (Or.inr ⟨by omega, by simpa [outG] using houtU⟩)).1
      (supp_out hG) hout_not
  rw [val_pair_out hG c₁ l, hadj_c₁l] at hout_f
  exact Bool.false_ne_true hout_f.symm

lemma unclean_cone_unclean {C : Circuit} (hG : Good C) (hOe : Omix C = ∅) :
    ∀ j < C.gates.length, supp C (26 + j) ≠ ∅ →
      ∀ i, InCone 26 C i j → supp C (26 + i) ≠ ∅ := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjl hne i hic
    obtain ⟨hop, hinj, _, _, _⟩ := gate_spec hG.2.1 hjl
    have hor : (gateAt C j).op = GateOp.or := by
      rcases hop with hand | hor
      · exact absurd (supp_and hG hjl hand) hne
      · exact hor
    have hsor : supp C (26 + j) = supp C (op0 C j) ∪ supp C (op1 C j) :=
      supp_or hG.2.1 hjl hor
    have hboth : supp C (op0 C j) ≠ ∅ ∧ supp C (op1 C j) ≠ ∅ := by
      constructor
      · intro h0e
        have h1ne : (supp C (op1 C j)).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h1e
          rw [hsor, h0e, h1e, Finset.union_empty] at hne
          exact hne rfl
        have hjOm : j ∈ Omix C := by
          simp only [Omix, Finset.mem_filter, Finset.mem_range, isOr_iff]
          exact ⟨hjl, hor, Or.inl ⟨h0e, h1ne⟩⟩
        rw [hOe] at hjOm
        exact Finset.notMem_empty j hjOm
      · intro h1e
        have h0ne : (supp C (op0 C j)).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h0e
          rw [hsor, h0e, h1e, Finset.union_empty] at hne
          exact hne rfl
        have hjOm : j ∈ Omix C := by
          simp only [Omix, Finset.mem_filter, Finset.mem_range, isOr_iff]
          exact ⟨hjl, hor, Or.inr ⟨h0ne, h1e⟩⟩
        rw [hOe] at hjOm
        exact Finset.notMem_empty j hjOm
    rw [inCone_iff] at hic
    obtain ⟨_, k, hkj, hkin, rfl | hik⟩ := hic
    · rw [hinj] at hkin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkin
      rcases hkin with heq | heq
      · rw [heq]; exact hboth.1
      · rw [heq]; exact hboth.2
    · have hkne : supp C (26 + k) ≠ ∅ := by
        rw [hinj] at hkin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkin
        rcases hkin with heq | heq
        · rw [heq]; exact hboth.1
        · rw [heq]; exact hboth.2
      exact ih k hkj (by omega) hkne i hik

lemma andPairs_eq_zero {C : Circuit} (hG : Good C) :
    PEqualNP.TopForm.andPairs 26 C = 0 := by
  have hAe := Aless_empty hG
  have hOe := Omix_empty hG
  unfold PEqualNP.TopForm.andPairs
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  rintro ⟨i, j⟩ hmem
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem
  obtain ⟨⟨hil, hjl⟩, hiAnd, hjAnd, hic⟩ := hmem
  obtain ⟨_, hinj, _, _, _⟩ := gate_spec hG.2.1 hjl
  have hboth : supp C (op0 C j) ≠ ∅ ∧ supp C (op1 C j) ≠ ∅ := by
    constructor
    · intro h0e
      have hjA : j ∈ Aless C := by
        simp only [Aless, Finset.mem_filter, Finset.mem_range, isAnd_iff]
        exact ⟨hjl, hjAnd, Or.inl h0e⟩
      rw [hAe] at hjA
      exact Finset.notMem_empty j hjA
    · intro h1e
      have hjA : j ∈ Aless C := by
        simp only [Aless, Finset.mem_filter, Finset.mem_range, isAnd_iff]
        exact ⟨hjl, hjAnd, Or.inr h1e⟩
      rw [hAe] at hjA
      exact Finset.notMem_empty j hjA
  rw [inCone_iff] at hic
  obtain ⟨_, k, hkj, hkin, rfl | hik⟩ := hic
  · have hkne : supp C (26 + i) ≠ ∅ := by
      rw [hinj] at hkin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkin
      rcases hkin with heq | heq
      · rw [heq]; exact hboth.1
      · rw [heq]; exact hboth.2
    exact hkne (supp_and hG hil hiAnd)
  · have hkne : supp C (26 + k) ≠ ∅ := by
      rw [hinj] at hkin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkin
      rcases hkin with heq | heq
      · rw [heq]; exact hboth.1
      · rw [heq]; exact hboth.2
    exact unclean_cone_unclean hG hOe k (by omega) hkne i hik (supp_and hG hil hiAnd)


lemma has_singleton {C : Circuit} (hG : Good C) (u v : Fin 26) :
    ∀ w, (supp C w).Nonempty → val C (pair u v) w = true →
      val C (one u) w = true ∨ val C (one v) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hs hp
    by_cases hinput : w < 26
    · simp only [val_input C _ w hinput] at hp ⊢
      have hw : (⟨w, hinput⟩ : Fin 26) = u ∨ (⟨w, hinput⟩ : Fin 26) = v := by
        simpa [pair] using hp
      rcases hw with hu | hv
      · exact Or.inl (by simp [one, hu])
      · exact Or.inr (by simp [one, hv])
    · have hbound : w < 26 + C.gates.length := by
        by_contra! h
        have hlen := foldl_len C.gates (List.ofFn (pair u v))
        simp only [List.length_ofFn] at hlen
        unfold val at hp
        rw [wires_eq, List.getD_eq_default _ _ (by rw [hlen]; exact h)] at hp
        contradiction
      let k := w - 26
      have hw : 26 + k = w := by dsimp [k]; omega
      have hk : k < C.gates.length := by omega
      rw [← hw] at hs hp ⊢
      obtain ⟨hop, _, _, ha, hb⟩ := gate_spec hG.2.1 hk
      have hor : (gateAt C k).op = GateOp.or := by
        rcases hop with hand | hor
        · rw [supp_and hG hk hand] at hs
          exact False.elim (Finset.not_nonempty_empty hs)
        · exact hor
      have hmix : ¬ ((supp C (op0 C k) = ∅ ∧ (supp C (op1 C k)).Nonempty) ∨
          ((supp C (op0 C k)).Nonempty ∧ supp C (op1 C k) = ∅)) := by
        intro hbad
        have hm : k ∈ Omix C :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, (isOr_iff _).mpr hor, hbad⟩
        simp only [Omix_empty hG, Finset.notMem_empty] at hm
      rw [supp_or hG.2.1 hk hor] at hs
      have both : (supp C (op0 C k)).Nonempty ∧ (supp C (op1 C k)).Nonempty := by
        by_cases h0 : (supp C (op0 C k)).Nonempty
        · refine ⟨h0, ?_⟩
          by_contra h1
          have he : supp C (op1 C k) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h1
          exact hmix (Or.inr ⟨h0, he⟩)
        · have he : supp C (op0 C k) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h0
          rw [he, Finset.empty_union] at hs
          exact False.elim (hmix (Or.inl ⟨he, hs⟩))
      rw [val_or hG.2.1 _ hk hor, Bool.or_eq_true] at hp
      rcases hp with hp | hp
      · rcases ih _ (by omega) both.1 hp with hu | hv
        · exact Or.inl (by simp [val_or hG.2.1 _ hk hor, hu])
        · exact Or.inr (by simp [val_or hG.2.1 _ hk hor, hv])
      · rcases ih _ (by omega) both.2 hp with hu | hv
        · exact Or.inl (by simp [val_or hG.2.1 _ hk hor, hu])
        · exact Or.inr (by simp [val_or hG.2.1 _ hk hor, hv])

end PEqualNP.Outside.L_meta_2613_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_2613_aux in
theorem PEqualNP.Outside.L_meta_2613 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (64 : ℕ) →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →       (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 → x5.inputs.Nodup) →         have x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => x5 - x6 = (0 : Fin (13 : ℕ)) ∨ x5 - x6 = (1 : Fin (13 : ℕ)) ∨ x5 - x6 = (3 : Fin (13 : ℕ)) ∨ x5 - x6 = (9 : Fin (13 : ℕ));         have x6 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ) => (x1.wires (List.ofFn x6)).getD x7 Bool.false;         (∀ (x7 : Fin (26 : ℕ) → Bool), x6 x7 x1.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x5 x8 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →           (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x10 : Fin (26 : ℕ) → Bool), x6 x10 ((26 : ℕ) + x8) = Bool.true → x6 x10 x1.output = Bool.true) →             ∀ (x9 x10 : Fin (13 : ℕ)),               x5 x9 x10 →                 have x12 : Fin ((13 : ℕ) + (13 : ℕ)) := Fin.castAdd (13 : ℕ) x9;                 have x13 : Fin ((13 : ℕ) + (13 : ℕ)) := Fin.natAdd (13 : ℕ) x10;                 have x14 : ℕ → ℕ → ℕ → Prop := fun (x14 x15 x16 : ℕ) => x1.gates[x14]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x15, x16] : PEqualNP.CircuitLowerBounds.Gate } ∧ x6 (fun (x17 : Fin (26 : ℕ)) => Decidable.decide (x17 = x12 ∨ x17 = x13)) ((26 : ℕ) + x14) = Bool.true;                 have x15 : Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x15 : Fin (26 : ℕ)) (x16 x17 : ℕ) => (x6 (fun (x18 : Fin (26 : ℕ)) => Decidable.decide (x18 = x15)) x16 || x6 (fun (x18 : Fin (26 : ℕ)) => Decidable.decide (x18 = x15)) x17) = Bool.true;                 ∀ (x16 x17 x18 : ℕ), x14 x16 x17 x18 → x15 x12 x17 x18 ∨ x15 x13 x17 x18 := by
  dsimp only
  intro C hsize hao hnodup hcorrect hclean p l _ j a b hactive
  rcases hactive with ⟨hgate, htrue⟩
  have hV : ValidGates C := by
    intro k g hg
    have hmem : g ∈ C.gates := List.mem_iff_getElem?.mpr ⟨k, hg⟩
    have hlen := hao.2.2 g hmem
    have hk : k < C.gates.length := by
      by_contra! h
      rw [List.getElem?_eq_none h] at hg
      contradiction
    have hg' : gateAt C k = g := gateAt_some hg
    have hlist : ∃ x y, g.inputs = [x, y] := by
      cases hi : g.inputs with
      | nil => simp [hi] at hlen
      | cons x xs =>
        cases xs with
        | nil => simp [hi] at hlen
        | cons y ys =>
          cases ys with
          | nil => exact ⟨x, y, rfl⟩
          | cons z zs => simp [hi] at hlen
    obtain ⟨x, y, hlist⟩ := hlist
    have hd := hnodup k g hg
    have hx : x ∈ (gateAt C k).inputs := by simp [hg', hlist]
    have hy : y ∈ (gateAt C k).inputs := by simp [hg', hlist]
    exact ⟨hao.1 g hmem, x, y, hlist, by simpa [hlist] using hd,
      hao.2.1 k hk x hx, hao.2.1 k hk y hy⟩
  have hG : Good C := by
    refine ⟨hsize, hV, ?_, ?_⟩
    · intro x
      simpa [val, D13, Finset.mem_insert, Finset.mem_singleton] using hcorrect x
    · intro k _ hop x hx
      exact hclean k hop x hx
  have hj : j < C.gates.length := by
    by_contra! h
    rw [List.getElem?_eq_none h] at hgate
    contradiction
  have hgate' : gateAt C j = ⟨.and, [a, b]⟩ := gateAt_some hgate
  have hop : (gateAt C j).op = .and := by rw [hgate']
  have ha : op0 C j = a := by simp [op0, hgate']
  have hb : op1 C j = b := by simp [op1, hgate']
  have hsa : (supp C a).Nonempty := by
    by_contra hn
    have he : supp C a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hm : j ∈ Aless C :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, (isAnd_iff _).mpr hop,
        Or.inl (by simpa only [ha] using he)⟩
    simp only [Aless_empty hG, Finset.notMem_empty] at hm
  let u : Fin 26 := Fin.castAdd 13 p
  let v : Fin 26 := Fin.natAdd 13 l
  have hp : val C (pair u v) (26 + j) = true := htrue
  rw [val_and hV _ hj hop, ha, hb, Bool.and_eq_true] at hp
  rcases has_singleton hG u v _ hsa hp.1 with hu | hv
  · exact Or.inl (by simpa [val, one, u, hu] using
      (show (val C (one u) a || val C (one u) b) = true by simp [hu]))
  · exact Or.inr (by simpa [val, one, v, hv] using
      (show (val C (one v) a || val C (one v) b) = true by simp [hv]))

