import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2069_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open Relation

def differences : Finset (Fin 13) := {0, 1, 3, 9}

abbrev Vertex := Fin 26
abbrev Point := Fin 13
abbrev Line := Fin 13

def point (p : Point) : Vertex := Fin.castAdd 13 p
def line (l : Line) : Vertex := Fin.natAdd 13 l

def incidence (p : Point) (l : Line) : Prop := p - l ∈ differences

def accepts (x : Vertex → Bool) : Prop :=
  ∃ p l, incidence p l ∧ x (point p) = true ∧ x (line l) = true

def computes (C : Circuit) : Prop :=
  ∀ x : Vertex → Bool, C.eval (List.ofFn x) = true ↔ accepts x

def binary (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧
    ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j

def clean (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = .and → ∀ x : Vertex → Bool,
    (C.wires (List.ofFn x)).getD (26 + j) false = true → C.eval (List.ofFn x) = true

def single (u : Vertex) : Vertex → Bool := fun v => decide (v = u)
def pair (u v : Vertex) : Vertex → Bool := fun w => decide (w = u ∨ w = v)

lemma point_ne_line (p : Point) (l : Line) : point p ≠ line l := by
  intro h
  have hp := p.isLt
  have hv := congrArg Fin.val h
  change p.val = 13 + l.val at hv
  omega

lemma no_singleton (u : Vertex) : ¬ accepts (single u) := by
  rintro ⟨p,l,_,hp,hl⟩
  exact point_ne_line p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)

lemma pair_incidence (p : Point) (l : Line) (h : incidence p l) :
    accepts (pair (point p) (line l)) := by
  exact ⟨p, l, h, by simp [pair], by simp [pair]⟩

lemma accepted_pair_iff (u v : Vertex) : accepts (pair u v) ↔
    ∃ p l, incidence p l ∧ ((u = point p ∧ v = line l) ∨ (v = point p ∧ u = line l)) := by
  constructor
  · rintro ⟨p,l,h,hp,hl⟩
    rcases of_decide_eq_true hp with hpu | hpv <;> rcases of_decide_eq_true hl with hlu | hlv
    · exact (point_ne_line p l (hpu.trans hlu.symm)).elim
    · exact ⟨p, l, h, Or.inl ⟨hpu.symm, hlv.symm⟩⟩
    · exact ⟨p, l, h, Or.inr ⟨hpv.symm, hlu.symm⟩⟩
    · exact (point_ne_line p l (hpv.trans hlv.symm)).elim
  · rintro ⟨p,l,h,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact pair_incidence p l h
    · exact ⟨p, l, h, by simp [pair], by simp [pair]⟩


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


def reads (C : Circuit) (u w : ℕ) : Prop :=
  ∃ j < C.gates.length, w = 26 + j ∧ u ∈ (gateAt C j).inputs

abbrev live (C : Circuit) (w : ℕ) : Prop := ReflTransGen (reads C) w C.output

def value (C : Circuit) (x : Vertex → Bool) (w : ℕ) : Bool := val C (List.ofFn x) w

def support (C : Circuit) (w : ℕ) : Finset Vertex :=
  Finset.univ.filter (fun u => value C (single u) w = true)

lemma mem_support (C : Circuit) (w : ℕ) (u : Vertex) :
    u ∈ support C w ↔ value C (single u) w = true := by
  simp [support]

lemma gate_shape {C : Circuit} (h : binary C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧
    ∃ a b, (gateAt C j).inputs = [a,b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j := by
  refine h j (gateAt C j) ?_
  rw [gateAt_eq hj]
  exact List.getElem?_eq_getElem hj

lemma apply_gate {C : Circuit} {j a b : ℕ}
    (hj : j < C.gates.length) (hab : (gateAt C j).inputs = [a,b])
    (ha : a < 26 + j) (hb : b < 26 + j) (x : Vertex → Bool) :
    ((gateAt C j).op = .and →
      value C x (26 + j) = (value C x a && value C x b)) ∧
    ((gateAt C j).op = .or →
      value C x (26 + j) = (value C x a || value C x b)) := by
  have hv := val_gate (C := C) (x := List.ofFn x) List.length_ofFn hj
  constructor <;> intro hop <;>
    simpa [value, hop, hab, ha, hb, GateOp.eval] using hv

lemma input_value {C : Circuit} {w : ℕ} (hw : w < 26) (x : Vertex → Bool) :
    value C x w = x ⟨w, hw⟩ := by
  unfold value
  rw [val_input List.length_ofFn hw]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw]
  rfl

lemma beyond_value {C : Circuit} {w : ℕ} (hw : 26 + C.gates.length ≤ w)
    (x : Vertex → Bool) : value C x w = false := val_ge List.length_ofFn hw

lemma and_single_false {C : Circuit} (hF : computes C) (hC : clean C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = .and) (v : Vertex) :
    value C (single v) (26 + j) = false := by
  cases ht : value C (single v) (26 + j)
  · rfl
  · exact (no_singleton v ((hF (single v)).mp (hC j hj hop _ ht))).elim

lemma or_support {C : Circuit} {j a b : ℕ}
    (hj : j < C.gates.length) (hab : (gateAt C j).inputs = [a,b])
    (ha : a < 26 + j) (hb : b < 26 + j) (hop : (gateAt C j).op = .or) :
    support C (26 + j) = support C a ∪ support C b := by
  ext u
  simp only [mem_support, Finset.mem_union, (apply_gate hj hab ha hb (single u)).2 hop,
    Bool.or_eq_true]

lemma and_support {C : Circuit} (hF : computes C) (hC : clean C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = .and) :
    support C (26 + j) = ∅ := by
  ext u
  simp [mem_support, and_single_false hF hC hj hop]

lemma eval_mono {C : Circuit} (hB : binary C) {x y : Vertex → Bool}
    (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro htrue
    by_cases hin : w < 26
    · rw [input_value hin] at htrue ⊢
      exact hxy _ htrue
    · by_cases hge : 26 + C.gates.length ≤ w
      · simp [beyond_value hge] at htrue
      · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨hop, a, b, hab, _, ha, hb⟩ := gate_shape hB hj
        rcases hop with hand | hor
        · rw [(apply_gate hj hab ha hb x).1 hand, Bool.and_eq_true] at htrue
          rw [(apply_gate hj hab ha hb y).1 hand, Bool.and_eq_true]
          exact ⟨ih a ha htrue.1, ih b hb htrue.2⟩
        · rw [(apply_gate hj hab ha hb x).2 hor, Bool.or_eq_true] at htrue
          rw [(apply_gate hj hab ha hb y).2 hor, Bool.or_eq_true]
          exact htrue.elim (fun ax => Or.inl (ih a ha ax)) (fun bx => Or.inr (ih b hb bx))


def birth (C : Circuit) (j : ℕ) (u v : Vertex) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = .and ∧
    ∃ a b, (gateAt C j).inputs = [a,b] ∧
    ((u ∈ support C a ∧ v ∈ support C b) ∨ (v ∈ support C a ∧ u ∈ support C b))

lemma birth_true {C : Circuit} (hB : binary C) (hF : computes C) (hC : clean C)
    {j : ℕ} {u v : Vertex} (h : birth C j u v) : accepts (pair u v) := by
  obtain ⟨hj, hop, a, b, hab, hcross⟩ := h
  obtain ⟨_, c, d, hcd, _, hc, hd⟩ := gate_shape hB hj
  have he : a = c ∧ b = d := by simpa using hab.symm.trans hcd
  rcases he with ⟨rfl, rfl⟩
  apply (hF _).mp (hC j hj hop _ ?_)
  change value C (pair u v) (26 + j) = true
  rw [(apply_gate hj hab hc hd _).1 hop, Bool.and_eq_true]
  have lef : ∀ i, single u i = true → pair u v i = true := by
    intro i
    simp only [single, pair, decide_eq_true_eq]
    exact Or.inl
  have rig : ∀ i, single v i = true → pair u v i = true := by
    intro i
    simp only [single, pair, decide_eq_true_eq]
    exact Or.inr
  rcases hcross with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact ⟨eval_mono hB lef _ ((mem_support C a u).mp h1),
      eval_mono hB rig _ ((mem_support C b v).mp h2)⟩
  · exact ⟨eval_mono hB rig _ ((mem_support C a v).mp h1),
      eval_mono hB lef _ ((mem_support C b u).mp h2)⟩

set_option maxHeartbeats 2000000 in
lemma true_pair_has_origin {C : Circuit} (hB : binary C) (u v : Vertex) (w : ℕ)
    (htrue : value C (pair u v) w = true) :
    u ∈ support C w ∨ v ∈ support C w ∨
      ∃ j, birth C j u v ∧ ReflTransGen (reads C) (26 + j) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < 26
    · rw [input_value hin] at htrue
      rcases of_decide_eq_true htrue with hu | hv
      · left; rw [mem_support, input_value hin]; simp [single, hu]
      · right; left; rw [mem_support, input_value hin]; simp [single, hv]
    · by_cases hge : 26 + C.gates.length ≤ w
      · simp [beyond_value hge] at htrue
      · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨hop, a, b, hab, _, ha, hb⟩ := gate_shape hB hj
        have reada : reads C a (26 + j) := ⟨j, hj, rfl, by simp [hab]⟩
        have readb : reads C b (26 + j) := ⟨j, hj, rfl, by simp [hab]⟩
        have propagate : ∀ w', reads C w' (26 + j) →
            (∃ k, birth C k u v ∧ ReflTransGen (reads C) (26 + k) w') →
            ∃ k, birth C k u v ∧ ReflTransGen (reads C) (26 + k) (26 + j) := by
          rintro w' read ⟨k,hk,path⟩
          exact ⟨k,hk,path.tail read⟩
        rcases hop with hand | hor
        · rw [(apply_gate hj hab ha hb _).1 hand, Bool.and_eq_true] at htrue
          have xa := ih a ha htrue.1
          have xb := ih b hb htrue.2
          have same : ∀ t, t ∈ support C a → t ∈ support C b →
              t ∈ support C (26 + j) := by
            intro t
            simp only [mem_support, (apply_gate hj hab ha hb (single t)).1 hand, Bool.and_eq_true]
            exact And.intro
          have mark : ((u ∈ support C a ∧ v ∈ support C b) ∨
                        (v ∈ support C a ∧ u ∈ support C b)) →
              ∃ k, birth C k u v ∧ ReflTransGen (reads C) (26 + k) (26 + j) :=
            fun cross => ⟨j, ⟨hj, hand, a, b, hab, cross⟩, .refl⟩
          have A := propagate a reada
          have B := propagate b readb
          have U := same u
          have V := same v
          tauto
        · rw [(apply_gate hj hab ha hb _).2 hor, Bool.or_eq_true] at htrue
          rw [or_support hj hab ha hb hor]
          simp only [Finset.mem_union]
          rcases htrue with ta | tb
          · have A := propagate a reada
            have xa := ih a ha ta
            tauto
          · have B := propagate b readb
            have xb := ih b hb tb
            tauto

lemma every_incidence_has_birth {C : Circuit} (hB : binary C) (hF : computes C)
    (p : Point) (l : Line) (hl : incidence p l) :
    ∃ j, birth C j (point p) (line l) ∧ live C (26 + j) := by
  have hv : value C (pair (point p) (line l)) C.output = true :=
    (hF _).mpr (pair_incidence p l hl)
  rcases true_pair_has_origin hB (point p) (line l) C.output hv with h | h | hb
  · exact (no_singleton _ ((hF _).mp ((mem_support C C.output (point p)).mp h))).elim
  · exact (no_singleton _ ((hF _).mp ((mem_support C C.output (line l)).mp h))).elim
  · exact hb

abbrev oriented (u v : Vertex) : Prop :=
  u.val < 13 ∧ 13 ≤ v.val ∧
    (u.val + 26 - v.val) % 13 ∈ ({0, 1, 3, 9} : Finset ℕ)

abbrev adjacent (u v : Vertex) : Prop := oriented u v ∨ oriented v u

def neighbors (u : Vertex) : Finset Vertex := Finset.univ.filter (adjacent u)

lemma vertex_cases (v : Vertex) :
    (∃ p, point p = v) ∨ (∃ l, line l = v) := by
  by_cases hv : v.val < 13
  · exact Or.inl ⟨⟨v.val, hv⟩, Fin.ext rfl⟩
  · have h26 := v.isLt
    exact Or.inr ⟨⟨v.val - 13, by omega⟩, Fin.ext (show 13 + (v.val - 13) = v.val by omega)⟩

set_option maxRecDepth 6000 in
lemma adjacent_point_line : ∀ p l, adjacent (point p) (line l) ↔ incidence p l := by
  unfold incidence
  decide +kernel

lemma not_adjacent_points : ∀ p q, ¬ adjacent (point p) (point q) := by
  decide +kernel

lemma not_adjacent_lines : ∀ p q, ¬ adjacent (line p) (line q) := by
  decide +kernel

lemma adjacent_symm (u v : Vertex) : adjacent u v ↔ adjacent v u := or_comm

lemma neighbor_iff (u v : Vertex) : v ∈ neighbors u ↔ adjacent u v := by
  simp [neighbors]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma degree_four : ∀ u, (neighbors u).card = 4 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma common_at_most_one : ∀ u v : Vertex, u ≠ v →
    ((neighbors u) ∩ (neighbors v)).card ≤ 1 := by
  decide +kernel

lemma pair_sound {u v : Vertex} (h : accepts (pair u v)) : adjacent u v := by
  obtain ⟨p,l,hl,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (accepted_pair_iff _ _).mp h
  · exact (adjacent_point_line p l).mpr hl
  · exact (adjacent_symm _ _).mp ((adjacent_point_line p l).mpr hl)

lemma rectangle_star (A B : Finset Vertex) (ha : A.Nonempty) (hb : B.Nonempty)
    (cross : ∀ u ∈ A, ∀ v ∈ B, adjacent u v) :
    (∃ c, A = {c} ∧ B ⊆ neighbors c) ∨ (∃ c, B = {c} ∧ A ⊆ neighbors c) := by
  by_cases hc : A.card ≤ 1
  · obtain ⟨c, he⟩ := Finset.card_eq_one.mp (show A.card = 1 by
      have := Finset.card_pos.mpr ha
      omega)
    left
    refine ⟨c, he, fun v hv => (neighbor_iff _ _).mpr (cross _ ?_ _ hv)⟩
    simp [he]
  · have nx := Finset.one_lt_card.mp (show 1 < A.card by omega)
    obtain ⟨u, uA, v, vA, uv⟩ := nx
    have sub : B ⊆ (neighbors u) ∩ (neighbors v) := by
      intro w hw
      exact Finset.mem_inter.mpr ⟨(neighbor_iff _ _).mpr (cross _ uA _ hw),
        (neighbor_iff _ _).mpr (cross _ vA _ hw)⟩
    have hbound := (Finset.card_le_card sub).trans (common_at_most_one u v uv)
    obtain ⟨c, he⟩ := Finset.card_eq_one.mp (show B.card = 1 by
      have := Finset.card_pos.mpr hb
      omega)
    right
    refine ⟨c, he, fun u hu => (neighbor_iff _ _).mpr ((adjacent_symm _ _).mp (cross _ hu _ ?_))⟩
    simp [he]

lemma tight_counts {p a b c z distinct slots single : Nat}
    (small : p + a + b + c + z ≤ 64)
    (covers : 52 ≤ 4 * p) (leafCosts : 52 ≤ p + a)
    (readsEvery : p + z + c ≤ distinct + 1) (countSlots : distinct ≤ slots)
    (slotCap : slots + single ≤ b + 2 * c + 2 * z) :
    p = 13 ∧ a = 39 ∧ b + c + z = 12 ∧
      distinct = p + z + c - 1 ∧ slots = distinct ∧ single = 0 := by
  omega

def pg3Inc (p l : Fin 13) : Prop := p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))

lemma pg3CommonLine : ∀ p q : Fin 13, ∃ l : Fin 13, pg3Inc p l ∧ pg3Inc q l := by
  unfold pg3Inc
  decide

lemma pg3Diagonal (v : Fin 13) : pg3Inc v v := by
  simp [pg3Inc]

lemma pg3CentersOneSide (P L : Finset (Fin 13))
    (exactOne : ∀ p l, pg3Inc p l → (p ∈ P ↔ l ∉ L)) :
    (P = Finset.univ ∧ L = ∅) ∨ (P = ∅ ∧ L = Finset.univ) := by
  have pointAgreement (p : Fin 13) : p ∈ P ↔ (0 : Fin 13) ∈ P := by
    obtain ⟨l, hp, h0⟩ := pg3CommonLine p 0
    exact (exactOne p l hp).trans (exactOne 0 l h0).symm
  by_cases first : (0 : Fin 13) ∈ P
  · left
    constructor
    · ext p
      simpa using (pointAgreement p).mpr first
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro l
      exact (exactOne l l (pg3Diagonal l)).mp ((pointAgreement l).mpr first)
  · right
    constructor
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      exact fun p hp => first ((pointAgreement p).mp hp)
    · ext l
      simp only [Finset.mem_univ, iff_true]
      by_contra hL
      exact first ((pointAgreement l).mp ((exactOne l l (pg3Diagonal l)).mpr hL))

lemma tight_stars {I E : Type*} [DecidableEq I] [DecidableEq E]
    (productive : Finset I) (edges : Finset E) (star : I → Finset E)
    (prods : productive.card = 13) (edgeCount : edges.card = 52)
    (bound : ∀ a ∈ productive, (star a).card ≤ 4)
    (covers : productive.biUnion star = edges) :
    (∀ a ∈ productive, (star a).card = 4) ∧
      (∀ a ∈ productive, ∀ b ∈ productive, ∀ e ∈ star a, e ∈ star b → a = b) := by
  classical
  let zip := productive.sigma star
  let proj : (Σ _ : I, E) → E := fun e => e.2
  have image : zip.image proj = edges := by
    rw [← covers]
    ext e
    simp [zip, proj]
  have lower : 52 ≤ zip.card := by
    have := Finset.card_image_le (s := zip) (f := proj)
    rwa [image, edgeCount] at this
  have upper : zip.card ≤ 52 := by
    change (productive.sigma star).card ≤ 52
    rw [Finset.card_sigma]
    calc
      ∑ a ∈ productive, (star a).card ≤ ∑ _a ∈ productive, (4 : Nat) :=
        Finset.sum_le_sum bound
      _ = 52 := by simp [prods]
  have card : zip.card = 52 := Nat.le_antisymm upper lower
  refine ⟨?_, ?_⟩
  · intro a ha
    by_contra notFull
    have lt : (star a).card < 4 := by have := bound a ha; omega
    have totalLt : (∑ a ∈ productive, (star a).card) < ∑ _a ∈ productive, (4 : Nat) :=
      Finset.sum_lt_sum bound ⟨a, ha, lt⟩
    have eqSum : (∑ a ∈ productive, (star a).card) = 52 := by
      simpa only [zip, Finset.card_sigma] using card
    simp [prods, eqSum] at totalLt
  · intro a ha b hb e hea heb
    have hinj := (Finset.card_image_iff (s := zip) (f := proj)).mp (by
      rw [image, edgeCount, card])
    have hzipa : (⟨a, e⟩ : Σ _ : I, E) ∈ zip := Finset.mem_sigma.mpr ⟨ha, hea⟩
    have hzipb : (⟨b, e⟩ : Σ _ : I, E) ∈ zip := Finset.mem_sigma.mpr ⟨hb, heb⟩
    exact congrArg Sigma.fst (hinj hzipa hzipb rfl)



def pg3Edges : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun e => e.1 - e.2 ∈ ({0, 1, 3, 9} : Finset (Fin 13))

lemma pg3MemEdges (p l : Fin 13) : (p, l) ∈ pg3Edges ↔ pg3Inc p l := by
  simp [pg3Edges, pg3Inc]

def pg3Star : Sum (Fin 13) (Fin 13) → Finset (Fin 13 × Fin 13)
  | .inl p => pg3Edges.filter fun e => e.1 = p
  | .inr l => pg3Edges.filter fun e => e.2 = l

set_option maxRecDepth 10000 in
lemma pg3EdgesCard : pg3Edges.card = 52 := by decide

set_option maxRecDepth 10000 in
lemma pg3StarCard : ∀ center, (pg3Star center).card = 4 := by
  intro center
  rcases center with p | l
  · revert p; decide
  · revert l; decide

lemma pg3FullStarsOneSide {I : Type*} [DecidableEq I] (productive : Finset I)
    (star : I → Finset (Fin 13 × Fin 13)) (center : I → Sum (Fin 13) (Fin 13))
    (size : productive.card = 13) (covers : productive.biUnion star = pg3Edges)
    (subsets : ∀ a ∈ productive, star a ⊆ pg3Star (center a)) :
    (∀ a ∈ productive, star a = pg3Star (center a)) ∧
      (∀ a ∈ productive, ∀ b ∈ productive, center a = center b → a = b) ∧
      ((∀ a ∈ productive, ∃ p, center a = .inl p) ∨
       (∀ a ∈ productive, ∃ l, center a = .inr l)) := by
  classical
  have tight := tight_stars productive pg3Edges star size pg3EdgesCard (fun a ha => by
    calc
      (star a).card ≤ (pg3Star (center a)).card := Finset.card_le_card (subsets a ha)
      _ = 4 := pg3StarCard _) covers
  have full (a : I) (ha : a ∈ productive) : star a = pg3Star (center a) := by
    apply Finset.eq_of_subset_of_card_le (subsets a ha)
    rw [pg3StarCard, tight.1 a ha]
  have notRepeat (a : I) (ha : a ∈ productive) (b : I) (hb : b ∈ productive) :
      center a = center b → a = b := by
    intro h
    have hstars : star a = star b := by rw [full a ha, full b hb, h]
    have hNonempty : (star a).Nonempty := Finset.card_pos.mp (by simp [tight.1 a ha])
    obtain ⟨e, he⟩ := hNonempty
    exact tight.2 a ha b hb e he (hstars ▸ he)
  let P := Finset.univ.filter (fun p : Fin 13 => ∃ a ∈ productive, center a = .inl p)
  let L := Finset.univ.filter (fun l : Fin 13 => ∃ a ∈ productive, center a = .inr l)
  have memP (p : Fin 13) : p ∈ P ↔ ∃ a ∈ productive, center a = .inl p := by simp [P]
  have memL (l : Fin 13) : l ∈ L ↔ ∃ a ∈ productive, center a = .inr l := by simp [L]
  have exactOne (p l : Fin 13) (inc : pg3Inc p l) : p ∈ P ↔ l ∉ L := by
    have ep := (pg3MemEdges p l).mpr inc
    constructor
    · intro hp hl
      obtain ⟨a, ha, hap⟩ := (memP p).mp hp
      obtain ⟨b, hb, hbl⟩ := (memL l).mp hl
      have hpa : (p, l) ∈ star a := by rw [full a ha, hap]; simp [pg3Star, ep]
      have hlb : (p, l) ∈ star b := by rw [full b hb, hbl]; simp [pg3Star, ep]
      have equal := tight.2 a ha b hb (p, l) hpa hlb
      rw [equal, hbl] at hap
      contradiction
    · intro notL
      have inUnion : (p, l) ∈ productive.biUnion star := covers.symm ▸ ep
      obtain ⟨a, ha, he⟩ := Finset.mem_biUnion.mp inUnion
      rw [full a ha] at he
      cases eqc : center a with
      | inl q =>
        simp only [eqc, pg3Star, Finset.mem_filter, ep, true_and] at he
        exact (memP p).mpr ⟨a, ha, by simpa [he] using eqc⟩
      | inr q =>
        simp only [eqc, pg3Star, Finset.mem_filter, ep, true_and] at he
        exact (notL ((memL l).mpr ⟨a, ha, by simpa [he] using eqc⟩)).elim
  refine ⟨full, notRepeat, ?_⟩
  rcases pg3CentersOneSide P L exactOne with ⟨_, noL⟩ | ⟨noP, _⟩
  · left
    intro a ha
    cases hc : center a with
    | inl p => exact ⟨p, rfl⟩
    | inr l =>
      have : l ∈ L := (memL l).mpr ⟨a, ha, hc⟩
      simp [noL] at this
  · right
    intro a ha
    cases hc : center a with
    | inl p =>
      have : p ∈ P := (memP p).mpr ⟨a, ha, hc⟩
      simp [noP] at this
    | inr l => exact ⟨l, rfl⟩

namespace ZeroSlots

open scoped BigOperators

variable {W : Type*} [DecidableEq W]

def gateClass (isAnd support : W → Bool) (operand : W → Bool → W) (w : W) : Fin 5 :=
  let a := support (operand w false)
  let b := support (operand w true)
  if isAnd w then (if a && b then 0 else 4)
  else if a && b then 1 else if a || b then 2 else 3

def classGates (gates : Finset W) (isAnd support : W → Bool)
    (operand : W → Bool → W) (k : Fin 5) : Finset W :=
  gates.filter (fun w => gateClass isAnd support operand w = k)

def onePositiveAnd (isAnd support : W → Bool) (operand : W → Bool → W)
    (w : W) : Bool :=
  isAnd w && (support (operand w false) != support (operand w true))

def zeroOperandSlots (support : W → Bool) (operand : W → Bool → W) (w : W) :
    Finset Bool := Finset.univ.filter fun side => support (operand w side) = false

def slots (gates : Finset W) (support : W → Bool) (operand : W → Bool → W) :
    Finset (Σ _ : W, Bool) := gates.sigma (zeroOperandSlots support operand)

def source (operand : W → Bool → W) (slot : Σ _ : W, Bool) : W :=
  operand slot.1 slot.2

lemma mem_slots {gates : Finset W} {support : W → Bool} {operand : W → Bool → W}
    {w : W} {side : Bool} :
    (⟨w, side⟩ : Σ _ : W, Bool) ∈ slots gates support operand ↔
      w ∈ gates ∧ support (operand w side) = false := by
  simp [slots, zeroOperandSlots]

lemma sum_classes (gates : Finset W) (isAnd support : W → Bool) (operand : W → Bool → W) :
    gates.card = (classGates gates isAnd support operand 0).card +
      (classGates gates isAnd support operand 1).card +
      (classGates gates isAnd support operand 2).card +
      (classGates gates isAnd support operand 3).card +
      (classGates gates isAnd support operand 4).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := gates) (t := (Finset.univ : Finset (Fin 5)))
    (f := gateClass isAnd support operand) (by simp)
  simpa [classGates, Fin.sum_univ_succ, Nat.add_assoc] using h

lemma zero_support_class (isAnd support : W → Bool) (operand : W → Bool → W) (w : W)
    (h : support w =
      (!isAnd w && (support (operand w false) || support (operand w true)))) :
    support w = false ↔
      gateClass isAnd support operand w = 0 ∨
        gateClass isAnd support operand w = 3 ∨ gateClass isAnd support operand w = 4 := by
  cases hi : isAnd w <;> cases ha : support (operand w false) <;>
    cases hb : support (operand w true) <;> simp [h, gateClass, hi, ha, hb]

lemma sum_zero_classes (gates : Finset W)
    (isAnd support : W → Bool) (operand : W → Bool → W)
    (derived : ∀ w ∈ gates, support w =
      (!isAnd w && (support (operand w false) || support (operand w true)))) :
    (gates.filter fun w => support w = false).card =
      (classGates gates isAnd support operand 0).card +
      (classGates gates isAnd support operand 3).card +
      (classGates gates isAnd support operand 4).card := by
  let z := gates.filter fun w => support w = false
  let c := classGates gates isAnd support operand
  have hz : z = c 0 ∪ c 3 ∪ c 4 := by
    ext w
    simp only [z, c, classGates, Finset.mem_filter, Finset.mem_union]
    by_cases hw : w ∈ gates
    · simp only [hw, true_and]
      rw [zero_support_class isAnd support operand w (derived w hw)]
      tauto
    · simp [hw]
  have hd (i j : Fin 5) (h : i ≠ j) : Disjoint (c i) (c j) := by
    rw [Finset.disjoint_left]
    intro w hw hu
    exact h ((Finset.mem_filter.mp hw).2.symm.trans (Finset.mem_filter.mp hu).2)
  change z.card = _
  rw [hz, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
    ⟨hd 0 4 (by decide), hd 3 4 (by decide)⟩), Finset.card_union_of_disjoint (hd 0 3 (by decide))]

lemma slot_pointwise (isAnd support : W → Bool) (operand : W → Bool → W) (w : W) :
    (zeroOperandSlots support operand w).card +
      (if onePositiveAnd isAnd support operand w then 1 else 0) =
      (if gateClass isAnd support operand w = 2 then 1 else 0) +
      (if gateClass isAnd support operand w = 3 then 2 else 0) +
      (if gateClass isAnd support operand w = 4 then 2 else 0) := by
  have univBool : (Finset.univ : Finset Bool) = {false, true} := by decide
  simp only [zeroOperandSlots, univBool, Finset.filter_insert, Finset.filter_singleton]
  cases hi : isAnd w <;> cases ha : support (operand w false) <;>
    cases hb : support (operand w true) <;>
    simp [onePositiveAnd, gateClass, hi, ha, hb]

lemma sum_slot_counts (gates : Finset W)
    (isAnd support : W → Bool) (operand : W → Bool → W) :
    (slots gates support operand).card +
      (gates.filter fun w => onePositiveAnd isAnd support operand w = true).card =
      (classGates gates isAnd support operand 2).card +
        2 * (classGates gates isAnd support operand 3).card +
        2 * (classGates gates isAnd support operand 4).card := by
  have h := Finset.sum_congr rfl
    (fun w (_ : w ∈ gates) => slot_pointwise isAnd support operand w)
  simp only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one] at h
  simpa [slots, Finset.card_sigma, classGates, Nat.mul_comm] using h

lemma slot_use_bound (gates : Finset W) (support : W → Bool)
    (operand : W → Bool → W) (out : W)
    (used : ∀ w ∈ gates, support w = false → w ≠ out →
      ∃ g ∈ gates, ∃ side, operand g side = w) :
    (gates.filter fun w => support w = false).card ≤
      ((slots gates support operand).image (source operand)).card + 1 := by
  let z := gates.filter fun w => support w = false
  have sub : z.erase out ⊆ (slots gates support operand).image (source operand) := by
    intro w hw
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hw
    obtain ⟨g, hg, side, eq⟩ := used w (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp hm).2 hne
    exact Finset.mem_image.mpr ⟨⟨g, side⟩, mem_slots.mpr
      ⟨hg, by rw [eq]; exact (Finset.mem_filter.mp hm).2⟩, eq⟩
  have h := Finset.card_le_card sub
  have hl := Finset.card_erase_add_one (s := z) (a := out)
  by_cases hout : out ∈ z
  · exact (hl hout).symm.trans_le (Nat.add_le_add_right h 1)
  · rw [Finset.erase_eq_of_notMem hout] at h
    exact h.trans (Nat.le_succ _)

lemma no_duplicate_slots (gates : Finset W) (support : W → Bool)
    (operand : W → Bool → W)
    (tight : ((slots gates support operand).image (source operand)).card =
      (slots gates support operand).card) :
    ∀ (w : W) (h₁ h₂ : Bool) (g₁ g₂ : W), w = operand g₁ h₁ → w = operand g₂ h₂ →
      g₁ ∈ gates → g₂ ∈ gates → support w = false → g₁ = g₂ := by
  intro w h₁ h₂ g₁ g₂ he₁ he₂ hg₁ hg₂ hz
  have hInj := (Finset.card_image_iff.mp tight)
  have hm₁ : (⟨g₁, h₁⟩ : Σ _ : W, Bool) ∈ slots gates support operand :=
    mem_slots.mpr ⟨hg₁, he₁ ▸ hz⟩
  have hm₂ : (⟨g₂, h₂⟩ : Σ _ : W, Bool) ∈ slots gates support operand :=
    mem_slots.mpr ⟨hg₂, he₂ ▸ hz⟩
  exact congrArg Sigma.fst (hInj hm₁ hm₂ (he₁.symm.trans he₂))

lemma tight_live_slots (gates : Finset W) (isAnd support : W → Bool)
    (operand : W → Bool → W) (out : W)
    (derived : ∀ w ∈ gates, support w =
      (!isAnd w && (support (operand w false) || support (operand w true))))
    (used : ∀ w ∈ gates, support w = false → w ≠ out →
      ∃ g ∈ gates, ∃ side, operand g side = w)
    (small : gates.card ≤ 64)
    (covers : 52 ≤ 4 * (classGates gates isAnd support operand 0).card)
    (leafCosts : 52 ≤ (classGates gates isAnd support operand 0).card +
      (classGates gates isAnd support operand 1).card) :
    (classGates gates isAnd support operand 0).card = 13 ∧
    (classGates gates isAnd support operand 1).card = 39 ∧
    gates.card = 64 ∧
    (∀ w ∈ gates, isAnd w = true → support (operand w false) = support (operand w true)) ∧
    Set.InjOn (source operand) ↑(slots gates support operand) := by
  have counts := sum_classes gates isAnd support operand
  have zeroUsed := slot_use_bound gates support operand out used
  rw [sum_zero_classes gates isAnd support operand derived] at zeroUsed
  have capacity := sum_slot_counts gates isAnd support operand
  have distinctLe := Finset.card_image_le (s := slots gates support operand) (f := source operand)
  have equalities :
      (classGates gates isAnd support operand 0).card = 13 ∧
      (classGates gates isAnd support operand 1).card = 39 ∧
      gates.card = 64 ∧
      (gates.filter fun w => onePositiveAnd isAnd support operand w = true).card = 0 ∧
      ((slots gates support operand).image (source operand)).card =
        (slots gates support operand).card := by omega
  obtain ⟨productive, bothPositive, gateCount, noSingletonAnd, uniqueSlots⟩ := equalities
  refine ⟨productive, bothPositive, gateCount, ?_, Finset.card_image_iff.mp uniqueSlots⟩
  intro w hw hand
  by_contra hn
  have hmem : w ∈ gates.filter (fun v => onePositiveAnd isAnd support operand v = true) := by
    simp [hw, hand, hn, onePositiveAnd]
  exact (Finset.card_ne_zero.mpr ⟨w, hmem⟩) noSingletonAnd

end ZeroSlots

namespace ORForest

open scoped BigOperators

theorem supportForestBound {A : Type*} [DecidableEq A]
    (bound : ℕ) (roots : Finset ℕ) (deps : ℕ → Finset ℕ) (support : ℕ → Finset A)
    (rootsBounded : ∀ r ∈ roots, r < bound)
    (expandSpec : ∀ w, 2 ≤ (support w).card →
      (∀ v ∈ deps w, v < w) ∧ (deps w).card ≤ 2 ∧ support w = (deps w).biUnion support) :
    ∃ internal : Finset ℕ,
      (∀ w ∈ internal, 2 ≤ (support w).card ∧ (deps w).card = 2 ∧ ∃ r ∈ roots, support w ⊆ support r) ∧
      (roots.biUnion support).card ≤ roots.card + internal.card := by
  classical
  let step : ℕ → ℕ → Prop := fun w v => 2 ≤ (support w).card ∧ v ∈ deps w
  let reached := (Finset.range bound).filter fun w =>
    ∃ r ∈ roots, Relation.ReflTransGen step r w
  let internal := reached.filter fun w => 2 ≤ (support w).card
  let split := internal.filter fun w => (deps w).card = 2
  let charge (w : ℕ) : Finset (A ⊕ ℕ) :=
    if 2 ≤ (support w).card then {Sum.inr w} else (support w).image Sum.inl
  let edgeCharges (w : ℕ) := (deps w).biUnion charge
  let pool := roots.biUnion charge ∪ internal.biUnion edgeCharges

  have isEarlier {w v : ℕ} (h : step w v) : v < w := (expandSpec w h.1).1 v h.2
  have childSubset {w v : ℕ} (h : step w v) : support v ⊆ support w := by
    rw [(expandSpec w h.1).2.2]
    exact Finset.subset_biUnion_of_mem support h.2
  have pathLe {r w : ℕ} (h : Relation.ReflTransGen step r w) : w ≤ r := by
    induction h with
    | refl => exact le_rfl
    | tail _ next ih => exact (isEarlier next).le.trans ih
  have pathSubset {r w : ℕ} (h : Relation.ReflTransGen step r w) : support w ⊆ support r := by
    induction h with
    | refl => exact Finset.Subset.rfl
    | tail _ next ih => exact (childSubset next).trans ih
  have ofPath {r w : ℕ} (hr : r ∈ roots) (h : Relation.ReflTransGen step r w) : w ∈ reached :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((pathLe h).trans_lt (rootsBounded r hr)), r, hr, h⟩
  have chargeCard (w : ℕ) : (charge w).card ≤ 1 := by
    by_cases hw : 2 ≤ (support w).card
    · simp [charge, hw]
    · simpa [charge, hw, Finset.card_image_of_injective _ Sum.inl_injective] using
        (show (support w).card ≤ 1 by omega)
  have edgeChargeCard (w : ℕ) : (edgeCharges w).card ≤ (deps w).card := by
    simpa [edgeCharges] using Finset.card_biUnion_le_card_mul (deps w) charge 1 (fun v _ => chargeCard v)
  have chargeInPool {r w : ℕ} (hr : r ∈ roots) (hp : Relation.ReflTransGen step r w) :
      charge w ⊆ pool := by
    rcases Relation.ReflTransGen.cases_tail hp with rfl | ⟨v, hv, hvw⟩
    · exact (Finset.subset_biUnion_of_mem charge hr).trans Finset.subset_union_left
    · have hInternal : v ∈ internal := Finset.mem_filter.mpr ⟨ofPath hr hv, hvw.1⟩
      exact (Finset.subset_biUnion_of_mem charge hvw.2).trans
        ((Finset.subset_biUnion_of_mem edgeCharges hInternal).trans Finset.subset_union_right)
  have terminal (w : ℕ) : ∀ a ∈ support w, ∃ v, Relation.ReflTransGen step w v ∧
      a ∈ support v ∧ ¬ 2 ≤ (support v).card := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro a ha
      by_cases hw : 2 ≤ (support w).card
      · rw [(expandSpec w hw).2.2] at ha
        obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp ha
        have hstep : step w v := ⟨hw, hv⟩
        obtain ⟨z, hz, haz, hzSmall⟩ := ih v (isEarlier hstep) a hav
        exact ⟨z, Relation.ReflTransGen.head hstep hz, haz, hzSmall⟩
      · exact ⟨w, Relation.ReflTransGen.refl, ha, hw⟩

  refine ⟨split, ?_, ?_⟩
  · intro w hw
    obtain ⟨hInt, hTwo⟩ := Finset.mem_filter.mp hw
    obtain ⟨wReach, wBig⟩ := Finset.mem_filter.mp hInt
    obtain ⟨r, hr, hp⟩ := (Finset.mem_filter.mp wReach).2
    exact ⟨wBig, hTwo, r, hr, pathSubset hp⟩
  · let leafCharges : Finset (A ⊕ ℕ) := (roots.biUnion support).image Sum.inl
    let internalCharges : Finset (A ⊕ ℕ) := internal.image Sum.inr
    have leafInPool : leafCharges ⊆ pool := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨v, hp, hav, hSmall⟩ := terminal r a har
      apply chargeInPool hr hp
      simp [charge, hSmall, hav]
    have internalInPool : internalCharges ⊆ pool := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨wReach, wBig⟩ := Finset.mem_filter.mp hw
      obtain ⟨r, hr, hp⟩ := (Finset.mem_filter.mp wReach).2
      apply chargeInPool hr hp
      simp [charge, wBig]
    have disjoint : Disjoint leafCharges internalCharges := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hx'
      cases hw
    have injectLeaf : (leafCharges).card = (roots.biUnion support).card :=
      Finset.card_image_of_injective _ Sum.inl_injective
    have injectInternal : internalCharges.card = internal.card :=
      Finset.card_image_of_injective _ Sum.inr_injective
    have hUnion := Finset.card_le_card (Finset.union_subset leafInPool internalInPool)
    rw [Finset.card_union_of_disjoint disjoint, injectLeaf, injectInternal] at hUnion
    have boundRoots : (roots.biUnion charge).card ≤ roots.card := by
      simpa using Finset.card_biUnion_le_card_mul roots charge 1 (fun w _ => chargeCard w)
    have boundEdges : (internal.biUnion edgeCharges).card ≤ internal.card + split.card := by
      apply Finset.card_biUnion_le.trans
      calc
        (∑ w ∈ internal, (edgeCharges w).card) ≤
            ∑ w ∈ internal, (1 + if (deps w).card = 2 then 1 else 0) := by
          apply Finset.sum_le_sum
          intro w hw
          have hCap := (expandSpec w (Finset.mem_filter.mp hw).2).2.1
          have hCharge := edgeChargeCard w
          split <;> omega
        _ = internal.card + split.card := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter]
          simp [split]
    have boundPool := (Finset.card_union_le (roots.biUnion charge) (internal.biUnion edgeCharges)).trans
      (Nat.add_le_add boundRoots boundEdges)
    change _ ≤ pool.card at hUnion
    change pool.card ≤ _ at boundPool
    omega

open scoped BigOperators

theorem aggregateForestBound {I V Edge : Type*} [DecidableEq V] [DecidableEq Edge]
    (bound : ℕ) (productive : Finset I) (center : I → V) (leafRoot : I → ℕ)
    (support : ℕ → Finset V) (deps : ℕ → Finset ℕ)
    (neighbors : V → Finset V) (edgeLabel : V → V → Edge)
    (edges : Finset Edge) (eligible : Finset ℕ)
    (rootsBounded : ∀ g ∈ productive, leafRoot g < bound)
    (rootsSupported : ∀ g ∈ productive, support (leafRoot g) ⊆ neighbors (center g))
    (expandSpec : ∀ w, 2 ≤ (support w).card →
      (∀ v ∈ deps w, v < w) ∧ (deps w).card ≤ 2 ∧ support w = (deps w).biUnion support)
    (eligibleSpec : ∀ w, 2 ≤ (support w).card → (deps w).card = 2 → w ∈ eligible)
    (commonBound : ∀ ⦃a b⦄, a ≠ b → (neighbors a ∩ neighbors b).card ≤ 1)
    (covers : ∀ e ∈ edges, ∃ g ∈ productive, ∃ v ∈ support (leafRoot g), e = edgeLabel (center g) v) :
    edges.card ≤ productive.card + eligible.card := by
  classical
  let centers := productive.image center
  let fiber (v : V) := productive.filter (fun g => center g = v)
  let roots (v : V) := (fiber v).image leafRoot
  let leaves (v : V) := (roots v).biUnion support
  have bounds (v : V) : ∀ r ∈ roots v, r < bound := by
    intro r hr
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hr
    exact rootsBounded _ (Finset.mem_filter.mp hg).1
  have ofRoot (v : V) {r : ℕ} (hr : r ∈ roots v) : support r ⊆ neighbors v := by
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hProd, hCenter⟩ := Finset.mem_filter.mp hg
    simpa [hCenter] using rootsSupported g hProd
  let picked (v : V) := Classical.choose
    (supportForestBound bound (roots v) deps support (bounds v) expandSpec)
  have spec (v : V) :
      (∀ w ∈ picked v, 2 ≤ (support w).card ∧ (deps w).card = 2 ∧
        ∃ r ∈ roots v, support w ⊆ support r) ∧
      (leaves v).card ≤ (roots v).card + (picked v).card :=
    Classical.choose_spec (supportForestBound bound (roots v) deps support (bounds v) expandSpec)
  have edgeSubset : edges ⊆ centers.biUnion (fun v => (leaves v).image (edgeLabel v)) := by
    intro e he
    obtain ⟨g, hg, v, hv, rfl⟩ := covers e he
    apply Finset.mem_biUnion.mpr
    refine ⟨center g, Finset.mem_image.mpr ⟨g, hg, rfl⟩, Finset.mem_image.mpr ⟨v, ?_, rfl⟩⟩
    exact Finset.mem_biUnion.mpr
      ⟨leafRoot g, Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, rfl⟩, rfl⟩, hv⟩
  have contained {v : V} {w : ℕ} (hw : w ∈ picked v) : support w ⊆ neighbors v := by
    obtain ⟨_, _, r, hr, hs⟩ := (spec v).1 w hw
    exact hs.trans (ofRoot v hr)
  have disjoint : (↑centers : Set V).PairwiseDisjoint picked := by
    intro a _ b _ hab
    change Disjoint (picked a) (picked b)
    rw [Finset.disjoint_left]
    intro w ha hb
    have hsubset : support w ⊆ neighbors a ∩ neighbors b :=
      Finset.subset_inter (contained ha) (contained hb)
    have hCard := (Finset.card_le_card hsubset).trans (commonBound hab)
    have hBig := ((spec a).1 w ha).1
    omega
  have unionEligible : centers.biUnion picked ⊆ eligible := by
    intro w hw
    obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hw
    exact eligibleSpec w ((spec v).1 w hv).1 ((spec v).1 w hv).2.1
  have sumPicked : (∑ v ∈ centers, (picked v).card) ≤ eligible.card := by
    rw [← Finset.card_biUnion disjoint]
    exact Finset.card_le_card unionEligible
  have sumFiber : (∑ v ∈ centers, (fiber v).card) = productive.card := by
    symm
    apply Finset.card_eq_sum_card_fiberwise
    intro g hg
    exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
  calc
    edges.card ≤ (centers.biUnion (fun v => (leaves v).image (edgeLabel v))).card :=
      Finset.card_le_card edgeSubset
    _ ≤ ∑ v ∈ centers, ((leaves v).image (edgeLabel v)).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ centers, ((fiber v).card + (picked v).card) := by
      apply Finset.sum_le_sum
      intro v _
      exact (Finset.card_image_le.trans (spec v).2).trans
        (Nat.add_le_add_right Finset.card_image_le _)
    _ ≤ productive.card + eligible.card := by
      rw [Finset.sum_add_distrib, sumFiber]
      exact Nat.add_le_add_left sumPicked productive.card


end ORForest

noncomputable def activeGates (C : Circuit) : Finset ℕ := by
  classical
  exact ((Finset.range C.gates.length).image (fun j => 26 + j)).filter (live C)

lemma mem_active_gates {C : Circuit} {w : ℕ} :
    w ∈ activeGates C ↔ (∃ j < C.gates.length, w = 26 + j) ∧ live C w := by
  classical
  simp [activeGates, eq_comm]

lemma active_card {C : Circuit} : (activeGates C).card ≤ C.size := by
  classical
  unfold activeGates Circuit.size
  exact (Finset.card_filter_le _ _).trans
    ((Finset.card_image_le).trans (by simp))

def atWire (C : Circuit) (w : ℕ) : Gate := gateAt C (w - 26)

def gateIsAnd (C : Circuit) (w : ℕ) : Bool :=
  match (atWire C w).op with
  | .and => true
  | _ => false

def operand (C : Circuit) (w : ℕ) (i : Bool) : ℕ :=
  (atWire C w).inputs.getD (if i then 1 else 0) 0

lemma wire_info {C : Circuit} (hB : binary C) {w : ℕ} (hw : w ∈ activeGates C) :
    ∃ j < C.gates.length, w = 26 + j ∧
      ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧
      (gateAt C j).inputs = [operand C w false, operand C w true] ∧
      operand C w false < w ∧ operand C w true < w := by
  obtain ⟨⟨j,hj,rfl⟩,_⟩ := mem_active_gates.mp hw
  obtain ⟨ops,a,b,hab,_,ha,hb⟩ := gate_shape hB hj
  have hfalse : operand C (26+j) false = a := by simp [operand, atWire, hab]
  have htrue : operand C (26+j) true = b := by simp [operand, atWire, hab]
  exact ⟨j,hj,rfl,ops,by rw [hfalse,htrue,hab],hfalse ▸ ha,htrue ▸ hb⟩

lemma tag_and {C : Circuit} {w j : ℕ} (hw : w = 26 + j) :
    gateIsAnd C w = true ↔ (gateAt C j).op = .and := by
  subst w
  simp only [gateIsAnd, atWire, Nat.add_sub_cancel_left]
  cases (gateAt C j).op <;> simp

lemma tag_or {C : Circuit} {w j : ℕ} (hw : w = 26 + j) (hop : (gateAt C j).op = .or) :
    gateIsAnd C w = false := by
  subst w
  simp [gateIsAnd, atWire, hop]

lemma op_reads {C : Circuit} (hB : binary C) {w : ℕ} (hw : w ∈ activeGates C) (i : Bool) :
    reads C (operand C w i) w := by
  obtain ⟨j,hj,hq,_,hop,_,_⟩ := wire_info hB hw
  refine ⟨j,hj,hq,?_⟩
  cases i <;> simp [hop]

lemma op_live {C : Circuit} (hB : binary C) {w : ℕ} (hw : w ∈ activeGates C) (i : Bool) :
    live C (operand C w i) :=
  ReflTransGen.head (op_reads hB hw i) (mem_active_gates.mp hw).2

lemma active_reader {C : Circuit} (hB : binary C) {w : ℕ}
    (h : live C w) (hout : w ≠ C.output) :
    ∃ g ∈ activeGates C, ∃ i, operand C g i = w := by
  rcases ReflTransGen.cases_head h with heq | ⟨g, hread, htail⟩
  · exact (hout heq).elim
  obtain ⟨j,hj,hg,hmem⟩ := hread
  have inG : g ∈ activeGates C := mem_active_gates.mpr ⟨⟨j,hj,hg⟩,htail⟩
  obtain ⟨k,_,hk,_,hab,_,_⟩ := wire_info hB inG
  have ek : k = j := by omega
  subst k
  rw [hab] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  exact ⟨g,inG,hmem.elim (fun e => ⟨false,e.symm⟩) (fun e => ⟨true,e.symm⟩)⟩

noncomputable def liveSupport (C : Circuit) (w : ℕ) : Finset Vertex := by
  classical
  exact if live C w then support C w else ∅

lemma support_at_live {C : Circuit} {w : ℕ} (hw : live C w) :
    liveSupport C w = support C w := by
  classical
  simp [liveSupport, hw]

lemma live_of_support {C : Circuit} {w : ℕ} (hw : (liveSupport C w).Nonempty) :
    live C w := by
  classical
  by_contra hh
  simp [liveSupport, hh] at hw

noncomputable def hasSupport (C : Circuit) (w : ℕ) : Bool :=
  decide ((liveSupport C w).Nonempty)

lemma derived_support {C : Circuit} (hB : binary C) (hF : computes C) (hC : clean C)
    (w : ℕ) (hw : w ∈ activeGates C) :
    hasSupport C w =
      (!gateIsAnd C w && (hasSupport C (operand C w false) || hasSupport C (operand C w true))) := by
  obtain ⟨j,hj,hq,ops,hab,ha,hb⟩ := wire_info hB hw
  have wLive := (mem_active_gates.mp hw).2
  have aLive := op_live hB hw false
  have bLive := op_live hB hw true
  rcases ops with hand | hor
  · have he : liveSupport C w = ∅ := by
      rw [support_at_live wLive, hq, and_support hF hC hj hand]
    simp [hasSupport, (tag_and hq).mpr hand, he]
  · have he : liveSupport C w = liveSupport C (operand C w false) ∪ liveSupport C (operand C w true) := by
      calc
        liveSupport C w = support C (26 + j) := by rw [support_at_live wLive, hq]
        _ = support C (operand C w false) ∪ support C (operand C w true) :=
          or_support hj hab (ha.trans_le hq.le) (hb.trans_le hq.le) hor
        _ = _ := by rw [support_at_live aLive, support_at_live bLive]
    simp [hasSupport, tag_or hq hor, he, Finset.union_nonempty]




noncomputable def productive (C : Circuit) : Finset ℕ :=
  ZeroSlots.classGates (activeGates C) (gateIsAnd C) (hasSupport C) (operand C) 0

noncomputable def twoPositiveOr (C : Circuit) : Finset ℕ :=
  ZeroSlots.classGates (activeGates C) (gateIsAnd C) (hasSupport C) (operand C) 1

lemma mem_productive {C : Circuit} {w : ℕ} :
    w ∈ productive C ↔ w ∈ activeGates C ∧ gateIsAnd C w = true ∧
      (liveSupport C (operand C w false)).Nonempty ∧
      (liveSupport C (operand C w true)).Nonempty := by
  have hf : hasSupport C (operand C w false) = true ↔
      (liveSupport C (operand C w false)).Nonempty := by simp [hasSupport]
  have ht : hasSupport C (operand C w true) = true ↔
      (liveSupport C (operand C w true)).Nonempty := by simp [hasSupport]
  rw [← hf, ← ht]
  cases hg : gateIsAnd C w <;>
    cases ha : hasSupport C (operand C w false) <;>
    cases hb : hasSupport C (operand C w true) <;>
    simp [productive, ZeroSlots.classGates, ZeroSlots.gateClass, hg, ha, hb]

lemma cross_productive {C : Circuit} (hB : binary C) (hF : computes C) (hC : clean C)
    {w : ℕ} (hw : w ∈ productive C) :
    ∀ u ∈ liveSupport C (operand C w false), ∀ v ∈ liveSupport C (operand C w true),
      adjacent u v := by
  obtain ⟨act, tag, _, _⟩ := mem_productive.mp hw
  obtain ⟨j,hj,hq,_,hab,_,_⟩ := wire_info hB act
  intro u hu v hv
  rw [support_at_live (op_live hB act false)] at hu
  rw [support_at_live (op_live hB act true)] at hv
  exact pair_sound (birth_true hB hF hC
    ⟨hj, (tag_and hq).mp tag, _, _, hab, Or.inl ⟨hu,hv⟩⟩)

def starShape (C : Circuit) (w : ℕ) (v : Vertex) (leaf : Bool) : Prop :=
  liveSupport C (operand C w (!leaf)) = {v} ∧
    liveSupport C (operand C w leaf) ⊆ neighbors v

lemma star_shape_exists {C : Circuit} (hB : binary C) (hF : computes C) (hC : clean C)
    {w : ℕ} (hw : w ∈ productive C) :
    ∃ v leaf, starShape C w v leaf := by
  obtain ⟨_,_,ha,hb⟩ := mem_productive.mp hw
  rcases rectangle_star _ _ ha hb (cross_productive hB hF hC hw) with ⟨c,hc,hn⟩ | ⟨c,hc,hn⟩
  · exact ⟨c,true,hc,hn⟩
  · exact ⟨c,false,hc,hn⟩

lemma live_birth_productive {C : Circuit} (hB : binary C) {j : ℕ} {u v : Vertex}
    (hb : birth C j u v) (hl : live C (26+j)) :
    26+j ∈ productive C := by
  obtain ⟨hj, hop, a, b, hab, cross⟩ := hb
  have active : 26+j ∈ activeGates C := mem_active_gates.mpr ⟨⟨j,hj,rfl⟩,hl⟩
  have eqA : operand C (26+j) false = a := by simp [operand, atWire, hab]
  have eqB : operand C (26+j) true = b := by simp [operand, atWire, hab]
  refine mem_productive.mpr ⟨active, (tag_and rfl).mpr hop, ?_, ?_⟩
  · rw [support_at_live (op_live hB active false), eqA]
    exact cross.elim (fun e => ⟨u,e.1⟩) (fun e => ⟨v,e.1⟩)
  · rw [support_at_live (op_live hB active true), eqB]
    exact cross.elim (fun e => ⟨v,e.2⟩) (fun e => ⟨u,e.2⟩)



def sideVertex (u : Vertex) : Sum Point Line :=
  if h : u.val < 13 then .inl ⟨u.val, h⟩
  else .inr ⟨u.val - 13, by have := u.isLt; omega⟩

lemma side_point (p : Point) : sideVertex (point p) = .inl p := by
  unfold sideVertex point
  have h : (Fin.castAdd 13 p).val < 13 := p.isLt
  rw [dif_pos h]
  rfl

lemma side_line (l : Line) : sideVertex (line l) = .inr l := by
  unfold sideVertex line
  have h : ¬ (Fin.natAdd 13 l).val < 13 := by simp
  rw [dif_neg h]
  congr 1
  apply Fin.ext
  simp

def edgeLabel (u v : Vertex) : Point × Line :=
  match sideVertex u, sideVertex v with
  | .inl p, .inr l => (p,l)
  | .inr l, .inl p => (p,l)
  | _, _ => (0,0)

lemma labeled_edge_in_star {u v : Vertex} (hv : v ∈ neighbors u) :
    edgeLabel u v ∈ pg3Star (sideVertex u) := by
  have hadj := (neighbor_iff u v).mp hv
  rcases vertex_cases u with ⟨p,rfl⟩ | ⟨l,rfl⟩ <;>
    rcases vertex_cases v with ⟨q,rfl⟩ | ⟨m,rfl⟩
  · exact (not_adjacent_points p q hadj).elim
  · have hmem : (p,m) ∈ pg3Edges := (pg3MemEdges p m).mpr ((adjacent_point_line p m).mp hadj)
    simp [edgeLabel, side_point, side_line, pg3Star, hmem]
  · have hmem : (q,l) ∈ pg3Edges :=
      (pg3MemEdges q l).mpr ((adjacent_point_line q l).mp ((adjacent_symm _ _).mp hadj))
    simp [edgeLabel, side_point, side_line, pg3Star, hmem]
  · exact (not_adjacent_lines l m hadj).elim

lemma birth_labels {C : Circuit} (hB : binary C) {j : ℕ} {p : Point} {l : Line}
    (hb : birth C j (point p) (line l)) (hl : live C (26+j))
    {center : Vertex} {leaf : Bool} (hstar : starShape C (26+j) center leaf) :
    ∃ v ∈ liveSupport C (operand C (26+j) leaf), (p,l) = edgeLabel center v := by
  obtain ⟨hj,hop,a,b,hab,hcross⟩ := hb
  have ha : operand C (26+j) false = a := by simp [operand, atWire, hab]
  have hc : operand C (26+j) true = b := by simp [operand, atWire, hab]
  have hactive : 26+j ∈ activeGates C := mem_active_gates.mpr ⟨⟨j,hj,rfl⟩,hl⟩
  rw [← ha, ← hc, ← support_at_live (op_live hB hactive false),
    ← support_at_live (op_live hB hactive true)] at hcross
  have hs := hstar.1
  cases leaf <;> simp only [Bool.not_false, Bool.not_true] at hs ⊢
  · rcases hcross with ⟨hp,hq⟩ | ⟨hq,hp⟩
    · rw [hs, Finset.mem_singleton] at hq
      exact ⟨point p,hp,by simp [← hq, edgeLabel, side_point, side_line]⟩
    · rw [hs, Finset.mem_singleton] at hp
      exact ⟨line l,hq,by simp [← hp, edgeLabel, side_point, side_line]⟩
  · rcases hcross with ⟨hp,hq⟩ | ⟨hq,hp⟩
    · rw [hs, Finset.mem_singleton] at hp
      exact ⟨line l,hq,by simp [← hp, edgeLabel, side_point, side_line]⟩
    · rw [hs, Finset.mem_singleton] at hq
      exact ⟨point p,hp,by simp [← hq, edgeLabel, side_point, side_line]⟩



noncomputable def positiveDeps (C : Circuit) (w : ℕ) : Finset ℕ :=
  ({operand C w false, operand C w true} : Finset ℕ).filter
    (fun a => hasSupport C a = true)

lemma multi_support_gate {C : Circuit} {w : ℕ}
    (h : 2 ≤ (liveSupport C w).card) : w ∈ activeGates C := by
  have hl := live_of_support (Finset.card_pos.mp (show 0 < (liveSupport C w).card by omega))
  have hs := support_at_live hl
  by_cases hin : w < 26
  · have hsu : support C w = {⟨w,hin⟩} := by
      ext u
      rw [mem_support, input_value hin, Finset.mem_singleton]
      simp [single, eq_comm]
    simp [hs, hsu] at h
  · by_cases hge : 26 + C.gates.length ≤ w
    · have hsu : support C w = ∅ := by
        ext u
        simp [mem_support, beyond_value hge]
      simp [hs, hsu] at h
    · exact mem_active_gates.mpr ⟨⟨w - 26, by omega, by omega⟩,hl⟩

lemma expand_support {C : Circuit} (hB : binary C) (hF : computes C) (hC : clean C)
    (w : ℕ) (h : 2 ≤ (liveSupport C w).card) :
    (∀ v ∈ positiveDeps C w, v < w) ∧ (positiveDeps C w).card ≤ 2 ∧
      liveSupport C w = (positiveDeps C w).biUnion (liveSupport C) := by
  have hw := multi_support_gate h
  obtain ⟨j,hj,hq,ops,hab,ha,hb⟩ := wire_info hB hw
  have hLive := (mem_active_gates.mp hw).2
  have hor : (gateAt C j).op = .or := by
    rcases ops with hand | hor
    · rw [support_at_live hLive, hq, and_support hF hC hj hand] at h
      simp at h
    · exact hor
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have hz := (Finset.mem_filter.mp hv).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    exact hz.elim (fun e => e.symm ▸ ha) (fun e => e.symm ▸ hb)
  · unfold positiveDeps
    exact (Finset.card_filter_le _ _).trans (Finset.card_insert_le _ _)
  · have hUnion : liveSupport C w =
        liveSupport C (operand C w false) ∪ liveSupport C (operand C w true) := by
      calc
        liveSupport C w = support C (26 + j) := by rw [support_at_live hLive, hq]
        _ = support C (operand C w false) ∪ support C (operand C w true) :=
          or_support hj hab (ha.trans_le hq.le) (hb.trans_le hq.le) hor
        _ = _ := by rw [support_at_live (op_live hB hw false), support_at_live (op_live hB hw true)]
    rw [hUnion]
    ext u
    simp only [positiveDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton, hasSupport, decide_eq_true_eq]
    constructor
    · rintro (hA | hB')
      · exact ⟨_,⟨Or.inl rfl,⟨u,hA⟩⟩,hA⟩
      · exact ⟨_,⟨Or.inr rfl,⟨u,hB'⟩⟩,hB'⟩
    · rintro ⟨v,⟨hv,_⟩,hU⟩
      exact hv.elim (fun e => Or.inl (e ▸ hU)) (fun e => Or.inr (e ▸ hU))

lemma eligible_support {C : Circuit} (hB : binary C) (hF : computes C) (hC : clean C)
    (w : ℕ) (h : 2 ≤ (liveSupport C w).card) (h2 : (positiveDeps C w).card = 2) :
    w ∈ twoPositiveOr C := by
  have hw := multi_support_gate h
  have htag : gateIsAnd C w = false := by
    have hh := derived_support hB hF hC w hw
    have ht : hasSupport C w = true := by
      simp [hasSupport, Finset.card_pos.mp (show 0 < (liveSupport C w).card by omega)]
    rw [ht] at hh
    cases e : gateIsAnd C w <;> simp_all
  have both (i : Bool) : hasSupport C (operand C w i) = true := by
    by_contra hh
    have sub : positiveDeps C w ⊆ {operand C w (!i)} := by
      intro v hv
      obtain ⟨hmem,hvPos⟩ := Finset.mem_filter.mp hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rw [Finset.mem_singleton]
      cases i
      · rcases hmem with hA | hB
        · exact (hh (hA ▸ hvPos)).elim
        · exact hB
      · rcases hmem with hA | hB
        · exact hA
        · exact (hh (hB ▸ hvPos)).elim
    have card := Finset.card_le_card sub
    rw [h2, Finset.card_singleton] at card
    omega
  simp [twoPositiveOr, ZeroSlots.classGates, ZeroSlots.gateClass, hw, htag, both false, both true]



noncomputable def countedStar (C : Circuit) (center : ℕ → Vertex) (leaf : ℕ → Bool) (w : ℕ) :
    Finset (Point × Line) :=
  (liveSupport C (operand C w (leaf w))).image (edgeLabel (center w))

structure TightCircuit (C : Circuit) where
  center : ℕ → Vertex
  leaf : ℕ → Bool
  shape : ∀ w ∈ productive C, starShape C w (center w) (leaf w)
  full : ∀ w ∈ productive C, countedStar C center leaf w = pg3Star (sideVertex (center w))
  unique : ∀ w ∈ productive C, ∀ v ∈ productive C,
    sideVertex (center w) = sideVertex (center v) → w = v
  uniform : (∀ w ∈ productive C, ∃ p, sideVertex (center w) = .inl p) ∨
    (∀ w ∈ productive C, ∃ l, sideVertex (center w) = .inr l)
  covers : (productive C).biUnion (countedStar C center leaf) = pg3Edges
  bothOrs : (twoPositiveOr C).card = 39
  allCount : (activeGates C).card = 64
  balanced : ∀ w ∈ activeGates C, gateIsAnd C w = true →
    hasSupport C (operand C w false) = hasSupport C (operand C w true)
  uniqueRead : Set.InjOn (ZeroSlots.source (operand C))
    ↑(ZeroSlots.slots (activeGates C) (hasSupport C) (operand C))

lemma tight_circuit {C : Circuit} (hB : binary C) (hF : computes C) (hC : clean C)
    (small : C.size ≤ 64) : Nonempty (TightCircuit C) := by
  classical
  have shapes : ∀ w, ∃ c : Vertex, ∃ leaf : Bool, w ∈ productive C → starShape C w c leaf := by
    intro w
    by_cases hw : w ∈ productive C
    · obtain ⟨c,leaf,hs⟩ := star_shape_exists hB hF hC hw
      exact ⟨c,leaf,fun _ => hs⟩
    · exact ⟨0,false,fun h => (hw h).elim⟩
  choose center leaf shape using shapes
  have subsets : ∀ w ∈ productive C, countedStar C center leaf w ⊆
      pg3Star (sideVertex (center w)) := by
    intro w hw e he
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
    exact labeled_edge_in_star ((shape w hw).2 hv)
  have edgesCovered : ∀ e ∈ pg3Edges, ∃ w ∈ productive C,
      ∃ v ∈ liveSupport C (operand C w (leaf w)), e = edgeLabel (center w) v := by
    rintro ⟨p,l⟩ he
    have hi := (pg3MemEdges p l).mp he
    obtain ⟨j,hj,hl⟩ := every_incidence_has_birth hB hF p l hi
    have wProd := live_birth_productive hB hj hl
    obtain ⟨v,hv,heq⟩ := birth_labels hB hj hl (shape (26+j) wProd)
    exact ⟨26+j,wProd,v,hv,heq⟩
  have allEdges : (productive C).biUnion (countedStar C center leaf) = pg3Edges := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨w,hw,he⟩ := Finset.mem_biUnion.mp he
      have hs := subsets w hw he
      cases h : sideVertex (center w) <;>
        rw [h, pg3Star] at hs <;> exact (Finset.mem_filter.mp hs).1
    · intro e he
      obtain ⟨w,hw,v,hv,heq⟩ := edgesCovered e he
      exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_image.mpr ⟨v,hv,heq.symm⟩⟩
  have enoughAND : 52 ≤ 4 * (productive C).card := by
    rw [← pg3EdgesCard, ← allEdges]
    calc
      _ ≤ ∑ w ∈ productive C, (countedStar C center leaf w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ productive C, (4 : ℕ) := Finset.sum_le_sum (fun w hw => by
        simpa [pg3StarCard] using Finset.card_le_card (subsets w hw))
      _ = _ := by simp [Nat.mul_comm]
  have enoughLeaf : 52 ≤ (productive C).card + (twoPositiveOr C).card := by
    rw [← pg3EdgesCard]
    apply ORForest.aggregateForestBound (26 + C.gates.length) (productive C) center
      (fun w => operand C w (leaf w)) (liveSupport C) (positiveDeps C) neighbors edgeLabel
      pg3Edges (twoPositiveOr C)
    · intro w hw
      have hwA := (mem_productive.mp hw).1
      obtain ⟨j,hj,hq,_,_,ha,hb⟩ := wire_info hB hwA
      cases leaf w <;> omega
    · exact fun w hw => (shape w hw).2
    · exact expand_support hB hF hC
    · exact eligible_support hB hF hC
    · exact fun {_ _} hn => common_at_most_one _ _ hn
    · exact edgesCovered
  obtain ⟨nP,nB,nAll,balanced,uniqueReads⟩ := ZeroSlots.tight_live_slots
    (activeGates C) (gateIsAnd C) (hasSupport C) (operand C) C.output
    (derived_support hB hF hC) (fun w hw _ hout => active_reader hB (mem_active_gates.mp hw).2 hout)
    (active_card.trans small) enoughAND enoughLeaf
  obtain ⟨full,unique,uniform⟩ := pg3FullStarsOneSide (productive C)
    (countedStar C center leaf) (fun w => sideVertex (center w)) nP allEdges subsets
  exact ⟨⟨center,leaf,shape,full,unique,uniform,allEdges,nB,nAll,balanced,uniqueReads⟩⟩



namespace Token

open Relation

def pureInputSide (isCenter : ℕ → Prop) (s : Finset ℕ) : Prop :=
  (∃ c, isCenter c ∧ s = {c}) ∨ (∀ v ∈ s, ¬ isCenter v)

lemma pureInputSide_subset {isCenter : ℕ → Prop} {small large : Finset ℕ}
    (pure : pureInputSide isCenter large) (sub : small ⊆ large) (nonempty : small.Nonempty) :
    pureInputSide isCenter small := by
  rcases pure with ⟨c, hc, rfl⟩ | pureLeaf
  · obtain ⟨u, hu⟩ := nonempty
    have huc := Finset.mem_singleton.mp (sub hu)
    subst u
    exact Or.inl ⟨c, hc, Finset.Subset.antisymm sub (Finset.singleton_subset_iff.mpr hu)⟩
  · exact Or.inr fun u hu => pureLeaf u (sub hu)

lemma pure_support_on_path {reads : ℕ → ℕ → Prop} {isCenter : ℕ → Prop}
    (support : ℕ → Finset ℕ) {out : ℕ}
    (zeroOut : support out = ∅)
    (preserve : ∀ {a b}, reads a b → (support b).Nonempty → support a ⊆ support b)
    (intoZero : ∀ {a b}, reads a b → (support a).Nonempty → support b = ∅ →
      pureInputSide isCenter (support a))
    {w : ℕ} (reaches : ReflTransGen reads w out) (nonempty : (support w).Nonempty) :
    pureInputSide isCenter (support w) := by
  induction reaches using ReflTransGen.head_induction_on with
  | refl => simp [zeroOut] at nonempty
  | @head a b step path ih =>
    by_cases hb : (support b).Nonempty
    · exact pureInputSide_subset (ih hb) (preserve step hb) nonempty
    · exact intoZero step nonempty (Finset.not_nonempty_iff_eq_empty.mp hb)

noncomputable def tagOfSupport (isCenter : ℕ → Prop) (s : Finset ℕ) :
    Option (Sum ℕ Unit) := by
  classical
  exact if hs : ∃ c ∈ s, isCenter c then some (.inl (Classical.choose hs))
    else if s.Nonempty then some (.inr ()) else none

lemma tagOfSupport_empty (isCenter : ℕ → Prop) : tagOfSupport isCenter ∅ = none := by
  unfold tagOfSupport
  simp

lemma tagOfSupport_none_iff {isCenter : ℕ → Prop} {s : Finset ℕ} :
    tagOfSupport isCenter s = none ↔ s = ∅ := by
  constructor
  · intro h
    unfold tagOfSupport at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · exact Finset.not_nonempty_iff_eq_empty.mp ‹¬s.Nonempty›
  · rintro rfl
    exact tagOfSupport_empty isCenter

lemma tagOfSupport_center {isCenter : ℕ → Prop} {c : ℕ} (hc : isCenter c) :
    tagOfSupport isCenter {c} = some (.inl c) := by
  unfold tagOfSupport
  have hs : ∃ u ∈ ({c} : Finset ℕ), isCenter u := ⟨c, by simp, hc⟩
  rw [dif_pos hs]
  have choose := (Classical.choose_spec hs).1
  rw [Finset.mem_singleton.mp choose]

lemma tagOfSupport_leaf {isCenter : ℕ → Prop} {s : Finset ℕ}
    (nonempty : s.Nonempty) (leaf : ∀ u ∈ s, ¬ isCenter u) :
    tagOfSupport isCenter s = some (.inr ()) := by
  unfold tagOfSupport
  rw [dif_neg (by rintro ⟨u, hu, hc⟩; exact leaf u hu hc), if_pos nonempty]

lemma tagOfSupport_eq_of_subset {isCenter : ℕ → Prop} {small large : Finset ℕ}
    (pure : pureInputSide isCenter large) (sub : small ⊆ large) (nonempty : small.Nonempty) :
    tagOfSupport isCenter small = tagOfSupport isCenter large := by
  rcases pure with ⟨c, hc, rfl⟩ | leaf
  · obtain ⟨u, hu⟩ := nonempty
    have huc := Finset.mem_singleton.mp (sub hu)
    subst u
    rw [show small = {c} from Finset.Subset.antisymm sub (Finset.singleton_subset_iff.mpr hu)]
  · exact (tagOfSupport_leaf nonempty (fun u hu => leaf u (sub hu))).trans
      (tagOfSupport_leaf (nonempty.mono sub) leaf).symm

lemma tagOfSupport_center_support {isCenter : ℕ → Prop} {s : Finset ℕ} {c : ℕ}
    (pure : pureInputSide isCenter s) (tag : tagOfSupport isCenter s = some (.inl c)) :
    isCenter c ∧ s = {c} := by
  have nz : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, tagOfSupport_empty] at tag
    contradiction
  rcases pure with ⟨d, hC, rfl⟩ | leaf
  · rw [tagOfSupport_center hC] at tag
    have eq : d = c := by simpa using tag
    subst d
    exact ⟨hC, rfl⟩
  · rw [tagOfSupport_leaf nz leaf] at tag
    cases tag

end Token

namespace Token

open Relation

abbrev Tag := Sum ℕ Unit

def sameLabelRead (reads : ℕ → ℕ → Prop) (label : ℕ → Option Tag)
    (t : Tag) (u v : ℕ) : Prop :=
  reads u v ∧ label u = some t ∧ label v = some t

def throughPositive (reads : ℕ → ℕ → Prop) (label : ℕ → Option Tag)
    (t : Tag) (u v : ℕ) : Prop :=
  ∃ w, reads u w ∧ label w = some t ∧
    ReflTransGen (sameLabelRead reads label t) w v

def transfers (reads : ℕ → ℕ → Prop) (label : ℕ → Option Tag)
    (trueEmpty : ℕ → Prop) (centerGate : ℕ → ℕ → Prop) (u v : ℕ) : Prop :=
  trueEmpty u ∧ trueEmpty v ∧ (reads u v ∨
    ∃ c w, centerGate c v ∧ reads w v ∧ throughPositive reads label (.inl c) u w)

lemma followsForward
    {R : ℕ → ℕ → Prop} (forward : ∀ {a b}, R a b → a < b)
    {a b : ℕ} (path : ReflTransGen R a b) : a ≤ b := by
  induction path with
  | refl => rfl
  | tail _ edge ih => exact ih.trans (forward edge).le

lemma throughPositiveEarlier
    {reads : ℕ → ℕ → Prop} {label : ℕ → Option Tag}
    (forward : ∀ {a b}, reads a b → a < b)
    {t : Tag} {u v : ℕ} (h : throughPositive reads label t u v) :
    u < v := by
  obtain ⟨w, read, _, path⟩ := h
  exact (forward read).trans_le (followsForward (fun h => forward h.1) path)

lemma transportsDerivative {reads : ℕ → ℕ → Prop} {label : ℕ → Option Tag}
    {deriv : ℕ → Bool}
    (propagate : ∀ {u v}, reads u v → label v ≠ none → deriv u = true → deriv v = true)
    {t : Tag} {u v : ℕ} (h : throughPositive reads label t u v) (start : deriv u = true) :
    deriv v = true := by
  obtain ⟨w, initial, lab, path⟩ := h
  have hw := propagate initial (by rw [lab]; simp) start
  induction path with
  | refl => exact hw
  | tail _ edge ih => exact propagate edge.1 (by rw [edge.2.2]; simp) ih

lemma transfersForward {reads : ℕ → ℕ → Prop} {label : ℕ → Option Tag}
    {trueEmpty : ℕ → Prop} {centerGate : ℕ → ℕ → Prop}
    (forward : ∀ {a b}, reads a b → a < b)
    {a b : ℕ} (h : transfers reads label trueEmpty centerGate a b) : a < b := by
  rcases h.2.2 with h | ⟨c, w, _, last, path⟩
  · exact forward h
  · exact (throughPositiveEarlier forward path).trans (forward last)

lemma transfersRightUnique {reads : ℕ → ℕ → Prop} {label : ℕ → Option Tag}
    {trueEmpty : ℕ → Prop} {centerGate : ℕ → ℕ → Prop}
    (empty : ∀ {u}, trueEmpty u → label u = none)
    (readUnique : ∀ {u v w}, trueEmpty u → reads u v → reads u w → v = w)
    (centerUnique : ∀ {c v w}, centerGate c v → centerGate c w → v = w) :
    Relator.RightUnique (transfers reads label trueEmpty centerGate) := by
  intro u v w hv hw
  rcases hv.2.2 with hold | ⟨c, a, hc, _, r, hr, tc, _⟩
  · rcases hw.2.2 with hnew | ⟨d, b, hd, _, s, hs, td, _⟩
    · exact readUnique hv.1 hold hnew
    · have eq := readUnique hv.1 hold hs
      rw [← eq, empty hv.2.1] at td
      contradiction
  · rcases hw.2.2 with hnew | ⟨d, b, hd, _, s, hs, td, _⟩
    · have eq := readUnique hw.1 hnew hr
      rw [← eq, empty hw.2.1] at tc
      contradiction
    · have eq := readUnique hv.1 hr hs
      rw [← eq, tc] at td
      have hcd : c = d := by simpa only [Option.some.injEq, Sum.inl.injEq] using td
      subst d
      exact centerUnique hc hd

lemma leafInjectionTerminal {reads : ℕ → ℕ → Prop} {label : ℕ → Option Tag}
    {trueEmpty : ℕ → Prop} {centerGate : ℕ → ℕ → Prop}
    (empty : ∀ {u}, trueEmpty u → label u = none)
    (readUnique : ∀ {u v w}, trueEmpty u → reads u v → reads u w → v = w)
    {u arm v : ℕ} (path : throughPositive reads label (.inr ()) u arm)
    (edge : transfers reads label trueEmpty centerGate u v) : False := by
  obtain ⟨s, hs, ts, _⟩ := path
  rcases edge.2.2 with hv | ⟨c, w, hc, _, r, hr, tc, _⟩
  · have eq := readUnique edge.1 hv hs
    rw [← eq, empty edge.2.1] at ts
    contradiction
  · have eq := readUnique edge.1 hr hs
    rw [← eq, tc] at ts
    cases ts

def trueEmptyWire (label : ℕ → Option Tag) (truth : ℕ → Prop) (w : ℕ) : Prop :=
  truth w ∧ label w = none

def singletonSignal (x : ℕ) (singleY : ℕ → Bool) (t : Tag) (w : ℕ) : Prop :=
  match t with
  | .inl c => c = x
  | .inr _ => singleY w = true

lemma positiveOrigin {reads : ℕ → ℕ → Prop} {label : ℕ → Option Tag}
    {truth : ℕ → Prop} {good : Tag → ℕ → Prop}
    (forward : ∀ {a b}, reads a b → a < b)
    (goodStep : ∀ {t a b}, sameLabelRead reads label t a b → good t a → good t b)
    (baseOrStep : ∀ {t w}, truth w → label w = some t → good t w ∨
      ∃ u, reads u w ∧ truth u ∧ (label u = none ∨ label u = some t))
    (t : Tag) (w : ℕ) (ht : truth w) (hlab : label w = some t) :
    good t w ∨ ∃ u, trueEmptyWire label truth u ∧ throughPositive reads label t u w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases baseOrStep ht hlab with h | ⟨u, read, tru, zero | pos⟩
    · exact Or.inl h
    · exact Or.inr ⟨u, ⟨tru, zero⟩, w, read, hlab, .refl⟩
    · have step : sameLabelRead reads label t u w := ⟨read, pos, hlab⟩
      rcases ih u (forward read) tru pos with goodU | ⟨v, hv, a, va, hlabel, path⟩
      · exact Or.inl (goodStep step goodU)
      · exact Or.inr ⟨v, hv, a, va, hlabel, path.tail step⟩

lemma competingPredecessors {R : ℕ → ℕ → Prop} {source a b w : ℕ}
    (unique : Relator.RightUnique R) (forward : ∀ {u v}, R u v → u < v)
    (pathA : ReflTransGen R source a) (pathB : ReflTransGen R source b)
    (aw : R a w) (bw : R b w) : a = b := by
  rcases ReflTransGen.total_of_right_unique unique pathA pathB with ab | ba
  · rcases ab.cases_head with h | ⟨u, au, ub⟩
    · exact h
    · have h := followsForward forward ub
      rw [unique au aw] at h
      exact (Nat.not_le_of_lt (forward bw) h).elim
  · rcases ba.cases_head with h | ⟨u, bu, ua⟩
    · exact h.symm
    · have h := followsForward forward ua
      rw [unique bu bw] at h
      exact (Nat.not_le_of_lt (forward aw) h).elim

lemma earlierPathHasSuccessor {R : ℕ → ℕ → Prop} {source a b : ℕ}
    (unique : Relator.RightUnique R) (forward : ∀ {u v}, R u v → u < v)
    (pathA : ReflTransGen R source a) (pathB : ReflTransGen R source b)
    (earlier : a < b) : ∃ next, R a next := by
  rcases ReflTransGen.total_of_right_unique unique pathA pathB with ab | ba
  · rcases ab.cases_head with h | ⟨u, au, _⟩
    · exact (Nat.ne_of_lt earlier h).elim
    · exact ⟨u, au⟩
  · exact (Nat.not_le_of_lt earlier (followsForward forward ba)).elim

def zeroStage (reads : ℕ → ℕ → Prop) (label : ℕ → Option Tag) (truth : ℕ → Prop)
    (centerGate : ℕ → ℕ → Prop) (singleY trace : ℕ → Bool) (w : ℕ) : Prop :=
  (∃ u, trueEmptyWire label truth u ∧ reads u w ∧ (trace u = true → trace w = true)) ∨
  (∃ a b, trueEmptyWire label truth a ∧ trueEmptyWire label truth b ∧
    a ≠ b ∧ reads a w ∧ reads b w) ∨
  (∃ c a b, centerGate c w ∧ reads a w ∧ reads b w ∧ truth a ∧ truth b ∧
    label a = some (.inl c) ∧ label b = some (.inr ()) ∧
    (trace a = true → singleY b = true → trace w = true))

theorem traceOfTightCenterSide (reads : ℕ → ℕ → Prop) (label : ℕ → Option Tag)
    (truth : ℕ → Prop) (centerGate : ℕ → ℕ → Prop) (singleY trace : ℕ → Bool)
    (x birth out : ℕ)
    (topological : ∀ {a b}, reads a b → a < b)
    (readUnique : ∀ {u v w}, trueEmptyWire label truth u → reads u v → reads u w → v = w)
    (centerUnique : ∀ {c v w}, centerGate c v → centerGate c w → v = w)
    (origin : centerGate x birth) (birthTrace : trace birth = true)
    (outTrue : trueEmptyWire label truth out)
    (singletonStep : ∀ {a b}, reads a b → label b ≠ none → singleY a = true → singleY b = true)
    (traceStep : ∀ {a b}, reads a b → label b ≠ none → trace a = true → trace b = true)
    (mixed : ∀ {t w}, truth w → label w = some t → singletonSignal x singleY t w ∨
      ∃ u, reads u w ∧ truth u ∧ (label u = none ∨ label u = some t))
    (shape : ∀ w, trueEmptyWire label truth w → w ≠ birth →
      zeroStage reads label truth centerGate singleY trace w) :
    trace out = true := by
  let E := trueEmptyWire label truth
  let R := transfers reads label E centerGate
  have forward : ∀ {a b}, R a b → a < b := transfersForward topological
  have unique : Relator.RightUnique R :=
    transfersRightUnique (fun h => h.2) readUnique centerUnique
  have ht (t : Tag) (w : ℕ) (hw : truth w) (hTag : label w = some t) :
      singletonSignal x singleY t w ∨ ∃ u, E u ∧ throughPositive reads label t u w :=
    positiveOrigin (reads := reads) (label := label) (truth := truth)
      (good := singletonSignal x singleY) topological (fun {s a b} h hs => by
      cases s with
      | inl c => exact hs
      | inr btag =>
        exact singletonStep h.1 (by rw [h.2.2]; simp) hs) mixed t w hw hTag
  have centerOrigin {w c a : ℕ} (hw : w ≠ birth) (hc : centerGate c w)
      (hv : truth a) (hl : label a = some (.inl c)) :
      ∃ u, E u ∧ throughPositive reads label (.inl c) u a := by
    rcases ht (.inl c) a hv hl with h | found
    · change c = x at h
      subst c
      exact (hw (centerUnique hc origin)).elim
    · exact found
  have prev (w : ℕ) (hw : E w) (hne : w ≠ birth) : ∃ u, E u ∧ R u w := by
    rcases shape w hw hne with ⟨u, hu, read, _⟩ | ⟨a, _, ha, _, _, aw, _⟩ |
        ⟨c, a, _, hc, read, _, ta, _, lab, _, _⟩
    · exact ⟨u, hu, hu, hw, Or.inl read⟩
    · exact ⟨a, ha, ha, hw, Or.inl aw⟩
    · obtain ⟨u, hu, route⟩ := centerOrigin hne hc ta lab
      exact ⟨u, hu, hu, hw, Or.inr ⟨c, a, hc, read, route⟩⟩
  have allPaths (w : ℕ) (h : E w) : ReflTransGen R birth w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw : w = birth
      · subst w
        exact .refl
      · obtain ⟨u, hu, edge⟩ := prev w h hw
        exact (ih u (forward edge) hu).tail edge
  have deriv (w : ℕ) (h : E w) : trace w = true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw : w = birth
      · simpa [hw] using birthTrace
      · rcases shape w h hw with ⟨u, hu, uw, step⟩ | ⟨a, b, ha, hb, hab, aw, bw⟩ |
            ⟨c, a, b, hc, aw, bw, ha, hb, ca, lb, rule⟩
        · exact step (ih u (topological uw) hu)
        · exact (hab (competingPredecessors unique forward (allPaths a ha) (allPaths b hb)
            ⟨ha, h, Or.inl aw⟩ ⟨hb, h, Or.inl bw⟩)).elim
        · obtain ⟨u, hu, reach⟩ := centerOrigin hw hc ha ca
          have huEarly := (throughPositiveEarlier topological reach).trans (topological aw)
          have huTrace := ih u huEarly hu
          apply rule (transportsDerivative (reads := reads) (label := label)
            (deriv := trace) traceStep reach huTrace)
          rcases ht (.inr ()) b hb lb with leafSingle | ⟨v, hv, leafPath⟩
          · exact leafSingle
          · have hvEarly := (throughPositiveEarlier topological leafPath).trans (topological bw)
            obtain ⟨next, edge⟩ := earlierPathHasSuccessor unique forward
              (allPaths v hv) (allPaths w h) hvEarly
            exact (leafInjectionTerminal (reads := reads) (label := label)
              (trueEmpty := E) (centerGate := centerGate) (fun h => h.2) readUnique leafPath edge).elim
  exact deriv out outTrue

end Token



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Relation

namespace TraceBridge

def activeReads (C : Circuit) (a b : ℕ) : Prop := reads C a b ∧ live C b

lemma active_path {C : Circuit} {w : ℕ} (h : live C w) :
    ReflTransGen (activeReads C) w C.output := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head read path ih => exact ih.head ⟨read, path⟩

def tracks (C : Circuit) (base : Vertex) (i : ℕ) (trace : ℕ → Bool) : Prop :=
  (∀ w < 26, trace w = decide (w = i)) ∧
  ∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] →
    (g.op = .and → trace (26 + j) =
      ((value C (single base) a && trace b) || (trace a && value C (single base) b))) ∧
    (g.op = .or → trace (26 + j) = (trace a || trace b))

lemma tracks_gate {C : Circuit} {base : Vertex} {i : ℕ} {trace : ℕ → Bool}
    (h : tracks C base i trace) {j a b : ℕ}
    (hj : j < C.gates.length) (args : (gateAt C j).inputs = [a,b]) :
    ((gateAt C j).op = .and → trace (26 + j) =
      ((value C (single base) a && trace b) || (trace a && value C (single base) b))) ∧
    ((gateAt C j).op = .or → trace (26 + j) = (trace a || trace b)) := by
  apply h.2 j (gateAt C j) a b _ args
  rw [gateAt_eq hj]
  exact List.getElem?_eq_getElem hj

lemma single_input_support (C : Circuit) {w : ℕ} (hw : w < 26) :
    support C w = {⟨w, hw⟩} := by
  ext x
  rw [mem_support, input_value hw]
  simp [single, eq_comm]

lemma trace_of_center_singleton {C : Circuit} {base center : Vertex} {trace : ℕ → Bool}
    (sh : binary C) (hExact : computes C) (hClean : clean C)
    (tr : tracks C base center.val trace) (w : ℕ) (present : center ∈ support C w) :
    trace w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < 26
    · have eq : center.val = w := by
        rw [single_input_support C hin] at present
        exact congrArg Fin.val (Finset.mem_singleton.mp present)
      rw [tr.1 w hin, eq]
      simp
    · by_cases hge : 26 + C.gates.length ≤ w
      · have ht := (mem_support C w center).mp present
        rw [beyond_value hge] at ht
        contradiction
      · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨op, a, b, args, _, ha, hb⟩ := gate_shape sh hj
        rcases op with hand | hor
        · rw [and_support hExact hClean hj hand] at present
          exact (Finset.notMem_empty _ present).elim
        · rw [or_support hj args ha hb hor, Finset.mem_union] at present
          rw [(tracks_gate tr hj args).2 hor, Bool.or_eq_true]
          exact present.elim (fun h => Or.inl (ih a ha h)) (fun h => Or.inr (ih b hb h))

def rawSupport (C : Circuit) (w : ℕ) : Finset ℕ := (support C w).image Fin.val

def rawCenter (isCenter : Vertex → Prop) (w : ℕ) : Prop := ∃ v, v.val = w ∧ isCenter v

lemma raw_nonempty {C : Circuit} {w : ℕ} :
    (rawSupport C w).Nonempty ↔ (support C w).Nonempty := Finset.image_nonempty

lemma raw_empty {C : Circuit} {w : ℕ} : rawSupport C w = ∅ ↔ support C w = ∅ :=
  Finset.image_eq_empty

def armDescription (C : Circuit) (isCenter : Vertex → Prop) (c : Vertex)
    (a b : ℕ) : Prop :=
  isCenter c ∧ support C a = {c} ∧ (support C b).Nonempty ∧
    ∀ v ∈ support C b, ¬ isCenter v

lemma arm_raw_purity {C : Circuit} {isCenter : Vertex → Prop} {c : Vertex} {a b : ℕ}
    (h : armDescription C isCenter c a b) :
    Token.pureInputSide (rawCenter isCenter) (rawSupport C a) ∧
      Token.pureInputSide (rawCenter isCenter) (rawSupport C b) := by
  refine ⟨Or.inl ⟨c.val, ⟨c, rfl, h.1⟩, by simp [rawSupport, h.2.1]⟩, Or.inr ?_⟩
  intro v hv hc
  obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hv
  obtain ⟨u, hu, hU⟩ := hc
  have hEq : u = w := Fin.ext (hu.trans eq.symm)
  exact h.2.2.2 w hw (hEq ▸ hU)

lemma arm_labels {C : Circuit} {isCenter : Vertex → Prop} {c : Vertex} {a b : ℕ}
    (h : armDescription C isCenter c a b) :
    Token.tagOfSupport (rawCenter isCenter) (rawSupport C a) = some (.inl c.val) ∧
    Token.tagOfSupport (rawCenter isCenter) (rawSupport C b) = some (.inr ()) := by
  constructor
  · simp only [rawSupport, h.2.1, Finset.image_singleton]
    exact Token.tagOfSupport_center ⟨c, rfl, h.1⟩
  · apply Token.tagOfSupport_leaf (raw_nonempty.mpr h.2.2.1)
    intro v hv hc
    obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, hU⟩ := hc
    have hEq : u = w := Fin.ext (hu.trans eq.symm)
    exact h.2.2.2 w hw (hEq ▸ hU)

def noMixedAnd (C : Circuit) : Prop :=
  ∀ j < C.gates.length, live C (26 + j) → (gateAt C j).op = .and →
    ∀ a b, (gateAt C j).inputs = [a,b] →
      ((support C a).Nonempty ↔ (support C b).Nonempty)

def productiveOriented (C : Circuit) (isCenter : Vertex → Prop)
    (centerGate : ℕ → ℕ → Prop) : Prop :=
  ∀ j < C.gates.length, live C (26 + j) → (gateAt C j).op = .and →
    ∀ a b, (gateAt C j).inputs = [a,b] →
      (support C a).Nonempty → (support C b).Nonempty →
    ∃ c : Vertex, centerGate c.val (26 + j) ∧
      (armDescription C isCenter c a b ∨ armDescription C isCenter c b a)

lemma active_shape {C : Circuit} (sh : binary C) {v w : ℕ} (read : activeReads C v w) :
    ∃ j < C.gates.length, w = 26 + j ∧
      ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧
      ∃ a b, (gateAt C j).inputs = [a,b] ∧ a ≠ b ∧ a < w ∧ b < w ∧ (v = a ∨ v = b) := by
  obtain ⟨j, hj, rfl, hv⟩ := read.1
  obtain ⟨hop, a, b, args, ne, ha, hb⟩ := gate_shape sh hj
  rw [args] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  exact ⟨j,hj,rfl,hop,a,b,args,ne,ha,hb,hv⟩

lemma support_pure_active {C : Circuit} (sh : binary C) (hExact : computes C) (hClean : clean C)
    (isCenter : Vertex → Prop) (centerGate : ℕ → ℕ → Prop)
    (noMix : noMixedAnd C) (prod : productiveOriented C isCenter centerGate)
    {w : ℕ} (liveW : live C w) (nz : (support C w).Nonempty) :
    Token.pureInputSide (rawCenter isCenter) (rawSupport C w) := by
  have outputEmpty : support C C.output = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact no_singleton y ((hExact _).mp ((mem_support C C.output y).mp hy))
  apply Token.pure_support_on_path (reads := activeReads C) (support := rawSupport C)
    (raw_empty.mpr outputEmpty) _ _ (active_path liveW) (raw_nonempty.mpr nz)
  · intro u v read positive
    obtain ⟨j,hj,rfl,op,a,b,args,ne,ha,hb,hu⟩ := active_shape sh read
    rcases op with hand | hor
    · exfalso
      have hpos := raw_nonempty.mp positive
      rw [and_support hExact hClean hj hand] at hpos
      exact Finset.not_nonempty_empty hpos
    · rw [rawSupport, rawSupport, or_support hj args ha hb hor]
      apply Finset.image_subset_image
      rcases hu with rfl | rfl
      · exact Finset.subset_union_left
      · exact Finset.subset_union_right
  · intro u v read positive zero
    obtain ⟨j,hj,rfl,op,a,b,args,ne,ha,hb,hu⟩ := active_shape sh read
    rcases op with hand | hor
    · have hp := raw_nonempty.mp positive
      have mix := noMix j hj read.2 hand a b args
      have hab : (support C a).Nonempty ∧ (support C b).Nonempty := by
        rcases hu with rfl | rfl
        · exact ⟨hp, mix.mp hp⟩
        · exact ⟨mix.mpr hp, hp⟩
      obtain ⟨c, _, lab | lab⟩ := prod j hj read.2 hand a b args hab.1 hab.2 <;>
        rcases hu with rfl | rfl
      · exact (arm_raw_purity lab).1
      · exact (arm_raw_purity lab).2
      · exact (arm_raw_purity lab).2
      · exact (arm_raw_purity lab).1
    · have common := raw_empty.mp zero
      rw [or_support hj args ha hb hor, Finset.union_eq_empty] at common
      have hp := raw_nonempty.mp positive
      rcases hu with rfl | rfl
      · exact (Finset.not_nonempty_empty (common.1 ▸ hp)).elim
      · exact (Finset.not_nonempty_empty (common.2 ▸ hp)).elim

lemma labeled_input {C : Circuit} {isCenter : Vertex → Prop} {w : ℕ}
    (hw : w < 26) :
    let v : Vertex := ⟨w,hw⟩
    (isCenter v → Token.tagOfSupport (rawCenter isCenter) (rawSupport C w) = some (.inl w)) ∧
    (¬isCenter v → Token.tagOfSupport (rawCenter isCenter) (rawSupport C w) = some (.inr ())) := by
  intro v
  have hs : rawSupport C w = {w} := by simp [rawSupport, single_input_support C hw]
  rw [hs]
  constructor
  · intro hc
    exact Token.tagOfSupport_center ⟨v, rfl, hc⟩
  · intro hn
    refine Token.tagOfSupport_leaf (by simp) ?_
    intro u hu hc
    rw [Finset.mem_singleton] at hu
    subst u
    obtain ⟨z, he, hc⟩ := hc
    exact hn ((show z = v from Fin.ext he) ▸ hc)

lemma center_trace_from_birth {C : Circuit} (sh : binary C) (hExact : computes C) (hClean : clean C)
    (isCenter : Vertex → Prop) (centerGate : ℕ → ℕ → Prop)
    (noMix : noMixedAnd C) (prod : productiveOriented C isCenter centerGate)
    (unique : ∀ {u v w}, support C u = ∅ → activeReads C u v → activeReads C u w → v = w)
    (uniqueCenter : ∀ {c v w}, centerGate c v → centerGate c w → v = w)
    {x y : Vertex} (hx : isCenter x) (hy : ¬isCenter y)
    (accept : accepts (pair x y)) {j₀ : ℕ}
    (born : birth C j₀ x y) (liveBirth : live C (26 + j₀))
    {trace : ℕ → Bool} (tracked : tracks C y x.val trace) :
    trace C.output = true := by
  let label (w : ℕ) := Token.tagOfSupport (rawCenter isCenter) (rawSupport C w)
  let truth (w : ℕ) := live C w ∧ value C (pair x y) w = true
  let singletonY (w : ℕ) := value C (single y) w
  have zeroLabel (w : ℕ) : label w = none ↔ support C w = ∅ :=
    Token.tagOfSupport_none_iff.trans raw_empty
  have valueTag {c : Vertex} {a b : ℕ} (arm : armDescription C isCenter c a b) :
      label a = some (.inl c.val) ∧ label b = some (.inr ()) := arm_labels arm
  have edgeA {v w : ℕ} (h : activeReads C v w) : live C v := h.2.head h.1
  have directRead (j : ℕ) (hj : j < C.gates.length) (h : live C (26 + j))
      (u : ℕ) (arg : u ∈ (gateAt C j).inputs) : activeReads C u (26 + j) :=
    ⟨⟨j,hj,rfl,arg⟩,h⟩
  have source : centerGate x.val (26 + j₀) ∧ trace (26 + j₀) = true := by
    obtain ⟨hj, hand, a, b, args, edge | edge⟩ := born
    <;> have truA : (support C a).Nonempty := ⟨_, edge.1⟩
    <;> have truB : (support C b).Nonempty := ⟨_, edge.2⟩
    <;> obtain ⟨c, hc, arm | arm⟩ := prod j₀ hj liveBirth hand a b args truA truB
    · have he : x = c := by simpa [arm.2.1] using edge.1
      subst c
      refine ⟨hc, ?_⟩
      rw [(tracks_gate tracked hj args).1 hand,
        trace_of_center_singleton sh hExact hClean tracked a edge.1,
        (mem_support C b y).mp edge.2]
      simp
    · exact (arm.2.2.2 x edge.1 hx).elim
    · exact (arm.2.2.2 x edge.2 hx).elim
    · have he : x = c := by simpa [arm.2.1] using edge.2
      subst c
      refine ⟨hc, ?_⟩
      rw [(tracks_gate tracked hj args).1 hand,
        trace_of_center_singleton sh hExact hClean tracked b edge.2,
        (mem_support C a y).mp edge.1]
      simp
  have output : Token.trueEmptyWire label truth C.output := by
    refine ⟨⟨.refl, (hExact _).mpr accept⟩, (zeroLabel _).mpr ?_⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v vv
    exact no_singleton v ((hExact _).mp ((mem_support C C.output v).mp vv))
  refine Token.traceOfTightCenterSide (activeReads C) label truth centerGate singletonY trace
    x.val (26 + j₀) C.output ?_ ?_ uniqueCenter source.1 source.2 output ?_ ?_ ?_ ?_
  · intro u w read
    obtain ⟨j,hj,eq,op,a,b,args,ne,ha,hb,hu⟩ := active_shape sh read
    rcases hu with rfl | rfl
    · exact ha
    · exact hb
  · intro u v w em hr₁ hr₂
    exact unique ((zeroLabel u).mp em.2) hr₁ hr₂
  · intro u w read pos val
    obtain ⟨j,hj,rfl,op,a,b,args,ne,ha,hb,hu⟩ := active_shape sh read
    rcases op with hand | hor
    · exact (pos ((zeroLabel _).mpr (and_support hExact hClean hj hand))).elim
    · change value C (single y) (26 + j) = true
      rw [(apply_gate hj args ha hb _).2 hor, Bool.or_eq_true]
      rcases hu with rfl | rfl
      · exact Or.inl val
      · exact Or.inr val
  · intro u w read pos D
    obtain ⟨j,hj,rfl,op,a,b,args,ne,ha,hb,hu⟩ := active_shape sh read
    rcases op with hand | hor
    · exact (pos ((zeroLabel _).mpr (and_support hExact hClean hj hand))).elim
    · rw [(tracks_gate tracked hj args).2 hor, Bool.or_eq_true]
      rcases hu with rfl | rfl
      · exact Or.inl D
      · exact Or.inr D
  · intro t w wt tag
    by_cases hin : w < 26
    · have ht := wt.2
      rw [input_value hin] at ht
      rcases of_decide_eq_true ht with ex | ey
      · have lc := (labeled_input (C := C) (isCenter := isCenter) hin).1 (ex.symm ▸ hx)
        have tt : t = .inl w := Option.some.inj (tag.symm.trans lc)
        subst t
        exact Or.inl (congrArg Fin.val ex)
      · have ll := (labeled_input (C := C) (isCenter := isCenter) hin).2 (ey.symm ▸ hy)
        have tt : t = .inr () := Option.some.inj (tag.symm.trans ll)
        subst t
        left
        change value C (single y) w = true
        rw [input_value hin, ey]
        simp [single]
    · have hw : w < 26 + C.gates.length := by
        by_contra! hh
        have hget := wt.2
        rw [beyond_value hh] at hget
        contradiction
      obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨op,a,b,args,ne,ha,hb⟩ := gate_shape sh hj
      rcases op with hand | hor
      · have he := (zeroLabel _).mpr (and_support hExact hClean hj hand)
        rw [he] at tag
        contradiction
      · have ht := wt.2
        rw [(apply_gate hj args ha hb _).2 hor, Bool.or_eq_true] at ht
        have hp : (support C (26 + j)).Nonempty := by
          by_contra h
          have eql := (zeroLabel _).mpr (Finset.not_nonempty_iff_eq_empty.mp h)
          rw [eql] at tag
          contradiction
        have pure := support_pure_active sh hExact hClean isCenter centerGate noMix prod wt.1 hp
        have labelFor (v : ℕ) (sub : support C v ⊆ support C (26 + j)) :
            label v = none ∨ label v = some t := by
          by_cases nz : (support C v).Nonempty
          · exact Or.inr ((Token.tagOfSupport_eq_of_subset pure (Finset.image_subset_image sub)
              (raw_nonempty.mpr nz)).trans tag)
          · exact Or.inl ((zeroLabel _).mpr (Finset.not_nonempty_iff_eq_empty.mp nz))
        have ea := directRead j hj wt.1 a (by simp [args])
        have eb := directRead j hj wt.1 b (by simp [args])
        have subA : support C a ⊆ support C (26 + j) := by
          rw [or_support hj args ha hb hor]
          exact Finset.subset_union_left
        have subB : support C b ⊆ support C (26 + j) := by
          rw [or_support hj args ha hb hor]
          exact Finset.subset_union_right
        exact Or.inr (ht.elim (fun h => ⟨a,ea,⟨edgeA ea,h⟩,labelFor _ subA⟩)
          (fun h => ⟨b,eb,⟨edgeA eb,h⟩,labelFor _ subB⟩))
  · intro w wt _
    have wp := wt.1.2
    have wL := wt.1.1
    have wZ := (zeroLabel _).mp wt.2
    have hin : ¬w < 26 := by
      intro h
      rw [single_input_support C h] at wZ
      simp at wZ
    have hw : w < 26 + C.gates.length := by
      by_contra! hh
      rw [beyond_value hh] at wp
      contradiction
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨op,a,b,args,ne,ha,hb⟩ := gate_shape sh hj
    have ea := directRead j hj wL a (by simp [args])
    have eb := directRead j hj wL b (by simp [args])
    rcases op with hand | hor
    · rw [(apply_gate hj args ha hb _).1 hand, Bool.and_eq_true] at wp
      by_cases na : (support C a).Nonempty
      · have nb := (noMix j hj wL hand a b args).mp na
        obtain ⟨c, hc, arm | arm⟩ := prod j hj wL hand a b args na nb
        · exact Or.inr (Or.inr ⟨c.val,a,b,hc,ea,eb,⟨edgeA ea,wp.1⟩,⟨edgeA eb,wp.2⟩,
            (valueTag arm).1, (valueTag arm).2, fun hd ht => by
              rw [(tracks_gate tracked hj args).1 hand, hd, show value C (single y) b = true from ht]
              simp⟩)
        · exact Or.inr (Or.inr ⟨c.val,b,a,hc,eb,ea,⟨edgeA eb,wp.2⟩,⟨edgeA ea,wp.1⟩,
            (valueTag arm).1, (valueTag arm).2, fun hd ht => by
              rw [(tracks_gate tracked hj args).1 hand, hd, show value C (single y) a = true from ht]
              simp⟩)
      · have nb : ¬(support C b).Nonempty := fun h => na ((noMix j hj wL hand a b args).mpr h)
        exact Or.inr (Or.inl ⟨a,b,
          ⟨⟨edgeA ea,wp.1⟩,(zeroLabel _).mpr (Finset.not_nonempty_iff_eq_empty.mp na)⟩,
          ⟨⟨edgeA eb,wp.2⟩,(zeroLabel _).mpr (Finset.not_nonempty_iff_eq_empty.mp nb)⟩,ne,ea,eb⟩)
    · rw [(apply_gate hj args ha hb _).2 hor, Bool.or_eq_true] at wp
      rw [or_support hj args ha hb hor, Finset.union_eq_empty] at wZ
      exact wp.elim
        (fun h => Or.inl ⟨a,⟨⟨edgeA ea,h⟩,(zeroLabel _).mpr wZ.1⟩,ea,
          fun ht => by rw [(tracks_gate tracked hj args).2 hor, ht]; simp⟩)
        (fun h => Or.inl ⟨b,⟨⟨edgeA eb,h⟩,(zeroLabel _).mpr wZ.2⟩,eb,
          fun ht => by rw [(tracks_gate tracked hj args).2 hor, ht]; simp⟩)

end TraceBridge



def onCenterSide (side : Bool) (v : ℕ) : Prop :=
  if side then v < 13 else 13 ≤ v

lemma adjacent_switch_side (side : Bool) {u v : Vertex}
    (hu : onCenterSide side u.val) (h : adjacent u v) :
    ¬ onCenterSide side v.val := by
  rcases side <;> simp only [onCenterSide, Bool.false_eq_true, if_false, if_true] at hu ⊢ <;>
    rcases h with h | h <;> omega

lemma some_center_side {C : Circuit} (T : TightCircuit C) :
    ∃ side : Bool, ∀ w ∈ productive C, onCenterSide side (T.center w).val := by
  rcases T.uniform with hp | hl
  · refine ⟨true,?_⟩
    intro w hw
    obtain ⟨p,hp'⟩ := hp w hw
    rcases vertex_cases (T.center w) with ⟨q,hq⟩ | ⟨l,hl⟩
    · rw [← hq]
      simpa [onCenterSide, point] using q.isLt
    · rw [← hl, side_line] at hp'
      cases hp'
  · refine ⟨false,?_⟩
    intro w hw
    obtain ⟨l,hl'⟩ := hl w hw
    rcases vertex_cases (T.center w) with ⟨p,hp⟩ | ⟨q,hq⟩
    · rw [← hp, side_point] at hl'
      cases hl'
    · rw [← hq]
      simp [onCenterSide, line]



def feeds (C : Circuit) (a b : ℕ) : Prop := reads C a b ∧ b ∈ activeGates C

lemma feeds_iff {C : Circuit} (hB : binary C) {a b : ℕ} :
    feeds C a b ↔ b ∈ activeGates C ∧ ∃ i, operand C b i = a := by
  constructor
  · rintro ⟨⟨k,hk,hq,hm⟩,act⟩
    obtain ⟨j,hj,hj',_,hab,_,_⟩ := wire_info hB act
    have hk' : k = j := by omega
    subst k
    rw [hab] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact ⟨act,hm.elim (fun e => ⟨false,e.symm⟩) (fun e => ⟨true,e.symm⟩)⟩
  · rintro ⟨act,i,rfl⟩
    exact ⟨op_reads hB act i,act⟩



lemma output_pair_birth {C : Circuit} (hB : binary C) (hF : computes C)
    {u v : Vertex} (accepted : accepts (pair u v)) :
    ∃ j, birth C j u v ∧ live C (26+j) := by
  have hv : value C (pair u v) C.output = true := (hF _).mpr accepted
  rcases true_pair_has_origin hB u v C.output hv with h | h | hb
  · exact (no_singleton _ ((hF _).mp ((mem_support C C.output u).mp h))).elim
  · exact (no_singleton _ ((hF _).mp ((mem_support C C.output v).mp h))).elim
  · exact hb

lemma tight_operand_info {C : Circuit} (hB : binary C) {j a b : ℕ}
    (hj : j < C.gates.length) (hl : live C (26+j)) (args : (gateAt C j).inputs = [a,b]) :
    26+j ∈ activeGates C ∧
    operand C (26+j) false = a ∧ operand C (26+j) true = b ∧ live C a ∧ live C b := by
  have act : 26+j ∈ activeGates C := mem_active_gates.mpr ⟨⟨j,hj,rfl⟩,hl⟩
  have hA : operand C (26+j) false = a := by simp [operand, atWire, args]
  have hB' : operand C (26+j) true = b := by simp [operand, atWire, args]
  exact ⟨act,hA,hB',hA ▸ op_live hB act false,hB' ▸ op_live hB act true⟩

lemma tight_no_mixed {C : Circuit} (hB : binary C) (T : TightCircuit C) :
    TraceBridge.noMixedAnd C := by
  intro j hj hl hand a b args
  obtain ⟨act,hA,hB',hlA,hlB⟩ := tight_operand_info hB hj hl args
  have eq := T.balanced (26+j) act ((tag_and rfl).mpr hand)
  rw [hA,hB'] at eq
  simp only [hasSupport, support_at_live hlA, support_at_live hlB] at eq
  constructor
  · intro h
    exact of_decide_eq_true (eq.symm.trans (decide_eq_true h))
  · intro h
    exact of_decide_eq_true (eq.trans (decide_eq_true h))

def centerOf (C : Circuit) (T : TightCircuit C) (c w : ℕ) : Prop :=
  w ∈ productive C ∧ (T.center w).val = c

lemma center_unique {C : Circuit} (T : TightCircuit C) {c v w : ℕ}
    (hv : centerOf C T c v) (hw : centerOf C T c w) : v = w := by
  apply T.unique v hv.1 w hw.1
  exact congrArg sideVertex (Fin.ext (hv.2.trans hw.2.symm))

lemma tight_oriented {C : Circuit} (hB : binary C) (T : TightCircuit C) (side : Bool)
    (centers : ∀ w ∈ productive C, onCenterSide side (T.center w).val) :
    TraceBridge.productiveOriented C (fun v : Vertex => onCenterSide side v.val) (centerOf C T) := by
  intro j hj hl hand a b args ha hb
  obtain ⟨act,hA,hB',hlA,hlB⟩ := tight_operand_info hB hj hl args
  have prod : 26+j ∈ productive C := mem_productive.mpr
    ⟨act,(tag_and rfl).mpr hand,by simpa [hA,support_at_live hlA] using ha,
      by simpa [hB',support_at_live hlB] using hb⟩
  have hcenter := centers (26+j) prod
  have shape := T.shape (26+j) prod
  refine ⟨T.center (26+j),⟨prod,rfl⟩,?_⟩
  cases he : T.leaf (26+j)
  · right
    simp only [starShape, he, Bool.not_false, hA, hB', support_at_live hlA,
      support_at_live hlB] at shape
    exact ⟨hcenter,shape.1,ha,fun v hv =>
      adjacent_switch_side side hcenter ((neighbor_iff _ _).mp (shape.2 hv))⟩
  · left
    simp only [starShape, he, Bool.not_true, hA, hB', support_at_live hlA,
      support_at_live hlB] at shape
    exact ⟨hcenter,shape.1,hb,fun v hv =>
      adjacent_switch_side side hcenter ((neighbor_iff _ _).mp (shape.2 hv))⟩

lemma tight_read_unique {C : Circuit} (hB : binary C) (T : TightCircuit C)
    {u v w : ℕ} (zero : support C u = ∅)
    (hv : TraceBridge.activeReads C u v) (hw : TraceBridge.activeReads C u w) : v = w := by
  have toFeed {a b : ℕ} (h : TraceBridge.activeReads C a b) : feeds C a b := by
    obtain ⟨j,hj,hb,ha⟩ := h.1
    exact ⟨⟨j,hj,hb,ha⟩, mem_active_gates.mpr ⟨⟨j,hj,hb⟩,h.2⟩⟩
  obtain ⟨actV,i,hi⟩ := (feeds_iff hB).mp (toFeed hv)
  obtain ⟨actW,k,hk⟩ := (feeds_iff hB).mp (toFeed hw)
  have liveU := ReflTransGen.head hv.1 hv.2
  have zeroU : hasSupport C u = false := by simp [hasSupport, support_at_live liveU, zero]
  have slV : (⟨v,i⟩ : Σ _ : ℕ, Bool) ∈
      ZeroSlots.slots (activeGates C) (hasSupport C) (operand C) :=
    ZeroSlots.mem_slots.mpr ⟨actV,by rw [hi,zeroU]⟩
  have slW : (⟨w,k⟩ : Σ _ : ℕ, Bool) ∈
      ZeroSlots.slots (activeGates C) (hasSupport C) (operand C) :=
    ZeroSlots.mem_slots.mpr ⟨actW,by rw [hk,zeroU]⟩
  exact congrArg Sigma.fst (T.uniqueRead slV slW (hi.trans hk.symm))

lemma incidence_trace {C : Circuit} (hB : binary C) (hF : computes C) (hC : clean C)
    (small : C.size ≤ 64) (p : Point) (l : Line) (hi : incidence p l)
    (v w : ℕ → Bool) (hv : TraceBridge.tracks C (point p) (line l).val v)
    (hw : TraceBridge.tracks C (line l) (point p).val w) :
    v C.output = true ∨ w C.output = true := by
  obtain ⟨T⟩ := tight_circuit hB hF hC small
  obtain ⟨side,centers⟩ := some_center_side T
  have run (x y : Vertex) (hx : onCenterSide side x.val) (hy : ¬onCenterSide side y.val)
      (hyx : accepts (pair x y)) (t : ℕ → Bool)
      (ht : TraceBridge.tracks C y x.val t) : t C.output = true := by
    obtain ⟨j,hj,hl⟩ := output_pair_birth hB hF hyx
    exact TraceBridge.center_trace_from_birth hB hF hC
      (fun u => onCenterSide side u.val) (centerOf C T)
      (tight_no_mixed hB T) (tight_oriented hB T side centers)
      (fun zero a b => tight_read_unique hB T zero a b)
      (fun a b => center_unique T a b) hx hy hyx hj hl ht
  cases side
  · left
    exact run (line l) (point p) (by simp [onCenterSide,line])
      (by simpa [onCenterSide,point] using p.isLt)
      ⟨p,l,hi,by simp [pair],by simp [pair]⟩ v hv
  · right
    exact run (point p) (line l) (by simpa [onCenterSide,point] using p.isLt)
      (by simp [onCenterSide,line]) (pair_incidence p l hi) w hw




end PEqualNP.Outside.L_meta_2069_aux

theorem PEqualNP.Outside.L_meta_2069 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∀ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 → ∀ (x17 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x17)).getD ((26 : ℕ) + x14) Bool.false = Bool.true → x4.eval (List.ofFn x17) = Bool.true) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  intro D A O C p l v w tr hsize hB hF _ hC hInc hv hw
  exact PEqualNP.Outside.L_meta_2069_aux.incidence_trace hB hF hC hsize p l hInc v w hv hw
