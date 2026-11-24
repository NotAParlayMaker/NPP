import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2393_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_step_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_none (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hg : C.gates[j]? = none) : val C n x (n + j) = false := by
  unfold val
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length]
  have := List.getElem?_eq_none_iff.mp hg
  simp only [List.length_ofFn]
  omega

theorem val_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) :
    val C n x (n + j) =
      h.op.eval (h.inputs.map fun i => if i < n + j then val C n x i else false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  have := gate_value C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at this
  exact this

theorem val_or (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.or) :
    val C n x (n + j) = true ↔ ∃ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨w, hw, hv⟩
    by_cases hlt : w < n + j
    · exact ⟨w, hw, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨w, hw, hlt, hv⟩
    exact ⟨w, hw, by simpa [hlt] using hv⟩

theorem val_and (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and) :
    val C n x (n + j) = true ↔ ∀ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  constructor
  · intro hall w hw
    have hv := hall w hw
    by_cases hlt : w < n + j
    · exact ⟨hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · intro hall w hw
    obtain ⟨hlt, hv⟩ := hall w hw
    simpa [hlt] using hv

def e1 {n : ℕ} (t : Fin n) : Fin n → Bool := fun i => decide (i = t)

def e2 {n : ℕ} (c t : Fin n) : Fin n → Bool := fun i => decide (i = c ∨ i = t)


def cn (n : ℕ) (gs : List Gate) (j : ℕ) : List ℕ :=
  (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j []

theorem cones_fold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

theorem cn_snoc_old (n : ℕ) (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    cn n (gs ++ [g]) j = cn n gs j := by
  unfold cn
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [PEqualNP.EdgeOwnership.coneStep]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [cones_fold_length]; simpa using hj)]

theorem cn_snoc_new (n : ℕ) (gs : List Gate) (g : Gate) :
    cn n (gs ++ [g]) gs.length =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
        (fun w => (w - n) :: cn n gs (w - n)) := by
  unfold cn
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [PEqualNP.EdgeOwnership.coneStep]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [cones_fold_length]; simp)]
  simp [cones_fold_length]

theorem cn_mem (n : ℕ) (gs : List Gate) (j : ℕ) (h : Gate) (hg : gs[j]? = some h) (i : ℕ) :
    i ∈ cn n gs j ↔
      ∃ w ∈ h.inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ i ∈ cn n gs (w - n)) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hg
  | append_singleton gs g0 ih =>
    obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.mp hg
    simp only [List.length_append, List.length_cons, List.length_nil] at hjlt
    have hold : ∀ w, n ≤ w → w < n + j → cn n (gs ++ [g0]) (w - n) = cn n gs (w - n) :=
      fun w _ _ => cn_snoc_old n gs g0 (w - n) (by omega)
    by_cases hjl : j = gs.length
    · subst hjl
      have hgg : g0 = h := by
        simpa using hg
      subst hgg
      rw [cn_snoc_new]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        exact ⟨w, hw, h1, h2, by rw [hold w h1 h2]; exact h3⟩
      · rintro ⟨w, hw, h1, h2, h3⟩
        exact ⟨w, ⟨hw, h1, h2⟩, by rw [hold w h1 h2] at h3; exact h3⟩
    · have hj' : j < gs.length := by omega
      have hg' : gs[j]? = some h := by
        rw [List.getElem?_append_left hj'] at hg
        exact hg
      rw [cn_snoc_old n gs g0 j hj', ih hg']
      constructor
      · rintro ⟨w, hw, h1, h2, h3⟩
        exact ⟨w, hw, h1, h2, by rw [hold w h1 h2]; exact h3⟩
      · rintro ⟨w, hw, h1, h2, h3⟩
        exact ⟨w, hw, h1, h2, by rw [hold w h1 h2] at h3; exact h3⟩

-- The plane of order 3: points are the inputs 0..12, lines the inputs 13..25.
def pt (p : Fin 13) : Fin 26 := ⟨p.val, by have := p.isLt; omega⟩

def ln (l : Fin 13) : Fin 26 := ⟨13 + l.val, by have := l.isLt; omega⟩

theorem pt_ne_ln (p l : Fin 13) : pt p ≠ ln l := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [pt, ln] at h2
  have := p.isLt
  omega

theorem pt_inj (p p' : Fin 13) (h : pt p = pt p') : p = p' := by
  have h2 := congrArg Fin.val h
  simp only [pt] at h2
  exact Fin.ext h2

theorem ln_inj (l l' : Fin 13) (h : ln l = ln l') : l = l' := by
  have h2 := congrArg Fin.val h
  simp only [ln] at h2
  exact Fin.ext (by omega)

theorem cases26 (i : Fin 26) : (∃ p : Fin 13, i = pt p) ∨ (∃ l : Fin 13, i = ln l) := by
  by_cases h : i.val < 13
  · exact Or.inl ⟨⟨i.val, h⟩, Fin.ext rfl⟩
  · have := i.isLt
    refine Or.inr ⟨⟨i.val - 13, by omega⟩, Fin.ext ?_⟩
    simp only [ln]
    omega

def adj (i j : Fin 26) : Prop :=
  ∃ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
    ((i = pt p ∧ j = ln l) ∨ (i = ln l ∧ j = pt p))

theorem adj_pl (p l : Fin 13) :
    adj (pt p) (ln l) ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  constructor
  · rintro ⟨a, b, hab, (⟨h1, h2⟩ | ⟨h1, _⟩)⟩
    · rw [pt_inj _ _ h1, ln_inj _ _ h2]
      exact hab
    · exact absurd h1 (pt_ne_ln p b)
  · intro h
    exact ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩

theorem adj_lp (l p : Fin 13) :
    adj (ln l) (pt p) ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  constructor
  · rintro ⟨a, b, hab, (⟨h1, _⟩ | ⟨h1, h2⟩)⟩
    · exact absurd h1.symm (pt_ne_ln a l)
    · rw [pt_inj _ _ h2, ln_inj _ _ h1]
      exact hab
  · intro h
    exact ⟨p, l, h, Or.inr ⟨rfl, rfl⟩⟩

theorem adj_pp (p p' : Fin 13) : ¬ adj (pt p) (pt p') := by
  rintro ⟨a, b, _, (⟨_, h2⟩ | ⟨h1, _⟩)⟩
  · exact pt_ne_ln p' b h2
  · exact pt_ne_ln p b h1

theorem adj_ll (l l' : Fin 13) : ¬ adj (ln l) (ln l') := by
  rintro ⟨a, b, _, (⟨h1, _⟩ | ⟨_, h2⟩)⟩
  · exact pt_ne_ln a l h1.symm
  · exact pt_ne_ln a l' h2.symm

-- Two points lie on at most one common line (checked by cases).
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem quad_aux : ∀ p1 l1 : Fin 13, p1 - l1 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
    ∀ l2 : Fin 13, p1 - l2 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
    ∀ p2 : Fin 13, p2 - l1 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
    p2 - l2 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → p1 = p2 ∨ l1 = l2 := by
  decide

theorem adj_irr (i : Fin 26) : ¬ adj i i := by
  rcases cases26 i with ⟨p, rfl⟩ | ⟨l, rfl⟩
  · exact adj_pp p p
  · exact adj_ll l l

theorem adj_c4 (c1 c2 a b : Fin 26) (hc : c1 ≠ c2) (hab : a ≠ b) (h1 : adj c1 a)
    (h2 : adj c1 b) (h3 : adj c2 a) (h4 : adj c2 b) : False := by
  rcases cases26 c1 with ⟨p1, rfl⟩ | ⟨l1, rfl⟩
  · rcases cases26 a with ⟨pa, rfl⟩ | ⟨l1, rfl⟩
    · exact adj_pp _ _ h1
    rcases cases26 b with ⟨pb, rfl⟩ | ⟨l2, rfl⟩
    · exact adj_pp _ _ h2
    rcases cases26 c2 with ⟨p2, rfl⟩ | ⟨lc, rfl⟩
    · rcases quad_aux p1 l1 ((adj_pl _ _).mp h1) l2 ((adj_pl _ _).mp h2) p2
        ((adj_pl _ _).mp h3) ((adj_pl _ _).mp h4) with h | h
      · exact hc (by rw [h])
      · exact hab (by rw [h])
    · exact adj_ll _ _ h3
  · rcases cases26 a with ⟨p1, rfl⟩ | ⟨la, rfl⟩
    swap
    · exact adj_ll _ _ h1
    rcases cases26 b with ⟨p2, rfl⟩ | ⟨lb, rfl⟩
    swap
    · exact adj_ll _ _ h2
    rcases cases26 c2 with ⟨pc, rfl⟩ | ⟨l2, rfl⟩
    · exact adj_pp _ _ h3
    · rcases quad_aux p1 l1 ((adj_lp _ _).mp h1) l2 ((adj_lp _ _).mp h3) p2
        ((adj_lp _ _).mp h2) ((adj_lp _ _).mp h4) with h | h
      · exact hab (by rw [h])
      · exact hc (by rw [h])

-- Quadrangles through two points, off two lines, through a point and off a line:

-- The 52 incident pairs, as pairs of inputs (point first).
def E26 : Finset (Fin 26 × Fin 26) :=
  ((Finset.univ : Finset (Fin 13 × Fin 13)).filter
    (fun e => e.1 - e.2 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).image
    (fun e => (pt e.1, ln e.2))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem e13_card : ((Finset.univ : Finset (Fin 13 × Fin 13)).filter
    (fun e => e.1 - e.2 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card = 52 := by
  decide

theorem e26_card : E26.card = 52 := by
  unfold E26
  rw [Finset.card_image_of_injective, e13_card]
  intro e e' h
  have h1 := pt_inj _ _ (congrArg Prod.fst h)
  have h2 := ln_inj _ _ (congrArg Prod.snd h)
  exact Prod.ext h1 h2

theorem e26_mem (e : Fin 26 × Fin 26) (he : e ∈ E26) :
    ∃ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ e = (pt p, ln l) := by
  unfold E26 at he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  exact ⟨a.1, a.2, (Finset.mem_filter.mp ha).2, rfl⟩

theorem e26_diag (l : Fin 13) : (pt l, ln l) ∈ E26 := by
  unfold E26
  refine Finset.mem_image.mpr ⟨(l, l), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  simp

-- The 13 pairs (point l, line l) are disjoint, so a cover has at least 13 inputs.
theorem cover13 (K : Finset (Fin 26)) (hK : ∀ e ∈ E26, e.1 ∈ K ∨ e.2 ∈ K) :
    13 ≤ K.card := by
  classical
  have hinj : Function.Injective (fun l : Fin 13 => if pt l ∈ K then pt l else ln l) := by
    intro l l' h
    simp only at h
    by_cases h1 : pt l ∈ K <;> by_cases h2 : pt l' ∈ K
    · rw [ite_eq_left h1, ite_eq_left h2] at h
      exact pt_inj _ _ h
    · rw [ite_eq_left h1, ite_eq_right h2] at h
      exact absurd h (pt_ne_ln l l')
    · rw [ite_eq_right h1, ite_eq_left h2] at h
      exact absurd h.symm (pt_ne_ln l' l)
    · rw [ite_eq_right h1, ite_eq_right h2] at h
      exact ln_inj _ _ h
  have hsub : (Finset.univ : Finset (Fin 13)).image
      (fun l : Fin 13 => if pt l ∈ K then pt l else ln l) ⊆ K := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
    by_cases h1 : pt l ∈ K
    · simp only [ite_eq_left h1]
      exact h1
    · simp only [ite_eq_right h1]
      rcases hK _ (e26_diag l) with h | h
      · exact absurd h h1
      · exact h
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hc
  exact hc

-- ===================== PART B: the setting (skeleton) =====================

-- more plane facts
theorem adj_symm (u v : Fin 26) (h : adj u v) : adj v u := by
  obtain ⟨p, l, hpl, h1 | h1⟩ := h
  · exact ⟨p, l, hpl, Or.inr ⟨h1.2, h1.1⟩⟩
  · exact ⟨p, l, hpl, Or.inl ⟨h1.2, h1.1⟩⟩

-- GROUP P (plane)
theorem e26_adj (e : Fin 26 × Fin 26) (he : e ∈ E26) : adj e.1 e.2 := by
  obtain ⟨p, l, hpl, he2⟩ := e26_mem e he
  rw [he2]
  exact ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩

theorem p_e26_pl (p l : Fin 13) (h : p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) :
    (pt p, ln l) ∈ E26 := by
  unfold E26
  exact Finset.mem_image.mpr ⟨(p, l), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

theorem adj_e26 (u v : Fin 26) (h : adj u v) : (u, v) ∈ E26 ∨ (v, u) ∈ E26 := by
  obtain ⟨p, l, hpl, h1 | h1⟩ := h
  · rw [h1.1, h1.2]
    exact Or.inl (p_e26_pl p l hpl)
  · rw [h1.1, h1.2]
    exact Or.inr (p_e26_pl p l hpl)

theorem e26_orient (e e' : Fin 26 × Fin 26) (he : e ∈ E26) (he' : e' ∈ E26)
    (h : (e.1 = e'.1 ∧ e.2 = e'.2) ∨ (e.1 = e'.2 ∧ e.2 = e'.1)) : e = e' := by
  obtain ⟨p, l, _, h1⟩ := e26_mem e he
  obtain ⟨p', l', _, h2⟩ := e26_mem e' he'
  rw [h1, h2] at h
  rcases h with h3 | h3
  · rw [h1, h2]
    exact Prod.ext h3.1 h3.2
  · exact absurd h3.1 (pt_ne_ln p l')

-- every point is on exactly four lines, every line carries exactly four points
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem p_deg_pt : ∀ p : Fin 13, ((Finset.univ : Finset (Fin 13)).filter
    (fun l : Fin 13 => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card = 4 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem p_deg_ln : ∀ l : Fin 13, ((Finset.univ : Finset (Fin 13)).filter
    (fun p : Fin 13 => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card = 4 := by
  decide

theorem deg4 (c : Fin 26) : (E26.filter (fun e => e.1 = c ∨ e.2 = c)).card ≤ 4 := by
  rcases cases26 c with ⟨p, hc⟩ | ⟨l, hc⟩
  · rw [hc]
    have hsub : E26.filter (fun e => e.1 = pt p ∨ e.2 = pt p) ⊆
        ((Finset.univ : Finset (Fin 13)).filter
          (fun l : Fin 13 => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).image
          (fun l : Fin 13 => (pt p, ln l)) := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
      obtain ⟨p', l', hpl, he3⟩ := e26_mem e he1
      rw [he3] at he2
      rw [he3]
      rcases he2 with h | h
      · have hpp : p' = p := pt_inj p' p h
        rw [hpp] at hpl
        rw [hpp]
        exact Finset.mem_image.mpr ⟨l', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩, rfl⟩
      · exact absurd h.symm (pt_ne_ln p l')
    exact le_trans (Finset.card_le_card hsub)
      (le_trans Finset.card_image_le (le_of_eq (p_deg_pt p)))
  · rw [hc]
    have hsub : E26.filter (fun e => e.1 = ln l ∨ e.2 = ln l) ⊆
        ((Finset.univ : Finset (Fin 13)).filter
          (fun p : Fin 13 => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).image
          (fun p : Fin 13 => (pt p, ln l)) := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
      obtain ⟨p', l', hpl, he3⟩ := e26_mem e he1
      rw [he3] at he2
      rw [he3]
      rcases he2 with h | h
      · exact absurd h (pt_ne_ln p' l)
      · have hll : l' = l := ln_inj l' l h
        rw [hll] at hpl
        rw [hll]
        exact Finset.mem_image.mpr ⟨p', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩, rfl⟩
    exact le_trans (Finset.card_le_card hsub)
      (le_trans Finset.card_image_le (le_of_eq (p_deg_ln l)))

-- two different points are separated by a line, two different lines by a point
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem p_diff_pt : ∀ p p' : Fin 13, p ≠ p' →
    ∃ l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      p' - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem p_diff_ln : ∀ l l' : Fin 13, l ≠ l' →
    ∃ p : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      p - l' ∉ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  decide

theorem p_self_mem (p : Fin 13) : p - p ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  simp

theorem nbr_diff (c c' : Fin 26) (h : c ≠ c') : ∃ w : Fin 26, adj c w ∧ ¬ adj c' w := by
  rcases cases26 c with ⟨p, hc⟩ | ⟨l, hc⟩
  · rcases cases26 c' with ⟨p', hc'⟩ | ⟨l', hc'⟩
    · rw [hc, hc']
      have hne : p ≠ p' := by
        intro hpp
        apply h
        rw [hc, hc', hpp]
      obtain ⟨l, h1, h2⟩ := p_diff_pt p p' hne
      exact ⟨ln l, (adj_pl p l).mpr h1, fun h3 => h2 ((adj_pl p' l).mp h3)⟩
    · rw [hc, hc']
      exact ⟨ln p, (adj_pl p p).mpr (p_self_mem p), adj_ll l' p⟩
  · rcases cases26 c' with ⟨p', hc'⟩ | ⟨l', hc'⟩
    · rw [hc, hc']
      exact ⟨pt l, (adj_lp l l).mpr (p_self_mem l), adj_pp p' l⟩
    · rw [hc, hc']
      have hne : l ≠ l' := by
        intro hll
        apply h
        rw [hc, hc', hll]
      obtain ⟨p, h1, h2⟩ := p_diff_ln l l' hne
      exact ⟨pt p, (adj_lp l p).mpr h1, fun h3 => h2 ((adj_lp l' p).mp h3)⟩

-- GROUP SETTING (frozen)
theorem e1_self (u : Fin 26) : e1 u u = true := by simp [e1]

theorem e1_mem (u z : Fin 26) (h : e1 u z = true) : z = u := by simpa [e1] using h

theorem e2_left (u v : Fin 26) : e2 u v u = true := by simp [e2]

theorem e2_right (u v : Fin 26) : e2 u v v = true := by simp [e2]

theorem e2_mem (u v z : Fin 26) (h : e2 u v z = true) : z = u ∨ z = v := by simpa [e2] using h

-- the circuit seen as data: gate j < C.gates.length is wire 26 + j, reads wires gA C j and gB C j
def gA (C : Circuit) (j : ℕ) : ℕ :=
  (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0

def gB (C : Circuit) (j : ℕ) : ℕ :=
  (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0

def isAnd (C : Circuit) (j : ℕ) : Prop :=
  (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and

def vl (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) : Bool := val C 26 x w

def oG (C : Circuit) : ℕ := C.output - 26

-- everything the argument uses about the circuit
def Good (C : Circuit) : Prop :=
  (∀ j, j < C.gates.length → gA C j < 26 + j ∧ gB C j < 26 + j) ∧
  (∀ (x : Fin 26 → Bool) (j : ℕ), j < C.gates.length → isAnd C j →
    vl C x (26 + j) = (vl C x (gA C j) && vl C x (gB C j))) ∧
  (∀ (x : Fin 26 → Bool) (j : ℕ), j < C.gates.length → ¬ isAnd C j →
    vl C x (26 + j) = (vl C x (gA C j) || vl C x (gB C j))) ∧
  oG C < C.gates.length ∧
  (∀ u v : Fin 26, adj u v → vl C (e2 u v) (26 + oG C) = true) ∧
  (∀ u : Fin 26, vl C (e1 u) (26 + oG C) = false) ∧
  (∀ j, j < C.gates.length → isAnd C j → ∀ x : Fin 26 → Bool, vl C x (26 + j) = true →
    ∃ u v : Fin 26, adj u v ∧ x u = true ∧ x v = true)

theorem good_hA (C : Circuit) (hG : Good C) (j : ℕ) (hj : j < C.gates.length) :
    gA C j < 26 + j := (hG.1 j hj).1

theorem good_hB (C : Circuit) (hG : Good C) (j : ℕ) (hj : j < C.gates.length) :
    gB C j < 26 + j := (hG.1 j hj).2

theorem good_and (C : Circuit) (hG : Good C) (x : Fin 26 → Bool) (j : ℕ)
    (hj : j < C.gates.length) (ha : isAnd C j) :
    vl C x (26 + j) = (vl C x (gA C j) && vl C x (gB C j)) := hG.2.1 x j hj ha

theorem good_or (C : Circuit) (hG : Good C) (x : Fin 26 → Bool) (j : ℕ)
    (hj : j < C.gates.length) (ha : ¬ isAnd C j) :
    vl C x (26 + j) = (vl C x (gA C j) || vl C x (gB C j)) := hG.2.2.1 x j hj ha

theorem good_o (C : Circuit) (hG : Good C) : oG C < C.gates.length := hG.2.2.2.1

theorem good_acc (C : Circuit) (hG : Good C) (u v : Fin 26) (h : adj u v) :
    vl C (e2 u v) (26 + oG C) = true := hG.2.2.2.2.1 u v h

theorem good_rej (C : Circuit) (hG : Good C) (u : Fin 26) :
    vl C (e1 u) (26 + oG C) = false := hG.2.2.2.2.2.1 u

theorem good_junk (C : Circuit) (hG : Good C) (j : ℕ) (hj : j < C.gates.length)
    (ha : isAnd C j) (x : Fin 26 → Bool) (hx : vl C x (26 + j) = true) :
    ∃ u v : Fin 26, adj u v ∧ x u = true ∧ x v = true := hG.2.2.2.2.2.2 j hj ha x hx

theorem vl_input (C : Circuit) (x : Fin 26 → Bool) (u : Fin 26) : vl C x u.val = x u :=
  val_input C 26 x u.val u.isLt

-- single-input supports
def acc (C : Circuit) (w : ℕ) (u : Fin 26) : Prop := vl C (e1 u) w = true

def LowW (C : Circuit) (w : ℕ) : Prop := ∀ u : Fin 26, ¬ acc C w u

def SingW (C : Circuit) (w : ℕ) (t : Fin 26) : Prop := ∀ u : Fin 26, acc C w u ↔ u = t

def BigW (C : Circuit) (w : ℕ) : Prop := ∃ t1 t2 : Fin 26, t1 ≠ t2 ∧ acc C w t1 ∧ acc C w t2

-- read positions: (gate, false) reads gA, (gate, true) reads gB
def rd (C : Circuit) (p : ℕ × Bool) : ℕ := if p.2 = true then gB C p.1 else gA C p.1

-- gate g reads gate k
def Rdv (C : Circuit) (g k : ℕ) : Prop :=
  g < C.gates.length ∧ (gA C g = 26 + k ∨ gB C g = 26 + k)

-- OR gate a reads gate b
def OrRd (C : Circuit) (a b : ℕ) : Prop :=
  a < C.gates.length ∧ ¬ isAnd C a ∧ (gA C a = 26 + b ∨ gB C a = 26 + b)

-- gate g lies in the OR closure of wire w
def Orc (C : Circuit) (w g : ℕ) : Prop :=
  ∃ k, w = 26 + k ∧ k < C.gates.length ∧ Relation.ReflTransGen (OrRd C) k g

-- GROUP G0 (basics)
theorem rd_false (C : Circuit) (j : ℕ) : rd C (j, false) = gA C j := by simp [rd]

theorem rd_true (C : Circuit) (j : ℕ) : rd C (j, true) = gB C j := by simp [rd]

theorem rd_lt (C : Circuit) (hG : Good C) (p : ℕ × Bool) (hp : p.1 < C.gates.length) :
    rd C p < 26 + p.1 := by
  obtain ⟨j, b⟩ := p
  cases b
  · rw [rd_false]
    exact good_hA C hG j hp
  · rw [rd_true]
    exact good_hB C hG j hp

theorem rdv_iff (C : Circuit) (g k : ℕ) :
    Rdv C g k ↔ g < C.gates.length ∧ ∃ b : Bool, rd C (g, b) = 26 + k := by
  unfold Rdv
  constructor
  · rintro ⟨hg, h | h⟩
    · exact ⟨hg, false, by rw [rd_false]; exact h⟩
    · exact ⟨hg, true, by rw [rd_true]; exact h⟩
  · rintro ⟨hg, b, h⟩
    cases b
    · rw [rd_false] at h
      exact ⟨hg, Or.inl h⟩
    · rw [rd_true] at h
      exact ⟨hg, Or.inr h⟩

theorem vl_and (C : Circuit) (hG : Good C) (x : Fin 26 → Bool) (j : ℕ)
    (hj : j < C.gates.length) (ha : isAnd C j) :
    vl C x (26 + j) = true ↔ vl C x (gA C j) = true ∧ vl C x (gB C j) = true := by
  rw [good_and C hG x j hj ha]
  exact Bool.and_eq_true_iff

theorem vl_or (C : Circuit) (hG : Good C) (x : Fin 26 → Bool) (j : ℕ)
    (hj : j < C.gates.length) (ha : ¬ isAnd C j) :
    vl C x (26 + j) = true ↔ vl C x (gA C j) = true ∨ vl C x (gB C j) = true := by
  rw [good_or C hG x j hj ha]
  exact Bool.or_eq_true_iff

theorem trich (C : Circuit) (w : ℕ) : LowW C w ∨ (∃ t, SingW C w t) ∨ BigW C w := by
  by_cases h1 : ∃ t : Fin 26, acc C w t
  · obtain ⟨t, ht⟩ := h1
    by_cases h2 : ∃ t' : Fin 26, t' ≠ t ∧ acc C w t'
    · obtain ⟨t', hne, ht'⟩ := h2
      exact Or.inr (Or.inr ⟨t', t, hne, ht', ht⟩)
    · refine Or.inr (Or.inl ⟨t, fun u => ⟨fun hu => ?_, fun hu => ?_⟩⟩)
      · by_contra hne
        exact h2 ⟨u, hne, hu⟩
      · rw [hu]
        exact ht
  · exact Or.inl (fun u hu => h1 ⟨u, hu⟩)

theorem wire_cases (C : Circuit) (w : ℕ) (hw : w < 26 + C.gates.length) :
    (∃ u : Fin 26, w = u.val) ∨ ∃ j, j < C.gates.length ∧ w = 26 + j := by
  by_cases h : w < 26
  · exact Or.inl ⟨⟨w, h⟩, rfl⟩
  · exact Or.inr ⟨w - 26, by omega, by omega⟩

theorem vl_mono (C : Circuit) (hG : Good C) (x y : Fin 26 → Bool)
    (hxy : ∀ u, x u = true → y u = true) (w : ℕ) (hw : w < 26 + C.gates.length)
    (hx : vl C x w = true) : vl C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases wire_cases C w hw with ⟨u, hwu⟩ | ⟨j, hj, hwj⟩
    · rw [hwu, vl_input] at hx
      rw [hwu, vl_input]
      exact hxy u hx
    · have hA := good_hA C hG j hj
      have hB := good_hB C hG j hj
      rw [hwj] at hx
      rw [hwj]
      by_cases ha : isAnd C j
      · rw [vl_and C hG x j hj ha] at hx
        rw [vl_and C hG y j hj ha]
        exact ⟨ih (gA C j) (by omega) (by omega) hx.1, ih (gB C j) (by omega) (by omega) hx.2⟩
      · rw [vl_or C hG x j hj ha] at hx
        rw [vl_or C hG y j hj ha]
        rcases hx with h | h
        · exact Or.inl (ih (gA C j) (by omega) (by omega) h)
        · exact Or.inr (ih (gB C j) (by omega) (by omega) h)

theorem sing_input (C : Circuit) (u : Fin 26) : SingW C u.val u := by
  unfold SingW
  intro t
  unfold acc
  rw [vl_input]
  constructor
  · intro h
    exact (e1_mem t u h).symm
  · intro h
    rw [h]
    exact e1_self u

theorem and_low (C : Circuit) (hG : Good C) (j : ℕ) (hj : j < C.gates.length)
    (ha : isAnd C j) : LowW C (26 + j) := by
  unfold LowW
  intro u hu
  obtain ⟨a, b, hab, h1, h2⟩ := good_junk C hG j hj ha (e1 u) hu
  have ha' : a = u := e1_mem u a h1
  have hb' : b = u := e1_mem u b h2
  rw [ha', hb'] at hab
  exact adj_irr u hab

theorem out_low (C : Circuit) (hG : Good C) : LowW C (26 + oG C) := by
  unfold LowW
  intro u hu
  unfold acc at hu
  rw [good_rej C hG u] at hu
  exact absurd hu (by decide)

theorem acc_or (C : Circuit) (hG : Good C) (j : ℕ) (hj : j < C.gates.length)
    (ha : ¬ isAnd C j) (u : Fin 26) :
    acc C (26 + j) u ↔ acc C (gA C j) u ∨ acc C (gB C j) u := by
  unfold acc
  exact vl_or C hG (e1 u) j hj ha

theorem low_is_gate (C : Circuit) (w : ℕ) (hw : w < 26 + C.gates.length) (hl : LowW C w) :
    ∃ j, j < C.gates.length ∧ w = 26 + j := by
  rcases wire_cases C w hw with ⟨u, hwu⟩ | h
  · rw [hwu] at hl
    exact absurd ((sing_input C u u).mpr rfl) (hl u)
  · exact h

theorem fact2 (C : Circuit) (hG : Good C) (j : ℕ) (hj : j < C.gates.length)
    (ha : isAnd C j) (u v : Fin 26) (hu : acc C (gA C j) u) (hv : acc C (gB C j) v) :
    adj u v := by
  have hA := good_hA C hG j hj
  have hB := good_hB C hG j hj
  have hxu : ∀ z : Fin 26, e1 u z = true → e2 u v z = true := by
    intro z hz
    rw [e1_mem u z hz]
    exact e2_left u v
  have hxv : ∀ z : Fin 26, e1 v z = true → e2 u v z = true := by
    intro z hz
    rw [e1_mem v z hz]
    exact e2_right u v
  have h1 : vl C (e2 u v) (gA C j) = true :=
    vl_mono C hG (e1 u) (e2 u v) hxu (gA C j) (by omega) hu
  have h2 : vl C (e2 u v) (gB C j) = true :=
    vl_mono C hG (e1 v) (e2 u v) hxv (gB C j) (by omega) hv
  have h3 : vl C (e2 u v) (26 + j) = true := (vl_and C hG (e2 u v) j hj ha).mpr ⟨h1, h2⟩
  obtain ⟨a, b, hab, ha1, hb1⟩ := good_junk C hG j hj ha (e2 u v) h3
  rcases e2_mem u v a ha1 with h4 | h4
  · rcases e2_mem u v b hb1 with h5 | h5
    · rw [h4, h5] at hab
      exact absurd hab (adj_irr u)
    · rw [h4, h5] at hab
      exact hab
  · rcases e2_mem u v b hb1 with h5 | h5
    · rw [h4, h5] at hab
      exact adj_symm v u hab
    · rw [h4, h5] at hab
      exact absurd hab (adj_irr v)

-- GROUP G0B (closure)
-- an OR gate reads only earlier gates
theorem g0b_orrd_lt (C : Circuit) (hG : Good C) (a b : ℕ) (h : OrRd C a b) : b < a := by
  obtain ⟨ha, _, h1 | h1⟩ := h
  · have h2 := good_hA C hG a ha
    omega
  · have h2 := good_hB C hG a ha
    omega

theorem g0b_rtg_le (C : Circuit) (hG : Good C) (a b : ℕ)
    (h : Relation.ReflTransGen (OrRd C) a b) : b ≤ a := by
  induction h with
  | refl => exact le_refl a
  | tail _ hbc ih =>
    have h2 := g0b_orrd_lt C hG _ _ hbc
    omega

theorem g0b_rtg_vl (C : Circuit) (hG : Good C) (x : Fin 26 → Bool) (k g : ℕ)
    (hp : Relation.ReflTransGen (OrRd C) k g) (hx : vl C x (26 + g) = true) :
    vl C x (26 + k) = true := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact hx
  | head hac _ ih =>
    obtain ⟨ha, hor, hr | hr⟩ := hac
    · exact (vl_or C hG x _ ha hor).mpr (Or.inl (by rw [hr]; exact ih))
    · exact (vl_or C hG x _ ha hor).mpr (Or.inr (by rw [hr]; exact ih))

theorem orc_base (C : Circuit) (g : ℕ) (hg : g < C.gates.length) : Orc C (26 + g) g := by
  exact ⟨g, rfl, hg, Relation.ReflTransGen.refl⟩

theorem orc_step (C : Circuit) (k : ℕ) (b : Bool) (g : ℕ) (hk : k < C.gates.length)
    (hor : ¬ isAnd C k) (h : Orc C (rd C (k, b)) g) : Orc C (26 + k) g := by
  obtain ⟨k', hk', _, hp⟩ := h
  refine ⟨k, rfl, hk, Relation.ReflTransGen.head ⟨hk, hor, ?_⟩ hp⟩
  cases b with
  | false =>
    rw [rd_false] at hk'
    exact Or.inl hk'
  | true =>
    rw [rd_true] at hk'
    exact Or.inr hk'

theorem orc_bounds (C : Circuit) (hG : Good C) (w g : ℕ) (h : Orc C w g) :
    g < C.gates.length ∧ 26 + g ≤ w ∧ w < 26 + C.gates.length := by
  obtain ⟨k, hw, hk, hp⟩ := h
  have h2 := g0b_rtg_le C hG k g hp
  refine ⟨?_, ?_, ?_⟩ <;> omega

-- orc_first with the extra hypothesis g < C.gates.length (no Good needed)
theorem g0b_orc_first_lt (C : Circuit) (w g : ℕ) (h : Orc C w g) (hg : g < C.gates.length) :
    w = 26 + g ∨ ∃ k b, w = 26 + k ∧ k < C.gates.length ∧ ¬ isAnd C k ∧
      Orc C (rd C (k, b)) g := by
  obtain ⟨k, hw, hk, hp⟩ := h
  rcases Relation.ReflTransGen.cases_head hp with h1 | ⟨c, hkc, hcg⟩
  · left
    omega
  · right
    have hc : c < C.gates.length := by
      rcases Relation.ReflTransGen.cases_head hcg with h2 | ⟨d, hcd, _⟩
      · omega
      · exact hcd.1
    obtain ⟨_, hor, hr | hr⟩ := hkc
    · exact ⟨k, false, hw, hk, hor, c, by rw [rd_false]; exact hr, hc, hcg⟩
    · exact ⟨k, true, hw, hk, hor, c, by rw [rd_true]; exact hr, hc, hcg⟩

-- orc_first with the hypothesis Good C
theorem g0b_orc_first (C : Circuit) (hG : Good C) (w g : ℕ) (h : Orc C w g) :
    w = 26 + g ∨ ∃ k b, w = 26 + k ∧ k < C.gates.length ∧ ¬ isAnd C k ∧
      Orc C (rd C (k, b)) g := by
  exact g0b_orc_first_lt C w g h (orc_bounds C hG w g h).1

theorem orc_first (C : Circuit) (hG : Good C) (w g : ℕ) (h : Orc C w g) :
    w = 26 + g ∨ ∃ k b, w = 26 + k ∧ k < C.gates.length ∧ ¬ isAnd C k ∧
      Orc C (rd C (k, b)) g := by
  exact g0b_orc_first C hG w g h

theorem orc_last (C : Circuit) (w g : ℕ) (h : Orc C w g) :
    w = 26 + g ∨ ∃ k b, Orc C w k ∧ k < C.gates.length ∧ ¬ isAnd C k ∧
      rd C (k, b) = 26 + g := by
  obtain ⟨k0, hw, hk0, hp⟩ := h
  rcases Relation.ReflTransGen.cases_tail hp with h1 | ⟨c, hkc, hcg⟩
  · left
    omega
  · right
    obtain ⟨hc, hor, hr | hr⟩ := hcg
    · exact ⟨c, false, ⟨k0, hw, hk0, hkc⟩, hc, hor, by rw [rd_false]; exact hr⟩
    · exact ⟨c, true, ⟨k0, hw, hk0, hkc⟩, hc, hor, by rw [rd_true]; exact hr⟩

theorem orc_trans (C : Circuit) (w k g : ℕ) (h1 : Orc C w k) (h2 : Orc C (26 + k) g) :
    Orc C w g := by
  obtain ⟨k0, hw, hk0, hp⟩ := h1
  obtain ⟨k1, hk1, _, hq⟩ := h2
  have hkk : k1 = k := by omega
  subst hkk
  exact ⟨k0, hw, hk0, hp.trans hq⟩

theorem orc_vl (C : Circuit) (hG : Good C) (w g : ℕ) (h : Orc C w g) (x : Fin 26 → Bool)
    (hx : vl C x (26 + g) = true) : vl C x w = true := by
  obtain ⟨k, hw, _, hp⟩ := h
  rw [hw]
  exact g0b_rtg_vl C hG x k g hp hx

theorem orc_acc (C : Circuit) (hG : Good C) (w g : ℕ) (h : Orc C w g) (u : Fin 26)
    (hu : acc C (26 + g) u) : acc C w u := by
  exact orc_vl C hG w g h (e1 u) hu

theorem orc_low (C : Circuit) (hG : Good C) (w g : ℕ) (h : Orc C w g) (hl : LowW C w) :
    LowW C (26 + g) := by
  intro u hu
  exact hl u (orc_acc C hG w g h u hu)

theorem orc_rtg (C : Circuit) (k g : ℕ) (h : Orc C (26 + k) g) :
    Relation.ReflTransGen (Rdv C) k g := by
  obtain ⟨k1, hk1, _, hp⟩ := h
  have hkk : k1 = k := by omega
  subst hkk
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ⟨hbc.1, hbc.2.2⟩

theorem orc_reach (C : Circuit) (j : ℕ) (b : Bool) (g : ℕ) (hj : j < C.gates.length)
    (h : Orc C (rd C (j, b)) g) : Relation.TransGen (Rdv C) j g := by
  obtain ⟨k1, hk1, hk1lt, hp⟩ := h
  have hr : Rdv C j k1 := by
    refine ⟨hj, ?_⟩
    cases b with
    | false =>
      rw [rd_false] at hk1
      exact Or.inl hk1
    | true =>
      rw [rd_true] at hk1
      exact Or.inr hk1
  exact Relation.TransGen.head' hr (orc_rtg C k1 g ⟨k1, rfl, hk1lt, hp⟩)

theorem rdv_lt (C : Circuit) (hG : Good C) (g k : ℕ) (h : Rdv C g k) : k < g := by
  obtain ⟨hg, h1 | h1⟩ := h
  · have h2 := good_hA C hG g hg
    omega
  · have h2 := good_hB C hG g hg
    omega

theorem tg_lt (C : Circuit) (hG : Good C) (g k : ℕ) (h : Relation.TransGen (Rdv C) g k) :
    k < g := by
  induction h with
  | single hab => exact rdv_lt C hG _ _ hab
  | tail _ hbc ih =>
    have h2 := rdv_lt C hG _ _ hbc
    omega

theorem fact1 (C : Circuit) (hG : Good C) (x : Fin 26 → Bool) (w : ℕ)
    (hw : w < 26 + C.gates.length) (hx : vl C x w = true) :
    (∃ u, acc C w u ∧ x u = true) ∨
      ∃ g, Orc C w g ∧ isAnd C g ∧ vl C x (26 + g) = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases wire_cases C w hw with ⟨u, rfl⟩ | ⟨j, hj, rfl⟩
    · left
      exact ⟨u, (sing_input C u u).mpr rfl, (vl_input C x u).symm.trans hx⟩
    · by_cases ha : isAnd C j
      · right
        exact ⟨j, orc_base C j hj, ha, hx⟩
      · rcases (vl_or C hG x j hj ha).mp hx with h1 | h1
        · have hlt := good_hA C hG j hj
          rcases ih (gA C j) hlt (by omega) h1 with ⟨u, hu, hxu⟩ | ⟨g, hg, hga, hgx⟩
          · left
            exact ⟨u, (acc_or C hG j hj ha u).mpr (Or.inl hu), hxu⟩
          · right
            refine ⟨g, orc_step C j false g hj ha ?_, hga, hgx⟩
            rw [rd_false]
            exact hg
        · have hlt := good_hB C hG j hj
          rcases ih (gB C j) hlt (by omega) h1 with ⟨u, hu, hxu⟩ | ⟨g, hg, hga, hgx⟩
          · left
            exact ⟨u, (acc_or C hG j hj ha u).mpr (Or.inr hu), hxu⟩
          · right
            refine ⟨g, orc_step C j true g hj ha ?_, hga, hgx⟩
            rw [rd_true]
            exact hg

theorem low_has_and (C : Circuit) (hG : Good C) (j : ℕ) (hj : j < C.gates.length)
    (hl : LowW C (26 + j)) : ∃ g, Orc C (26 + j) g ∧ isAnd C g := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases ha : isAnd C j
    · exact ⟨j, orc_base C j hj, ha⟩
    · have hlA : LowW C (gA C j) :=
        fun u hu => hl u ((acc_or C hG j hj ha u).mpr (Or.inl hu))
      have hlt := good_hA C hG j hj
      obtain ⟨j1, hj1, hjj⟩ := low_is_gate C (gA C j) (by omega) hlA
      have hlA1 : LowW C (26 + j1) := by
        rw [← hjj]
        exact hlA
      obtain ⟨g, hg, hga⟩ := ih j1 (by omega) hj1 hlA1
      refine ⟨g, orc_step C j false g hj ha ?_, hga⟩
      rw [rd_false, hjj]
      exact hg

-- GROUP C1 (local structure)
-- a nonempty property of naturals has a least witness
theorem c1_least (P : ℕ → Prop) (h : ∃ j, P j) : ∃ j, P j ∧ ∀ g, g < j → ¬ P g := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hlow : ∃ g, g < n ∧ P g
    · obtain ⟨g, hg, hPg⟩ := hlow
      exact ih g hg hPg
    · exact ⟨n, hn, fun g hg hPg => hlow ⟨g, hg, hPg⟩⟩

-- a wire that accepts t and is not Sing t accepts another single
theorem c1_not_sing (C : Circuit) (w : ℕ) (t : Fin 26) (ht : acc C w t)
    (hn : ¬ SingW C w t) : ∃ t' : Fin 26, acc C w t' ∧ t' ≠ t := by
  by_contra hcon
  apply hn
  intro u
  constructor
  · intro hu
    by_contra hne
    exact hcon ⟨u, hu, hne⟩
  · intro h
    rw [h]
    exact ht

theorem reach_lt (C : Circuit) (hG : Good C) (k : ℕ)
    (h : Relation.ReflTransGen (Rdv C) (oG C) k) : k < C.gates.length := by
  induction h with
  | refl => exact good_o C hG
  | tail _ hstep ih =>
    have hlt := rdv_lt C hG _ _ hstep
    omega

theorem reach_reader (C : Circuit) (hG : Good C) (k : ℕ)
    (h : Relation.ReflTransGen (Rdv C) (oG C) k) (hk : k ≠ oG C) :
    ∃ p : ℕ × Bool, Relation.ReflTransGen (Rdv C) (oG C) p.1 ∧ p.1 < C.gates.length ∧
      rd C p = 26 + k := by
  rcases Relation.ReflTransGen.cases_tail h with h0 | ⟨g, hg, hgk⟩
  · exact absurd h0 hk
  · have hgl : g < C.gates.length := reach_lt C hG g hg
    obtain ⟨_, h1 | h1⟩ := hgk
    · exact ⟨(g, false), hg, hgl, by rw [rd_false]; exact h1⟩
    · exact ⟨(g, true), hg, hgl, by rw [rd_true]; exact h1⟩

-- an operand of the least true AND gate accepts a single that is true at x
theorem c1_operand (C : Circuit) (hG : Good C) (x : Fin 26 → Bool) (j : ℕ) (b : Bool)
    (hjl : j < C.gates.length)
    (hjr : Relation.ReflTransGen (Rdv C) (oG C) j)
    (hmin : ∀ g, g < j → ¬ (g < C.gates.length ∧ isAnd C g ∧
      Relation.ReflTransGen (Rdv C) (oG C) g ∧ vl C x (26 + g) = true))
    (hx : vl C x (rd C (j, b)) = true) :
    ∃ a : Fin 26, acc C (rd C (j, b)) a ∧ x a = true := by
  have hlt : rd C (j, b) < 26 + j := rd_lt C hG (j, b) hjl
  rcases fact1 C hG x (rd C (j, b)) (by omega) hx with h | ⟨g, hg, hga, hgx⟩
  · exact h
  · exfalso
    have htg : Relation.TransGen (Rdv C) j g := orc_reach C j b g hjl hg
    have hgj : g < j := tg_lt C hG j g htg
    exact hmin g hgj ⟨(orc_bounds C hG _ _ hg).1, hga, hjr.trans htg.to_reflTransGen, hgx⟩

theorem owner_exists (C : Circuit) (hG : Good C) (e : Fin 26 × Fin 26) (he : e ∈ E26) :
    ∃ j, j < C.gates.length ∧ isAnd C j ∧ Relation.ReflTransGen (Rdv C) (oG C) j ∧
      ((acc C (gA C j) e.1 ∧ acc C (gB C j) e.2) ∨
        (acc C (gA C j) e.2 ∧ acc C (gB C j) e.1)) := by
  have hadj : adj e.1 e.2 := e26_adj e he
  have hout : vl C (e2 e.1 e.2) (26 + oG C) = true := good_acc C hG e.1 e.2 hadj
  have ho : oG C < C.gates.length := good_o C hG
  have hex : ∃ j, j < C.gates.length ∧ isAnd C j ∧
      Relation.ReflTransGen (Rdv C) (oG C) j ∧ vl C (e2 e.1 e.2) (26 + j) = true := by
    rcases fact1 C hG (e2 e.1 e.2) (26 + oG C) (by omega) hout with
      ⟨u, hu, _⟩ | ⟨g, hg, hga, hgx⟩
    · exact absurd hu (out_low C hG u)
    · exact ⟨g, (orc_bounds C hG _ _ hg).1, hga, orc_rtg C _ _ hg, hgx⟩
  obtain ⟨j, hjP, hmin⟩ := c1_least (fun j => j < C.gates.length ∧ isAnd C j ∧
      Relation.ReflTransGen (Rdv C) (oG C) j ∧ vl C (e2 e.1 e.2) (26 + j) = true) hex
  obtain ⟨hjl, hja, hjr, hjx⟩ := hjP
  have hAB := (vl_and C hG (e2 e.1 e.2) j hjl hja).mp hjx
  have hA : ∃ a : Fin 26, acc C (rd C (j, false)) a ∧ e2 e.1 e.2 a = true :=
    c1_operand C hG (e2 e.1 e.2) j false hjl hjr hmin (by rw [rd_false]; exact hAB.1)
  have hB : ∃ a : Fin 26, acc C (rd C (j, true)) a ∧ e2 e.1 e.2 a = true :=
    c1_operand C hG (e2 e.1 e.2) j true hjl hjr hmin (by rw [rd_true]; exact hAB.2)
  rw [rd_false] at hA
  rw [rd_true] at hB
  obtain ⟨a, haA, hax⟩ := hA
  obtain ⟨b, hbB, hbx⟩ := hB
  have hab : adj a b := fact2 C hG j hjl hja a b haA hbB
  have hne : a ≠ b := by
    intro h
    rw [h] at hab
    exact adj_irr b hab
  refine ⟨j, hjl, hja, hjr, ?_⟩
  rcases e2_mem e.1 e.2 a hax with ha1 | ha2
  · rcases e2_mem e.1 e.2 b hbx with hb1 | hb2
    · exact absurd (ha1.trans hb1.symm) hne
    · left
      rw [← ha1, ← hb2]
      exact ⟨haA, hbB⟩
  · rcases e2_mem e.1 e.2 b hbx with hb1 | hb2
    · right
      rw [← ha2, ← hb1]
      exact ⟨haA, hbB⟩
    · exact absurd (ha2.trans hb2.symm) hne

theorem star_side (C : Circuit) (hG : Good C) (j : ℕ) (hj : j < C.gates.length)
    (ha : isAnd C j) (u v : Fin 26) (hu : acc C (gA C j) u) (hv : acc C (gB C j) v) :
    SingW C (gA C j) u ∨ SingW C (gB C j) v := by
  by_contra hcon
  obtain ⟨hnA, hnB⟩ := not_or.mp hcon
  obtain ⟨u', hu', hneu⟩ := c1_not_sing C (gA C j) u hu hnA
  obtain ⟨v', hv', hnev⟩ := c1_not_sing C (gB C j) v hv hnB
  exact adj_c4 u u' v v' (Ne.symm hneu) (Ne.symm hnev)
    (fact2 C hG j hj ha u v hu hv) (fact2 C hG j hj ha u v' hu hv')
    (fact2 C hG j hj ha u' v hu' hv) (fact2 C hG j hj ha u' v' hu' hv')

theorem leaf_trace (C : Circuit) (hG : Good C) (w : ℕ) (hw : w < 26 + C.gates.length)
    (t : Fin 26) (ht : acc C w t) :
    SingW C w t ∨ ∃ g b, Orc C w g ∧ ¬ isAnd C g ∧ BigW C (26 + g) ∧
      SingW C (rd C (g, b)) t := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hs : SingW C w t
    · exact Or.inl hs
    · right
      obtain ⟨t', ht', hne⟩ := c1_not_sing C w t ht hs
      rcases wire_cases C w hw with ⟨u, hwu⟩ | ⟨k, hk, hwk⟩
      · exfalso
        rw [hwu] at ht ht'
        have h1 : t = u := (sing_input C u t).mp ht
        have h2 : t' = u := (sing_input C u t').mp ht'
        exact hne (h2.trans h1.symm)
      · subst hwk
        by_cases hand : isAnd C k
        · exact absurd ht (and_low C hG k hk hand t)
        · have hbig : BigW C (26 + k) := ⟨t, t', Ne.symm hne, ht, ht'⟩
          have hop : ∃ b : Bool, acc C (rd C (k, b)) t := by
            rcases (acc_or C hG k hk hand t).mp ht with hA | hB
            · exact ⟨false, by rw [rd_false]; exact hA⟩
            · exact ⟨true, by rw [rd_true]; exact hB⟩
          obtain ⟨b, hb⟩ := hop
          have hlt : rd C (k, b) < 26 + k := rd_lt C hG (k, b) hk
          rcases ih (rd C (k, b)) hlt (by omega) hb with hsb | ⟨g, b', hg, hga, hgb, hgs⟩
          · exact ⟨k, b, orc_base C k hk, hand, hbig, hsb⟩
          · exact ⟨g, b', orc_step C k b g hk hand hg, hga, hgb, hgs⟩

theorem sing_gate_pos (C : Circuit) (hG : Good C) (k : ℕ) (hk : k < C.gates.length)
    (t : Fin 26) (h : SingW C (26 + k) t) :
    ¬ isAnd C k ∧ ∃ b : Bool, SingW C (rd C (k, b)) t := by
  have hacc : acc C (26 + k) t := (h t).mpr rfl
  have hand : ¬ isAnd C k := fun ha => and_low C hG k hk ha t hacc
  refine ⟨hand, ?_⟩
  have hop : ∃ b : Bool, acc C (rd C (k, b)) t ∧
      ∀ u : Fin 26, acc C (rd C (k, b)) u → acc C (26 + k) u := by
    rcases (acc_or C hG k hk hand t).mp hacc with hA | hB
    · refine ⟨false, by rw [rd_false]; exact hA, ?_⟩
      intro u hu
      rw [rd_false] at hu
      exact (acc_or C hG k hk hand u).mpr (Or.inl hu)
    · refine ⟨true, by rw [rd_true]; exact hB, ?_⟩
      intro u hu
      rw [rd_true] at hu
      exact (acc_or C hG k hk hand u).mpr (Or.inr hu)
  obtain ⟨b, hb, hsub⟩ := hop
  refine ⟨b, ?_⟩
  intro u
  constructor
  · intro hu
    exact (h u).mp (hsub u hu)
  · intro hut
    rw [hut]
    exact hb

-- the tight structure of a circuit with at most 64 gates
def IsTight (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool) (cen : ℕ → Fin 26) :
    Prop :=
  (∀ e ∈ E26, own e < C.gates.length ∧ isAnd C (own e)) ∧
  (∀ e ∈ E26, SingW C (rd C (own e, cs (own e))) (cen (own e))) ∧
  (∀ e ∈ E26, (e.1 = cen (own e) ∧ acc C (rd C (own e, !(cs (own e)))) e.2) ∨
    (e.2 = cen (own e) ∧ acc C (rd C (own e, !(cs (own e)))) e.1)) ∧
  ((E26.image own).card = 13) ∧
  (∀ k, k < C.gates.length → k ≠ oG C → (¬ ∃ t, SingW C (26 + k) t) →
    ∃ p : ℕ × Bool, p.1 < C.gates.length ∧ rd C p = 26 + k ∧
      ∀ q : ℕ × Bool, q.1 < C.gates.length → rd C q = 26 + k → q = p) ∧
  (∀ q : ℕ × Bool, q.1 < C.gates.length → rd C q ≠ 26 + oG C) ∧
  (∀ q : ℕ × Bool, q.1 < C.gates.length → (∃ t, SingW C (rd C q) t) →
    (∃ t, SingW C (26 + q.1) t) ∨ (q.1 ∈ E26.image own ∧ q.2 = cs q.1) ∨
    (∃ e ∈ E26, (q.1 = own e ∧ q.2 = !(cs (own e))) ∨
      (¬ isAnd C q.1 ∧ BigW C (26 + q.1) ∧ Orc C (rd C (own e, !(cs (own e)))) q.1)))

theorem tight_own (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool)
    (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (e : Fin 26 × Fin 26) (he : e ∈ E26) :
    own e < C.gates.length ∧ isAnd C (own e) := hT.1 e he

theorem tight_cen (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool)
    (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (e : Fin 26 × Fin 26) (he : e ∈ E26) :
    SingW C (rd C (own e, cs (own e))) (cen (own e)) := hT.2.1 e he

theorem tight_leaf (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool)
    (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (e : Fin 26 × Fin 26) (he : e ∈ E26) :
    (e.1 = cen (own e) ∧ acc C (rd C (own e, !(cs (own e)))) e.2) ∨
      (e.2 = cen (own e) ∧ acc C (rd C (own e, !(cs (own e)))) e.1) := hT.2.2.1 e he

theorem tight_card (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool)
    (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) : (E26.image own).card = 13 :=
  hT.2.2.2.1

theorem tight_read (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool)
    (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (k : ℕ) (hk : k < C.gates.length)
    (hko : k ≠ oG C) (hns : ¬ ∃ t, SingW C (26 + k) t) :
    ∃ p : ℕ × Bool, p.1 < C.gates.length ∧ rd C p = 26 + k ∧
      ∀ q : ℕ × Bool, q.1 < C.gates.length → rd C q = 26 + k → q = p :=
  hT.2.2.2.2.1 k hk hko hns

theorem tight_out (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool)
    (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (q : ℕ × Bool)
    (hq : q.1 < C.gates.length) : rd C q ≠ 26 + oG C := hT.2.2.2.2.2.1 q hq

theorem tight_sing (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool)
    (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (q : ℕ × Bool)
    (hq : q.1 < C.gates.length) (hs : ∃ t, SingW C (rd C q) t) :
    (∃ t, SingW C (26 + q.1) t) ∨ (q.1 ∈ E26.image own ∧ q.2 = cs q.1) ∨
    (∃ e ∈ E26, (q.1 = own e ∧ q.2 = !(cs (own e))) ∨
      (¬ isAnd C q.1 ∧ BigW C (26 + q.1) ∧ Orc C (rd C (own e, !(cs (own e)))) q.1)) :=
  hT.2.2.2.2.2.2 q hq hs

-- GROUP G1 (the count)
-- small facts about Sing / Low / Big wires
theorem g1_sing_eq (C : Circuit) (w : ℕ) (t u : Fin 26) (h : SingW C w t) (hu : acc C w u) :
    u = t := (h u).mp hu

theorem g1_sing_self (C : Circuit) (w : ℕ) (t : Fin 26) (h : SingW C w t) : acc C w t :=
  (h t).mpr rfl

theorem g1_low_not_sing (C : Circuit) (w : ℕ) (hl : LowW C w) : ¬ ∃ t, SingW C w t := by
  rintro ⟨t, ht⟩
  exact hl t (g1_sing_self C w t ht)

theorem g1_sing_not_big (C : Circuit) (w : ℕ) (hs : ∃ t, SingW C w t) : ¬ BigW C w := by
  obtain ⟨t, ht⟩ := hs
  rintro ⟨t1, t2, hne, h1, h2⟩
  exact hne ((g1_sing_eq C w t t1 ht h1).trans (g1_sing_eq C w t t2 ht h2).symm)

theorem g1_bnot_ne (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

-- the choices: owner of an edge, centre side and centre of a gate
noncomputable def g1_own (C : Circuit) (e : Fin 26 × Fin 26) : ℕ :=
  Classical.epsilon (fun j : ℕ => j < C.gates.length ∧ isAnd C j ∧
    Relation.ReflTransGen (Rdv C) (oG C) j ∧
    ((acc C (gA C j) e.1 ∧ acc C (gB C j) e.2) ∨ (acc C (gA C j) e.2 ∧ acc C (gB C j) e.1)))

theorem g1_own_spec (C : Circuit) (hG : Good C) (e : Fin 26 × Fin 26) (he : e ∈ E26) :
    g1_own C e < C.gates.length ∧ isAnd C (g1_own C e) ∧
    Relation.ReflTransGen (Rdv C) (oG C) (g1_own C e) ∧
    ((acc C (gA C (g1_own C e)) e.1 ∧ acc C (gB C (g1_own C e)) e.2) ∨
      (acc C (gA C (g1_own C e)) e.2 ∧ acc C (gB C (g1_own C e)) e.1)) :=
  Classical.epsilon_spec (owner_exists C hG e he)

noncomputable def g1_cs (C : Circuit) (j : ℕ) : Bool :=
  Classical.epsilon (fun b : Bool => ∃ t, SingW C (rd C (j, b)) t)

noncomputable def g1_cen (C : Circuit) (j : ℕ) : Fin 26 :=
  Classical.epsilon (fun t : Fin 26 => SingW C (rd C (j, g1_cs C j)) t)

theorem g1_cs_spec (C : Circuit) (j : ℕ) (h : ∃ b : Bool, ∃ t, SingW C (rd C (j, b)) t) :
    SingW C (rd C (j, g1_cs C j)) (g1_cen C j) := by
  have h1 : ∃ t, SingW C (rd C (j, g1_cs C j)) t := Classical.epsilon_spec h
  exact Classical.epsilon_spec h1

theorem g1_owner_sing (C : Circuit) (hG : Good C) (e : Fin 26 × Fin 26) (he : e ∈ E26) :
    SingW C (rd C (g1_own C e, g1_cs C (g1_own C e))) (g1_cen C (g1_own C e)) := by
  obtain ⟨hj, ha, _, h⟩ := g1_own_spec C hG e he
  apply g1_cs_spec
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases star_side C hG _ hj ha _ _ h1 h2 with h3 | h3
    · exact ⟨false, _, by rw [rd_false]; exact h3⟩
    · exact ⟨true, _, by rw [rd_true]; exact h3⟩
  · rcases star_side C hG _ hj ha _ _ h1 h2 with h3 | h3
    · exact ⟨false, _, by rw [rd_false]; exact h3⟩
    · exact ⟨true, _, by rw [rd_true]; exact h3⟩

theorem g1_pos_cases (C : Circuit) (j : ℕ) (b : Bool) (c u v : Fin 26)
    (hs : SingW C (rd C (j, b)) c) (hu : acc C (gA C j) u) (hv : acc C (gB C j) v) :
    (u = c ∧ acc C (rd C (j, !b)) v) ∨ (v = c ∧ acc C (rd C (j, !b)) u) := by
  cases b with
  | false =>
    rw [rd_false] at hs
    refine Or.inl ⟨g1_sing_eq C _ c u hs hu, ?_⟩
    show acc C (rd C (j, true)) v
    rw [rd_true]
    exact hv
  | true =>
    rw [rd_true] at hs
    refine Or.inr ⟨g1_sing_eq C _ c v hs hv, ?_⟩
    show acc C (rd C (j, false)) u
    rw [rd_false]
    exact hu

theorem g1_owner_leaf (C : Circuit) (hG : Good C) (e : Fin 26 × Fin 26) (he : e ∈ E26) :
    (e.1 = g1_cen C (g1_own C e) ∧ acc C (rd C (g1_own C e, !(g1_cs C (g1_own C e)))) e.2) ∨
    (e.2 = g1_cen C (g1_own C e) ∧ acc C (rd C (g1_own C e, !(g1_cs C (g1_own C e)))) e.1) := by
  have hs := g1_owner_sing C hG e he
  obtain ⟨_, _, _, h⟩ := g1_own_spec C hG e he
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact g1_pos_cases C _ _ _ _ _ hs h1 h2
  · exact (g1_pos_cases C _ _ _ _ _ hs h1 h2).symm

theorem g1_and_adj (C : Circuit) (hG : Good C) (j : ℕ) (hj : j < C.gates.length)
    (ha : isAnd C j) (b : Bool) (c t : Fin 26) (hs : SingW C (rd C (j, b)) c)
    (ht : acc C (rd C (j, !b)) t) : adj c t := by
  cases b with
  | false =>
    rw [rd_false] at hs
    have ht' : acc C (gB C j) t := by
      rw [← rd_true]
      exact ht
    exact fact2 C hG j hj ha c t (g1_sing_self C _ c hs) ht'
  | true =>
    rw [rd_true] at hs
    have ht' : acc C (gA C j) t := by
      rw [← rd_false]
      exact ht
    exact adj_symm _ _ (fact2 C hG j hj ha t c ht' (g1_sing_self C _ c hs))

-- the position charged to an edge: it reads the Sing wire of the leaf end of the edge
def g1_LamP (C : Circuit) (e : Fin 26 × Fin 26) (p : ℕ × Bool) : Prop :=
  (∃ t, SingW C (rd C p) t ∧
    ((e.1 = g1_cen C (g1_own C e) ∧ t = e.2) ∨ (e.2 = g1_cen C (g1_own C e) ∧ t = e.1))) ∧
  (p = (g1_own C e, !(g1_cs C (g1_own C e))) ∨
    (¬ isAnd C p.1 ∧ BigW C (26 + p.1) ∧
      Orc C (rd C (g1_own C e, !(g1_cs C (g1_own C e)))) p.1))

noncomputable def g1_lam (C : Circuit) (e : Fin 26 × Fin 26) : ℕ × Bool :=
  Classical.epsilon (g1_LamP C e)

theorem g1_lam_spec (C : Circuit) (hG : Good C) (e : Fin 26 × Fin 26) (he : e ∈ E26) :
    g1_LamP C e (g1_lam C e) := by
  obtain ⟨hj, _, _, _⟩ := g1_own_spec C hG e he
  have hlt0 : rd C (g1_own C e, !(g1_cs C (g1_own C e))) < 26 + g1_own C e :=
    rd_lt C hG (g1_own C e, !(g1_cs C (g1_own C e))) hj
  have hlt : rd C (g1_own C e, !(g1_cs C (g1_own C e))) < 26 + C.gates.length := by
    omega
  have key : ∀ t : Fin 26, acc C (rd C (g1_own C e, !(g1_cs C (g1_own C e)))) t →
      ((e.1 = g1_cen C (g1_own C e) ∧ t = e.2) ∨ (e.2 = g1_cen C (g1_own C e) ∧ t = e.1)) →
      ∃ p, g1_LamP C e p := by
    intro t ht hc
    rcases leaf_trace C hG _ hlt t ht with h | ⟨g, b, h1, h2, h3, h4⟩
    · exact ⟨(g1_own C e, !(g1_cs C (g1_own C e))), ⟨t, h, hc⟩, Or.inl rfl⟩
    · exact ⟨(g, b), ⟨t, h4, hc⟩, Or.inr ⟨h2, h3, h1⟩⟩
  have hex : ∃ p, g1_LamP C e p := by
    rcases g1_owner_leaf C hG e he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key e.2 h2 (Or.inl ⟨h1, rfl⟩)
    · exact key e.1 h2 (Or.inr ⟨h1, rfl⟩)
  exact Classical.epsilon_spec hex

theorem g1_lam_reach (C : Circuit) (hG : Good C) (e : Fin 26 × Fin 26) (he : e ∈ E26) :
    Relation.ReflTransGen (Rdv C) (oG C) (g1_lam C e).1 := by
  obtain ⟨hj, _, hr, _⟩ := g1_own_spec C hG e he
  obtain ⟨_, h | ⟨_, _, h⟩⟩ := g1_lam_spec C hG e he
  · rw [h]
    exact hr
  · exact hr.trans (orc_reach C _ _ _ hj h).to_reflTransGen

theorem g1_lam_inj (C : Circuit) (hG : Good C) (e e' : Fin 26 × Fin 26) (he : e ∈ E26)
    (he' : e' ∈ E26) (h : g1_lam C e = g1_lam C e') : e = e' := by
  obtain ⟨⟨t, hts, htc⟩, hp⟩ := g1_lam_spec C hG e he
  obtain ⟨⟨t', hts', htc'⟩, hp'⟩ := g1_lam_spec C hG e' he'
  rw [← h] at hts' hp'
  have htt : t' = t := g1_sing_eq C _ t t' hts (g1_sing_self C _ t' hts')
  obtain ⟨hj, ha, _, _⟩ := g1_own_spec C hG e he
  obtain ⟨hj', ha', _, _⟩ := g1_own_spec C hG e' he'
  have hcc : g1_cen C (g1_own C e) = g1_cen C (g1_own C e') := by
    rcases hp with hp | ⟨hna, hb, ho⟩
    · rcases hp' with hp' | ⟨hna', _, _⟩
      · have hoo : g1_own C e = g1_own C e' := congrArg Prod.fst (hp.symm.trans hp')
        rw [hoo]
      · rw [hp] at hna'
        exact absurd ha hna'
    · rcases hp' with hp' | ⟨_, _, ho'⟩
      · rw [hp'] at hna
        exact absurd ha' hna
      · by_contra hne
        obtain ⟨t1, t2, h12, a1, a2⟩ := hb
        have s := g1_owner_sing C hG e he
        have s' := g1_owner_sing C hG e' he'
        exact adj_c4 _ _ t1 t2 hne h12
          (g1_and_adj C hG _ hj ha _ _ _ s (orc_acc C hG _ _ ho t1 a1))
          (g1_and_adj C hG _ hj ha _ _ _ s (orc_acc C hG _ _ ho t2 a2))
          (g1_and_adj C hG _ hj' ha' _ _ _ s' (orc_acc C hG _ _ ho' t1 a1))
          (g1_and_adj C hG _ hj' ha' _ _ _ s' (orc_acc C hG _ _ ho' t2 a2))
  apply e26_orient e e' he he'
  rcases htc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases htc' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact Or.inl ⟨h1.trans (hcc.trans h1'.symm), h2.symm.trans (htt.symm.trans h2')⟩
  · exact Or.inr ⟨h1.trans (hcc.trans h1'.symm), h2.symm.trans (htt.symm.trans h2')⟩
  · exact Or.inr ⟨h2.symm.trans (htt.symm.trans h2'), h1.trans (hcc.trans h1'.symm)⟩
  · exact Or.inl ⟨h2.symm.trans (htt.symm.trans h2'), h1.trans (hcc.trans h1'.symm)⟩

-- the reader of a reachable gate
noncomputable def g1_rho (C : Circuit) (k : ℕ) : ℕ × Bool :=
  Classical.epsilon (fun p : ℕ × Bool => Relation.ReflTransGen (Rdv C) (oG C) p.1 ∧
    p.1 < C.gates.length ∧ rd C p = 26 + k)

theorem g1_rho_spec (C : Circuit) (hG : Good C) (k : ℕ)
    (h : Relation.ReflTransGen (Rdv C) (oG C) k) (hk : k ≠ oG C) :
    Relation.ReflTransGen (Rdv C) (oG C) (g1_rho C k).1 ∧
      (g1_rho C k).1 < C.gates.length ∧ rd C (g1_rho C k) = 26 + k :=
  Classical.epsilon_spec (reach_reader C hG k h hk)

-- the finite sets of the count
noncomputable def g1_S (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter
    (fun k => Relation.ReflTransGen (Rdv C) (oG C) k)

theorem g1_mem_S (C : Circuit) (hG : Good C) (k : ℕ) :
    k ∈ g1_S C ↔ Relation.ReflTransGen (Rdv C) (oG C) k := by
  classical
  unfold g1_S
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨reach_lt C hG k h, h⟩⟩

noncomputable def g1_I1 (C : Circuit) : Finset ℕ := by
  classical
  exact (g1_S C).filter (fun k => k ≠ oG C ∧ ¬ ∃ t, SingW C (26 + k) t)

noncomputable def g1_I2 (C : Circuit) : Finset ℕ := by
  classical
  exact (g1_S C).filter (fun k => ∃ t, SingW C (26 + k) t)

theorem g1_mem_I1 (C : Circuit) (k : ℕ) :
    k ∈ g1_I1 C ↔ k ∈ g1_S C ∧ k ≠ oG C ∧ ¬ ∃ t, SingW C (26 + k) t := by
  classical
  unfold g1_I1
  rw [Finset.mem_filter]

theorem g1_mem_I2 (C : Circuit) (k : ℕ) :
    k ∈ g1_I2 C ↔ k ∈ g1_S C ∧ ∃ t, SingW C (26 + k) t := by
  classical
  unfold g1_I2
  rw [Finset.mem_filter]

theorem g1_card_S (C : Circuit) (hG : Good C) :
    (g1_S C).card = (g1_I1 C).card + (g1_I2 C).card + 1 := by
  classical
  have hdisj : Disjoint (g1_I1 C) (g1_I2 C) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    exact ((g1_mem_I1 C k).mp h1).2.2 ((g1_mem_I2 C k).mp h2).2
  have hno : oG C ∉ g1_I1 C ∪ g1_I2 C := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact ((g1_mem_I1 C _).mp h).2.1 rfl
    · exact g1_low_not_sing C _ (out_low C hG) ((g1_mem_I2 C _).mp h).2
  have heq : g1_S C = insert (oG C) (g1_I1 C ∪ g1_I2 C) := by
    ext k
    rw [Finset.mem_insert, Finset.mem_union, g1_mem_I1, g1_mem_I2]
    constructor
    · intro hk
      by_cases h1 : k = oG C
      · exact Or.inl h1
      · by_cases h2 : ∃ t, SingW C (26 + k) t
        · exact Or.inr (Or.inr ⟨hk, h2⟩)
        · exact Or.inr (Or.inl ⟨hk, h1, h2⟩)
    · rintro (h | h | h)
      · subst h
        exact (g1_mem_S C hG _).mpr Relation.ReflTransGen.refl
      · exact h.1
      · exact h.1
  rw [heq, Finset.card_insert_of_notMem hno, Finset.card_union_of_disjoint hdisj]

theorem g1_card_A (C : Circuit) (hG : Good C) : 13 ≤ (E26.image (g1_own C)).card := by
  have hK : ∀ e ∈ E26, e.1 ∈ (E26.image (g1_own C)).image (g1_cen C) ∨
      e.2 ∈ (E26.image (g1_own C)).image (g1_cen C) := by
    intro e he
    have hm : g1_cen C (g1_own C e) ∈ (E26.image (g1_own C)).image (g1_cen C) :=
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ he)
    rcases g1_owner_leaf C hG e he with ⟨h1, _⟩ | ⟨h1, _⟩
    · refine Or.inl ?_
      rw [h1]
      exact hm
    · refine Or.inr ?_
      rw [h1]
      exact hm
  exact (cover13 _ hK).trans Finset.card_image_le

noncomputable def g1_Z1 (C : Circuit) : Finset (ℕ × Bool) := (g1_I1 C).image (g1_rho C)

noncomputable def g1_Z2 (C : Circuit) : Finset (ℕ × Bool) :=
  (g1_I2 C ∪ E26.image (g1_own C)).image (fun k : ℕ => (k, g1_cs C k))

noncomputable def g1_Z4 (C : Circuit) : Finset (ℕ × Bool) := E26.image (g1_lam C)

noncomputable def g1_Z (C : Circuit) : Finset (ℕ × Bool) :=
  g1_S C ×ˢ (Finset.univ : Finset Bool)

theorem g1_mem_Z (C : Circuit) (q : ℕ × Bool) : q ∈ g1_Z C ↔ q.1 ∈ g1_S C := by
  unfold g1_Z
  rw [Finset.mem_product]
  exact ⟨fun h => h.1, fun h => ⟨h, Finset.mem_univ _⟩⟩

theorem g1_card_Z (C : Circuit) : (g1_Z C).card = (g1_S C).card * 2 := by
  unfold g1_Z
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]

theorem g1_Z1_prop (C : Circuit) (hG : Good C) (q : ℕ × Bool) (hq : q ∈ g1_Z1 C) :
    ∃ k, k ∈ g1_I1 C ∧ q = g1_rho C k ∧ rd C q = 26 + k ∧
      Relation.ReflTransGen (Rdv C) (oG C) q.1 := by
  unfold g1_Z1 at hq
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
  have hk1 := (g1_mem_I1 C k).mp hk
  have r := g1_rho_spec C hG k ((g1_mem_S C hG k).mp hk1.1) hk1.2.1
  exact ⟨k, hk, rfl, r.2.2, r.1⟩

theorem g1_Z1_nsing (C : Circuit) (hG : Good C) (q : ℕ × Bool) (hq : q ∈ g1_Z1 C) :
    ¬ ∃ t, SingW C (rd C q) t := by
  obtain ⟨k, hk, _, hr, _⟩ := g1_Z1_prop C hG q hq
  rw [hr]
  exact ((g1_mem_I1 C k).mp hk).2.2

theorem g1_Z2_prop (C : Circuit) (hG : Good C) (q : ℕ × Bool) (hq : q ∈ g1_Z2 C) :
    q.2 = g1_cs C q.1 ∧ SingW C (rd C q) (g1_cen C q.1) ∧
      ((q.1 ∈ g1_S C ∧ ∃ t, SingW C (26 + q.1) t) ∨ q.1 ∈ E26.image (g1_own C)) := by
  unfold g1_Z2 at hq
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp hk with h | h
  · have h2 := (g1_mem_I2 C k).mp h
    obtain ⟨t, ht⟩ := h2.2
    have hlt := reach_lt C hG k ((g1_mem_S C hG k).mp h2.1)
    obtain ⟨_, b, hb⟩ := sing_gate_pos C hG k hlt t ht
    exact ⟨rfl, g1_cs_spec C k ⟨b, t, hb⟩, Or.inl h2⟩
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
    exact ⟨rfl, g1_owner_sing C hG e he, Or.inr (Finset.mem_image_of_mem _ he)⟩

theorem g1_Z4_sing (C : Circuit) (hG : Good C) (q : ℕ × Bool) (hq : q ∈ g1_Z4 C) :
    ∃ t, SingW C (rd C q) t := by
  unfold g1_Z4 at hq
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨⟨t, ht, _⟩, _⟩ := g1_lam_spec C hG e he
  exact ⟨t, ht⟩

theorem g1_card_Z1 (C : Circuit) (hG : Good C) : (g1_Z1 C).card = (g1_I1 C).card := by
  unfold g1_Z1
  apply Finset.card_image_of_injOn
  intro k hk k' hk' h
  have hk1 := (g1_mem_I1 C k).mp (Finset.mem_coe.mp hk)
  have hk1' := (g1_mem_I1 C k').mp (Finset.mem_coe.mp hk')
  have r := (g1_rho_spec C hG k ((g1_mem_S C hG k).mp hk1.1) hk1.2.1).2.2
  have r' := (g1_rho_spec C hG k' ((g1_mem_S C hG k').mp hk1'.1) hk1'.2.1).2.2
  have h' : g1_rho C k = g1_rho C k' := h
  rw [h'] at r
  omega

theorem g1_card_Z2 (C : Circuit) (hG : Good C) :
    (g1_Z2 C).card = (g1_I2 C).card + (E26.image (g1_own C)).card := by
  have hinj : Function.Injective (fun k : ℕ => (k, g1_cs C k)) :=
    fun k k' h => congrArg Prod.fst h
  have hdisj : Disjoint (g1_I2 C) (E26.image (g1_own C)) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h2
    obtain ⟨hj, ha, _, _⟩ := g1_own_spec C hG e he
    exact g1_low_not_sing C _ (and_low C hG _ hj ha) ((g1_mem_I2 C _).mp h1).2
  unfold g1_Z2
  rw [Finset.card_image_of_injective _ hinj, Finset.card_union_of_disjoint hdisj]

theorem g1_card_Z4 (C : Circuit) (hG : Good C) : (g1_Z4 C).card = 52 := by
  unfold g1_Z4
  rw [Finset.card_image_of_injOn, e26_card]
  intro e he e' he' h
  exact g1_lam_inj C hG e e' (Finset.mem_coe.mp he) (Finset.mem_coe.mp he') h

theorem g1_disj24 (C : Circuit) (hG : Good C) : Disjoint (g1_Z2 C) (g1_Z4 C) := by
  rw [Finset.disjoint_left]
  intro q h2 h4
  obtain ⟨hcs, _, hq⟩ := g1_Z2_prop C hG q h2
  unfold g1_Z4 at h4
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h4
  obtain ⟨_, hp | ⟨hna, hb, _⟩⟩ := g1_lam_spec C hG e he
  · rw [hp] at hcs
    exact g1_bnot_ne _ hcs
  · rcases hq with ⟨_, hs⟩ | hq
    · exact g1_sing_not_big C _ hs hb
    · obtain ⟨e', he', hee⟩ := Finset.mem_image.mp hq
      rw [← hee] at hna
      exact hna (g1_own_spec C hG e' he').2.1

theorem g1_card_U (C : Circuit) (hG : Good C) :
    (g1_Z1 C ∪ g1_Z2 C ∪ g1_Z4 C).card =
      (g1_I1 C).card + ((g1_I2 C).card + (E26.image (g1_own C)).card) + 52 := by
  have d12 : Disjoint (g1_Z1 C) (g1_Z2 C) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    exact g1_Z1_nsing C hG q h1 ⟨_, (g1_Z2_prop C hG q h2).2.1⟩
  have d14 : Disjoint (g1_Z1 C) (g1_Z4 C) := by
    rw [Finset.disjoint_left]
    intro q h1 h4
    exact g1_Z1_nsing C hG q h1 (g1_Z4_sing C hG q h4)
  have d24 := g1_disj24 C hG
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d14, d24⟩),
    Finset.card_union_of_disjoint d12, g1_card_Z1 C hG, g1_card_Z2 C hG, g1_card_Z4 C hG]

theorem g1_U_sub (C : Circuit) (hG : Good C) : g1_Z1 C ∪ g1_Z2 C ∪ g1_Z4 C ⊆ g1_Z C := by
  intro q hq
  rw [g1_mem_Z, g1_mem_S C hG]
  rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨k, _, _, _, hr⟩ := g1_Z1_prop C hG q hq
      exact hr
    · obtain ⟨_, _, h | h⟩ := g1_Z2_prop C hG q hq
      · exact (g1_mem_S C hG _).mp h.1
      · obtain ⟨e, he, hee⟩ := Finset.mem_image.mp h
        rw [← hee]
        exact (g1_own_spec C hG e he).2.2.1
  · unfold g1_Z4 at hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
    exact g1_lam_reach C hG e he

-- the count: 13 owners, every gate is reachable, every position lies in one family
theorem g1_count (C : Circuit) (hG : Good C) (hs : C.gates.length ≤ 64) :
    (E26.image (g1_own C)).card = 13 ∧ (∀ k, k < C.gates.length → k ∈ g1_S C) ∧
      (∀ q : ℕ × Bool, q.1 < C.gates.length → q ∈ g1_Z1 C ∪ g1_Z2 C ∪ g1_Z4 C) := by
  have h1 := g1_card_U C hG
  have h2 := Finset.card_le_card (g1_U_sub C hG)
  have h3 := g1_card_Z C
  have h4 := g1_card_S C hG
  have h5 := g1_card_A C hG
  have hsub : g1_S C ⊆ Finset.range C.gates.length := by
    intro k hk
    exact Finset.mem_range.mpr (reach_lt C hG k ((g1_mem_S C hG k).mp hk))
  have h6 := Finset.card_le_card hsub
  rw [Finset.card_range] at h6
  have hA : (E26.image (g1_own C)).card = 13 := by omega
  have hS : g1_S C = Finset.range C.gates.length :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range]; omega)
  have hU : g1_Z1 C ∪ g1_Z2 C ∪ g1_Z4 C = g1_Z C :=
    Finset.eq_of_subset_of_card_le (g1_U_sub C hG) (by omega)
  refine ⟨hA, ?_, ?_⟩
  · intro k hk
    rw [hS]
    exact Finset.mem_range.mpr hk
  · intro q hq
    rw [hU, g1_mem_Z, hS]
    exact Finset.mem_range.mpr hq

theorem tight_exists (C : Circuit) (hG : Good C) (hs : C.gates.length ≤ 64) :
    ∃ (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool) (cen : ℕ → Fin 26),
      IsTight C own cs cen := by
  obtain ⟨hA, hS, hU⟩ := g1_count C hG hs
  refine ⟨g1_own C, g1_cs C, g1_cen C, ?_, ?_, ?_, hA, ?_, ?_, ?_⟩
  · intro e he
    exact ⟨(g1_own_spec C hG e he).1, (g1_own_spec C hG e he).2.1⟩
  · intro e he
    exact g1_owner_sing C hG e he
  · intro e he
    exact g1_owner_leaf C hG e he
  · intro k hk hko hns
    have r := g1_rho_spec C hG k ((g1_mem_S C hG k).mp (hS k hk)) hko
    refine ⟨g1_rho C k, r.2.1, r.2.2, ?_⟩
    intro q hq hrq
    rcases Finset.mem_union.mp (hU q hq) with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨k', _, hqk, hr', _⟩ := g1_Z1_prop C hG q h
        have hkk : k' = k := by omega
        rw [hqk, hkk]
      · have hsq : ∃ t, SingW C (rd C q) t := ⟨_, (g1_Z2_prop C hG q h).2.1⟩
        rw [hrq] at hsq
        exact absurd hsq hns
    · have hsq : ∃ t, SingW C (rd C q) t := g1_Z4_sing C hG q h
      rw [hrq] at hsq
      exact absurd hsq hns
  · intro q hq hrq
    have hns : ¬ ∃ t, SingW C (26 + oG C) t := g1_low_not_sing C _ (out_low C hG)
    rcases Finset.mem_union.mp (hU q hq) with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨k', hk', _, hr', _⟩ := g1_Z1_prop C hG q h
        have hkk : k' = oG C := by omega
        exact ((g1_mem_I1 C k').mp hk').2.1 hkk
      · have hsq : ∃ t, SingW C (rd C q) t := ⟨_, (g1_Z2_prop C hG q h).2.1⟩
        rw [hrq] at hsq
        exact hns hsq
    · have hsq : ∃ t, SingW C (rd C q) t := g1_Z4_sing C hG q h
      rw [hrq] at hsq
      exact hns hsq
  · intro q hq hsq
    rcases Finset.mem_union.mp (hU q hq) with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact absurd hsq (g1_Z1_nsing C hG q h)
      · obtain ⟨hcs, _, h' | h'⟩ := g1_Z2_prop C hG q h
        · exact Or.inl h'.2
        · exact Or.inr (Or.inl ⟨h', hcs⟩)
    · unfold g1_Z4 at h
      obtain ⟨e, he, hqe⟩ := Finset.mem_image.mp h
      obtain ⟨_, hp⟩ := g1_lam_spec C hG e he
      rw [hqe] at hp
      refine Or.inr (Or.inr ⟨e, he, ?_⟩)
      rcases hp with hp | hp
      · exact Or.inl ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
      · exact Or.inr hp

-- GROUP G2 (consequences of tightness)
theorem owner_leaf_adj (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (e : Fin 26 × Fin 26) (he : e ∈ E26) (t : Fin 26)
    (ht : acc C (rd C (own e, !(cs (own e)))) t) : adj (cen (own e)) t := by
  obtain ⟨hj, ha⟩ := tight_own C own cs cen hT e he
  have hc := tight_cen C own cs cen hT e he
  have hacc : acc C (rd C (own e, cs (own e))) (cen (own e)) := (hc (cen (own e))).mpr rfl
  have key : ∀ b : Bool, acc C (rd C (own e, b)) (cen (own e)) →
      acc C (rd C (own e, !b)) t → adj (cen (own e)) t := by
    intro b h1 h2
    cases b with
    | false =>
      rw [rd_false] at h1
      have h2' : acc C (gB C (own e)) t := by
        rw [← rd_true]
        exact h2
      exact fact2 C hG (own e) hj ha _ _ h1 h2'
    | true =>
      rw [rd_true] at h1
      have h2' : acc C (gA C (own e)) t := by
        rw [← rd_false]
        exact h2
      exact adj_symm _ _ (fact2 C hG (own e) hj ha _ _ h2' h1)
  exact key (cs (own e)) hacc ht

-- a Sing wire is not Big
theorem g2_sing_not_big (C : Circuit) (w : ℕ) (t : Fin 26) (hs : SingW C w t)
    (hb : BigW C w) : False := by
  obtain ⟨t1, t2, hne, h1, h2⟩ := hb
  exact hne (((hs t1).mp h1).trans ((hs t2).mp h2).symm)

-- the reader position of a non-Sing gate k lying in the OR closure of a leaf operand:
-- it is the leaf position itself, or a position of an OR gate of that closure
theorem g2_reader (C : Circuit) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (k : ℕ) (hk : k < C.gates.length) (hns : ¬ ∃ t, SingW C (26 + k) t)
    (q : ℕ × Bool) (hq : q.1 < C.gates.length) (hrq : rd C q = 26 + k)
    (e : Fin 26 × Fin 26) (he : e ∈ E26)
    (ho : Orc C (rd C (own e, !(cs (own e)))) k) :
    q = (own e, !(cs (own e))) ∨
      (¬ isAnd C q.1 ∧ Orc C (rd C (own e, !(cs (own e)))) q.1) := by
  have hko : k ≠ oG C := by
    intro h
    apply tight_out C own cs cen hT q hq
    rw [hrq, h]
  obtain ⟨p, _, _, hp3⟩ := tight_read C own cs cen hT k hk hko hns
  have hqp : q = p := hp3 q hq hrq
  rcases orc_last C _ _ ho with h | ⟨k2, b2, h1, h2, h3, h4⟩
  · left
    have h5 : (own e, !(cs (own e))) = p :=
      hp3 (own e, !(cs (own e))) (tight_own C own cs cen hT e he).1 h
    rw [hqp, h5]
  · right
    have h5 : (k2, b2) = p := hp3 (k2, b2) h2 h4
    have hq1 : q.1 = k2 := by
      rw [hqp, ← h5]
    rw [hq1]
    exact ⟨h3, h1⟩

-- the U-lemma: every Big gate lies in the OR closure of the leaf operand of some owner
theorem g2_big_in_leaf (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (w : ℕ) (hw : w < C.gates.length) (hb : BigW C (26 + w)) :
    ∃ e ∈ E26, Orc C (rd C (own e, !(cs (own e)))) w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    have hor : ¬ isAnd C w := by
      intro ha
      obtain ⟨t1, _, _, h1, _⟩ := hb
      exact and_low C hG w hw ha t1 h1
    have hown : ∀ e ∈ E26, w ≠ own e := by
      intro e he h
      apply hor
      rw [h]
      exact (tight_own C own cs cen hT e he).2
    by_cases hs : ∃ b : Bool, ∃ t, SingW C (rd C (w, b)) t
    · obtain ⟨b, hs⟩ := hs
      rcases tight_sing C own cs cen hT (w, b) hw hs with
        ⟨t, h1⟩ | ⟨h1, _⟩ | ⟨e, he, ⟨h1, _⟩ | ⟨_, _, h1⟩⟩
      · exact (g2_sing_not_big C (26 + w) t h1 hb).elim
      · obtain ⟨e, he, h2⟩ := Finset.mem_image.mp h1
        exact absurd h2.symm (hown e he)
      · exact absurd h1 (hown e he)
      · exact ⟨e, he, h1⟩
    · obtain ⟨t1, _, _, h1, _⟩ := hb
      have hop : ∃ b : Bool, acc C (rd C (w, b)) t1 := by
        rcases (acc_or C hG w hw hor t1).mp h1 with h | h
        · exact ⟨false, by rw [rd_false]; exact h⟩
        · exact ⟨true, by rw [rd_true]; exact h⟩
      obtain ⟨b, hacc⟩ := hop
      have hns : ¬ ∃ t, SingW C (rd C (w, b)) t := fun h => hs ⟨b, h⟩
      have hlt : rd C (w, b) < 26 + w := rd_lt C hG (w, b) hw
      rcases wire_cases C (rd C (w, b)) (by omega) with ⟨u, hu⟩ | ⟨k, hk, hk2⟩
      · exact absurd ⟨u, by rw [hu]; exact sing_input C u⟩ hns
      · have hbig : BigW C (26 + k) := by
          rcases trich C (rd C (w, b)) with h | h | h
          · exact absurd hacc (h t1)
          · exact absurd h hns
          · rw [hk2] at h
            exact h
        rw [hk2] at hns
        obtain ⟨e, he, ho⟩ := ih k (by omega) hk hbig
        rcases g2_reader C own cs cen hT k hk hns (w, b) hw hk2 e he ho with h3 | ⟨_, h3⟩
        · exact absurd (congrArg Prod.fst h3) (hown e he)
        · exact ⟨e, he, h3⟩

theorem and_cases (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (g : ℕ) (hg : g < C.gates.length) (ha : isAnd C g) :
    g ∈ E26.image own ∨ (LowW C (gA C g) ∧ LowW C (gB C g)) := by
  classical
  by_cases hmem : g ∈ E26.image own
  · exact Or.inl hmem
  · right
    have hlow : ∀ b : Bool, LowW C (rd C (g, b)) := by
      intro b
      have hns : ¬ ∃ t, SingW C (rd C (g, b)) t := by
        intro hs
        rcases tight_sing C own cs cen hT (g, b) hg hs with
          ⟨t, h1⟩ | ⟨h1, _⟩ | ⟨e, he, ⟨h1, _⟩ | ⟨h1, _⟩⟩
        · exact and_low C hG g hg ha t ((h1 t).mpr rfl)
        · exact hmem h1
        · apply hmem
          have h2 : g = own e := h1
          rw [h2]
          exact Finset.mem_image_of_mem own he
        · exact h1 ha
      rcases trich C (rd C (g, b)) with h | h | h
      · exact h
      · exact absurd h hns
      · exfalso
        have hlt : rd C (g, b) < 26 + g := rd_lt C hG (g, b) hg
        rcases wire_cases C (rd C (g, b)) (by omega) with ⟨u, hu⟩ | ⟨k, hk, hk2⟩
        · exact hns ⟨u, by rw [hu]; exact sing_input C u⟩
        · rw [hk2] at h hns
          obtain ⟨e, he, ho⟩ := g2_big_in_leaf C hG own cs cen hT k hk h
          rcases g2_reader C own cs cen hT k hk hns (g, b) hg hk2 e he ho with h1 | ⟨h1, _⟩
          · apply hmem
            have h2 : g = own e := congrArg Prod.fst h1
            rw [h2]
            exact Finset.mem_image_of_mem own he
          · exact h1 ha
    have hA := hlow false
    have hB := hlow true
    rw [rd_false] at hA
    rw [rd_true] at hB
    exact ⟨hA, hB⟩

theorem cen_inj (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (j j' : ℕ) (hj : j ∈ E26.image own) (hj' : j' ∈ E26.image own)
    (h : cen j = cen j') : j = j' := by
  classical
  -- hG is not needed for this statement; the next line only keeps the linter quiet
  have _ := hG
  have hcov : ∀ e ∈ E26, e.1 ∈ (E26.image own).image cen ∨
      e.2 ∈ (E26.image own).image cen := by
    intro e he
    have hmem : cen (own e) ∈ (E26.image own).image cen :=
      Finset.mem_image_of_mem cen (Finset.mem_image_of_mem own he)
    rcases tight_leaf C own cs cen hT e he with ⟨h1, _⟩ | ⟨h1, _⟩
    · left
      rw [h1]
      exact hmem
    · right
      rw [h1]
      exact hmem
  have h13 := cover13 ((E26.image own).image cen) hcov
  have hle : ((E26.image own).image cen).card ≤ (E26.image own).card :=
    Finset.card_image_le
  have hcard := tight_card C own cs cen hT
  have heq : ((E26.image own).image cen).card = (E26.image own).card := by omega
  have hinj : Set.InjOn cen (E26.image own) := Finset.injOn_of_card_image_eq heq
  exact hinj hj hj' h

-- the fibre of own over i lies in the star of the centre of i
theorem g2_fib_sub (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool)
    (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (i : ℕ) :
    E26.filter (fun e => own e = i) ⊆ E26.filter (fun e => e.1 = cen i ∨ e.2 = cen i) := by
  intro e he
  obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
  refine Finset.mem_filter.mpr ⟨he1, ?_⟩
  rcases tight_leaf C own cs cen hT e he1 with ⟨h1, _⟩ | ⟨h1, _⟩
  · left
    rw [h1, he2]
  · right
    rw [h1, he2]

theorem g2_fib_le (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool)
    (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (i : ℕ) :
    (E26.filter (fun e => own e = i)).card ≤ 4 :=
  le_trans (Finset.card_le_card (g2_fib_sub C own cs cen hT i)) (deg4 (cen i))

-- 13 fibres of size at most 4 cover the 52 edges, so every fibre has exactly 4 edges
theorem g2_fib_card (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool)
    (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (i : ℕ) (hi : i ∈ E26.image own) :
    (E26.filter (fun e => own e = i)).card = 4 := by
  classical
  by_contra hne
  have hlt : (E26.filter (fun e => own e = i)).card < 4 :=
    lt_of_le_of_ne (g2_fib_le C own cs cen hT i) hne
  have hsum : E26.card = ∑ b ∈ E26.image own, (E26.filter (fun a => own a = b)).card :=
    Finset.card_eq_sum_card_image own E26
  have hlt2 : ∑ b ∈ E26.image own, (E26.filter (fun a => own a = b)).card
      < ∑ _b ∈ E26.image own, 4 :=
    Finset.sum_lt_sum (fun b _ => g2_fib_le C own cs cen hT b) ⟨i, hi, hlt⟩
  rw [Finset.sum_const, smul_eq_mul, tight_card C own cs cen hT, ← hsum, e26_card] at hlt2
  omega

theorem g2_fib_eq (C : Circuit) (own : Fin 26 × Fin 26 → ℕ) (cs : ℕ → Bool)
    (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (i : ℕ) (hi : i ∈ E26.image own) :
    E26.filter (fun e => own e = i) = E26.filter (fun e => e.1 = cen i ∨ e.2 = cen i) := by
  apply Finset.eq_of_subset_of_card_le (g2_fib_sub C own cs cen hT i)
  rw [g2_fib_card C own cs cen hT i hi]
  exact deg4 (cen i)

theorem cen_indep (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (j j' : ℕ) (hj : j ∈ E26.image own) (hj' : j' ∈ E26.image own) :
    ¬ adj (cen j) (cen j') := by
  classical
  -- hG is not needed for this statement; the next line only keeps the linter quiet
  have _ := hG
  intro hadj
  have hne : j ≠ j' := by
    intro h
    subst h
    exact adj_irr _ hadj
  have key : ∀ e ∈ E26, (e.1 = cen j ∨ e.2 = cen j) → (e.1 = cen j' ∨ e.2 = cen j') →
      False := by
    intro e he h1 h2
    have m1 : e ∈ E26.filter (fun e => own e = j) := by
      rw [g2_fib_eq C own cs cen hT j hj]
      exact Finset.mem_filter.mpr ⟨he, h1⟩
    have m2 : e ∈ E26.filter (fun e => own e = j') := by
      rw [g2_fib_eq C own cs cen hT j' hj']
      exact Finset.mem_filter.mpr ⟨he, h2⟩
    exact hne ((Finset.mem_filter.mp m1).2.symm.trans (Finset.mem_filter.mp m2).2)
  rcases adj_e26 _ _ hadj with h | h
  · exact key _ h (Or.inl rfl) (Or.inr rfl)
  · exact key _ h (Or.inr rfl) (Or.inl rfl)

-- GROUP G3A (ancestors)
theorem low_not_sing (C : Circuit) (w : ℕ) (hl : LowW C w) : ¬ ∃ t, SingW C w t := by
  rintro ⟨t, ht⟩
  exact hl t ((ht t).mpr rfl)

theorem uniq_pos (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (k : ℕ) (hk : k < C.gates.length) (hns : ¬ ∃ t, SingW C (26 + k) t)
    (p q : ℕ × Bool) (hp : p.1 < C.gates.length) (hq : q.1 < C.gates.length)
    (hrp : rd C p = 26 + k) (hrq : rd C q = 26 + k) : p = q := by
  -- hG is not needed here; the next line only keeps the linter quiet
  have _ := hG
  have hko : k ≠ oG C := by
    intro hko
    rw [hko] at hrp
    exact tight_out C own cs cen hT p hp hrp
  obtain ⟨r, _, _, hr⟩ := tight_read C own cs cen hT k hk hko hns
  rw [hr p hp hrp, hr q hq hrq]

-- (L2) with an explicit bound n on (number of gates) - a
theorem g3a_anc_cmp (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (n : ℕ) :
    ∀ a k h : ℕ, C.gates.length ≤ a + n → LowW C (26 + a) → LowW C (26 + k) →
      LowW C (26 + h) → Orc C (26 + k) a → Orc C (26 + h) a →
      Orc C (26 + h) k ∨ Orc C (26 + k) h := by
  induction n with
  | zero =>
    intro a k h hn hla hlk hlh hk hh
    have hal : a < C.gates.length := (orc_bounds C hG (26 + k) a hk).1
    omega
  | succ n ih =>
    intro a k h hn hla hlk hlh hk hh
    have hal : a < C.gates.length := (orc_bounds C hG (26 + k) a hk).1
    by_cases hka : k = a
    · rw [hka]
      exact Or.inl hh
    by_cases hha : h = a
    · rw [hha]
      exact Or.inr hk
    rcases orc_last C (26 + k) a hk with h1 | ⟨k1, b1, hk1, hk1l, hk1o, hk1r⟩
    · exact absurd (by omega) hka
    rcases orc_last C (26 + h) a hh with h2 | ⟨k2, b2, hk2, hk2l, hk2o, hk2r⟩
    · exact absurd (by omega) hha
    have hpq : (k1, b1) = (k2, b2) :=
      uniq_pos C hG own cs cen hT a hal (low_not_sing C (26 + a) hla) (k1, b1) (k2, b2)
        hk1l hk2l hk1r hk2r
    have h12 : k1 = k2 := congrArg Prod.fst hpq
    rw [← h12] at hk2
    have hlu : LowW C (26 + k1) := orc_low C hG (26 + k) k1 hk1 hlk
    have hlt : rd C (k1, b1) < 26 + k1 := rd_lt C hG (k1, b1) hk1l
    have hak : a < k1 := by
      rw [hk1r] at hlt
      omega
    exact ih k1 k h (by omega) hlu hlk hlh hk1 hk2

theorem anc_cmp (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (a k h : ℕ) (hla : LowW C (26 + a)) (hlk : LowW C (26 + k)) (hlh : LowW C (26 + h))
    (hk : Orc C (26 + k) a) (hh : Orc C (26 + h) a) :
    Orc C (26 + h) k ∨ Orc C (26 + k) h := by
  exact g3a_anc_cmp C hG own cs cen hT C.gates.length a k h (by omega) hla hlk hlh hk hh

theorem anc_pos (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (a k h : ℕ) (hla : LowW C (26 + a)) (hlk : LowW C (26 + k)) (hlh : LowW C (26 + h))
    (hk : Orc C (26 + k) a) (hh : Orc C (26 + h) a)
    (P Q : ℕ × Bool) (hP : P.1 < C.gates.length) (hQ : Q.1 < C.gates.length)
    (hrP : rd C P = 26 + k) (hrQ : rd C Q = 26 + h) :
    (k = h ∧ P = Q) ∨ (¬ isAnd C P.1 ∧ LowW C (26 + P.1)) ∨
      (¬ isAnd C Q.1 ∧ LowW C (26 + Q.1)) := by
  have hkl : k < C.gates.length := by
    have hb := (orc_bounds C hG (26 + k) a hk).2.2
    omega
  have hhl : h < C.gates.length := by
    have hb := (orc_bounds C hG (26 + h) a hh).2.2
    omega
  by_cases hkh : k = h
  · refine Or.inl ⟨hkh, ?_⟩
    rw [← hkh] at hrQ
    exact uniq_pos C hG own cs cen hT k hkl (low_not_sing C (26 + k) hlk) P Q hP hQ hrP hrQ
  · rcases anc_cmp C hG own cs cen hT a k h hla hlk hlh hk hh with hc | hc
    · rcases orc_last C (26 + h) k hc with h1 | ⟨k1, b1, hk1, hk1l, hk1o, hk1r⟩
      · exact absurd (by omega) hkh
      · have hPe : P = (k1, b1) :=
          uniq_pos C hG own cs cen hT k hkl (low_not_sing C (26 + k) hlk) P (k1, b1)
            hP hk1l hrP hk1r
        have hlu : LowW C (26 + k1) := orc_low C hG (26 + h) k1 hk1 hlh
        refine Or.inr (Or.inl ?_)
        rw [hPe]
        exact ⟨hk1o, hlu⟩
    · rcases orc_last C (26 + k) h hc with h1 | ⟨k1, b1, hk1, hk1l, hk1o, hk1r⟩
      · exact absurd (by omega) hkh
      · have hQe : Q = (k1, b1) :=
          uniq_pos C hG own cs cen hT h hhl (low_not_sing C (26 + h) hlh) Q (k1, b1)
            hQ hk1l hrQ hk1r
        have hlu : LowW C (26 + k1) := orc_low C hG (26 + k) k1 hk1 hlk
        refine Or.inr (Or.inr ?_)
        rw [hQe]
        exact ⟨hk1o, hlu⟩

theorem low_step (C : Circuit) (hG : Good C) (q a : ℕ) (h : Orc C q a)
    (hq : ¬ LowW C q) (ha : LowW C (26 + a)) :
    ∃ p b h', Orc C q p ∧ p < C.gates.length ∧ ¬ isAnd C p ∧ ¬ LowW C (26 + p) ∧
      rd C (p, b) = 26 + h' ∧ LowW C (26 + h') ∧ Orc C (26 + h') a := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases orc_first C hG q a h with h1 | ⟨k, b, hqk, hkl, hko, hkr⟩
    · rw [h1] at hq
      exact absurd ha hq
    · have hlt : rd C (k, b) < 26 + k := rd_lt C hG (k, b) hkl
      by_cases hl : LowW C (rd C (k, b))
      · obtain ⟨h', _, hh'⟩ := low_is_gate C (rd C (k, b)) (by omega) hl
        refine ⟨k, b, h', ?_, hkl, hko, ?_, hh', ?_, ?_⟩
        · rw [hqk]
          exact orc_base C k hkl
        · rw [← hqk]
          exact hq
        · rw [← hh']
          exact hl
        · rw [← hh']
          exact hkr
      · obtain ⟨p, b', h', hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ :=
          ih (rd C (k, b)) (by omega) hkr hl
        refine ⟨p, b', h', ?_, hp2, hp3, hp4, hp5, hp6, hp7⟩
        rw [hqk]
        exact orc_step C k b p hkl hko hp1

-- the first AND gate on a path of read steps from k down to the AND gate i
theorem g3a_first_and (C : Circuit) (hG : Good C) (i : ℕ) (hai : isAnd C i) (k : ℕ) :
    Relation.ReflTransGen (Rdv C) k i → k < C.gates.length →
      ∃ i1, isAnd C i1 ∧ Orc C (26 + k) i1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h hk
    by_cases hx : isAnd C k
    · exact ⟨k, hx, orc_base C k hk⟩
    · rcases Relation.ReflTransGen.cases_head h with h0 | ⟨y, hky, hyi⟩
      · rw [h0] at hx
        exact absurd hai hx
      · obtain ⟨_, b, hb⟩ := (rdv_iff C k y).mp hky
        have hyk : y < k := rdv_lt C hG k y hky
        obtain ⟨i1, hi1, ho⟩ := ih y hyk hyi (by omega)
        refine ⟨i1, hi1, orc_step C k b i1 hk hx ?_⟩
        rw [hb]
        exact ho

-- from an AND gate below an AND gate down to an owner
theorem g3a_down (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen) (i1 : ℕ) :
    ∀ (j' : ℕ) (b : Bool), j' < C.gates.length → isAnd C j' → isAnd C i1 →
      Orc C (rd C (j', b)) i1 →
      ∃ j'' b'' a, j'' < C.gates.length ∧ isAnd C j'' ∧ a ∈ E26.image own ∧
        Orc C (rd C (j'', b'')) a := by
  induction i1 using Nat.strong_induction_on with
  | _ i1 ih =>
    intro j' b hj' haj' hai1 ho
    have hi1 : i1 < C.gates.length := (orc_bounds C hG (rd C (j', b)) i1 ho).1
    rcases and_cases C hG own cs cen hT i1 hi1 hai1 with hin | ⟨hlA, _⟩
    · exact ⟨j', b, i1, hj', haj', hin, ho⟩
    · have hA : gA C i1 < 26 + i1 := good_hA C hG i1 hi1
      obtain ⟨k2, hk2l, hk2⟩ := low_is_gate C (gA C i1) (by omega) hlA
      have hlk2 : LowW C (26 + k2) := by
        rw [← hk2]
        exact hlA
      obtain ⟨g, hg, hga⟩ := low_has_and C hG k2 hk2l hlk2
      have hg' : Orc C (rd C (i1, false)) g := by
        rw [rd_false, hk2]
        exact hg
      have hgb : 26 + g ≤ 26 + k2 := (orc_bounds C hG (26 + k2) g hg).2.1
      have hgi : g < i1 := by omega
      exact ih g hgi i1 false hi1 hai1 hga hg'

theorem nest_pair (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (i j : ℕ) (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hai : isAnd C i) (haj : isAnd C j) (h : Relation.TransGen (Rdv C) j i) :
    ∃ j' b a, j' < C.gates.length ∧ isAnd C j' ∧ a ∈ E26.image own ∧
      Orc C (rd C (j', b)) a := by
  -- hi is not needed here; the next line only keeps the linter quiet
  have _ := hi
  obtain ⟨k, hjk, hki⟩ := Relation.TransGen.head'_iff.mp h
  obtain ⟨_, b, hb⟩ := (rdv_iff C j k).mp hjk
  have hkj : k < j := rdv_lt C hG j k hjk
  obtain ⟨i1, hi1, ho⟩ := g3a_first_and C hG i hai k hki (by omega)
  have ho' : Orc C (rd C (j, b)) i1 := by
    rw [hb]
    exact ho
  exact g3a_down C hG own cs cen hT i1 j b hj haj hi1 ho'

-- GROUP G3B (every owner is at the top)
-- an AND gate true at x has both operands true at x
theorem g3b_vl_rd (C : Circuit) (hG : Good C) (x : Fin 26 → Bool) (i : ℕ)
    (hi : i < C.gates.length) (ha : isAnd C i) (b : Bool)
    (hx : vl C x (26 + i) = true) : vl C x (rd C (i, b)) = true := by
  have h := (vl_and C hG x i hi ha).mp hx
  cases b
  · rw [rd_false]
    exact h.1
  · rw [rd_true]
    exact h.2

-- the dictionary for an owner
theorem g3b_owner (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (a : ℕ) (ha : a ∈ E26.image own) :
    a < C.gates.length ∧ isAnd C a ∧ SingW C (rd C (a, cs a)) (cen a) ∧
      ¬ LowW C (rd C (a, !(cs a))) ∧
      ∀ t : Fin 26, acc C (rd C (a, !(cs a))) t → adj (cen a) t := by
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
  refine ⟨(tight_own C own cs cen hT e he).1, (tight_own C own cs cen hT e he).2,
    tight_cen C own cs cen hT e he, ?_, ?_⟩
  · intro hl
    rcases tight_leaf C own cs cen hT e he with h | h
    · exact hl _ h.2
    · exact hl _ h.2
  · intro t ht
    exact owner_leaf_adj C hG own cs cen hT e he t ht

-- an AND gate that is not an owner has two Low operands
theorem g3b_low_rd (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (i : ℕ) (hi : i < C.gates.length) (hai : isAnd C i) (hno : i ∉ E26.image own)
    (b : Bool) : LowW C (rd C (i, b)) := by
  rcases and_cases C hG own cs cen hT i hi hai with h | h
  · exact absurd h hno
  · cases b
    · rw [rd_false]
      exact h.1
    · rw [rd_true]
      exact h.2

-- a wire that is not Low accepts a single
theorem g3b_not_low (C : Circuit) (w : ℕ) (h : ¬ LowW C w) : ∃ u : Fin 26, acc C w u := by
  by_contra hcon
  exact h (fun u hu => hcon ⟨u, hu⟩)

-- claim (Q)
theorem g3b_Q (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (a : ℕ) (ha : a ∈ E26.image own) (w : Fin 26) (hw : adj (cen a) w)
    (i : ℕ) (hi : i < C.gates.length) (hai : isAnd C i)
    (hx : vl C (e2 (cen a) w) (26 + i) = true) (hne : i ≠ a) :
    ∃ b i', i' < C.gates.length ∧ isAnd C i' ∧ vl C (e2 (cen a) w) (26 + i') = true ∧
      i' < i ∧ Orc C (rd C (i, b)) i' ∧
      (i ∈ E26.image own → b = cs i) ∧ (i ∉ E26.image own → LowW C (rd C (i, b))) := by
  by_cases hio : i ∈ E26.image own
  · obtain ⟨_, _, hsing, _, _⟩ := g3b_owner C hG own cs cen hT i hio
    have hz := g3b_vl_rd C hG (e2 (cen a) w) i hi hai (cs i) hx
    have hlt : rd C (i, cs i) < 26 + i := rd_lt C hG (i, cs i) hi
    rcases fact1 C hG (e2 (cen a) w) (rd C (i, cs i)) (by omega) hz with
      ⟨u, hu, hxu⟩ | ⟨g, hg, hga, hgx⟩
    · exfalso
      have huc : u = cen i := (hsing u).mp hu
      rcases e2_mem (cen a) w u hxu with h | h
      · exact hne (cen_inj C hG own cs cen hT i a hio ha (huc.symm.trans h))
      · apply cen_indep C hG own cs cen hT a i ha hio
        rw [← huc, h]
        exact hw
    · obtain ⟨hgl, hge, _⟩ := orc_bounds C hG _ _ hg
      exact ⟨cs i, g, hgl, hga, hgx, by omega, hg, fun _ => rfl, fun h => absurd hio h⟩
  · have hlow := g3b_low_rd C hG own cs cen hT i hi hai hio false
    have hz := g3b_vl_rd C hG (e2 (cen a) w) i hi hai false hx
    have hlt : rd C (i, false) < 26 + i := rd_lt C hG (i, false) hi
    rcases fact1 C hG (e2 (cen a) w) (rd C (i, false)) (by omega) hz with
      ⟨u, hu, _⟩ | ⟨g, hg, hga, hgx⟩
    · exact absurd hu (hlow u)
    · obtain ⟨hgl, hge, _⟩ := orc_bounds C hG _ _ hg
      exact ⟨false, g, hgl, hga, hgx, by omega, hg, fun h => absurd h hio, fun _ => hlow⟩

theorem descent (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (a : ℕ) (ha : a ∈ E26.image own) (w : Fin 26) (hw : adj (cen a) w)
    (i : ℕ) (hi : i < C.gates.length) (hai : isAnd C i)
    (hx : vl C (e2 (cen a) w) (26 + i) = true) (hne : i ≠ a) :
    ∃ i' b, i' < C.gates.length ∧ isAnd C i' ∧ vl C (e2 (cen a) w) (26 + i') = true ∧
      i' ≠ a ∧ i' ≤ i ∧ Orc C (rd C (i', b)) a ∧
      (i' ∈ E26.image own → b = cs i') ∧ (i' ∉ E26.image own → LowW C (rd C (i', b))) := by
  revert hi hai hx hne
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi hai hx hne
    obtain ⟨b, i', hi'l, hi'a, hi'x, hi'lt, hi'o, hown, hnown⟩ :=
      g3b_Q C hG own cs cen hT a ha w hw i hi hai hx hne
    by_cases hia : i' = a
    · rw [hia] at hi'o
      exact ⟨i, b, hi, hai, hx, hne, le_refl i, hi'o, hown, hnown⟩
    · obtain ⟨i2, b2, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih i' hi'lt hi'l hi'a hi'x hia
      exact ⟨i2, b2, h1, h2, h3, h4, by omega, h6, h7, h8⟩

-- the start: an AND gate true at x, different from a
theorem g3b_start (C : Circuit) (hG : Good C)
    (cen : ℕ → Fin 26) (a : ℕ) (hno : ¬ Orc C (26 + oG C) a) (w : Fin 26)
    (hw : adj (cen a) w) :
    ∃ i, i < C.gates.length ∧ isAnd C i ∧ vl C (e2 (cen a) w) (26 + i) = true ∧ i ≠ a := by
  have hacc := good_acc C hG (cen a) w hw
  have ho := good_o C hG
  rcases fact1 C hG (e2 (cen a) w) (26 + oG C) (by omega) hacc with
    ⟨u, hu, _⟩ | ⟨g, hg, hga, hgx⟩
  · exact absurd hu (out_low C hG u)
  · refine ⟨g, (orc_bounds C hG _ _ hg).1, hga, hgx, ?_⟩
    intro h
    rw [h] at hg
    exact hno hg

-- Case A is impossible: the gate reached by the descent cannot be a non-owner
theorem g3b_caseA (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (a : ℕ) (ha : a ∈ E26.image own) (w : Fin 26) (hw : adj (cen a) w)
    (i : ℕ) (hi : i < C.gates.length) (hai : isAnd C i)
    (hx : vl C (e2 (cen a) w) (26 + i) = true)
    (hno : i ∉ E26.image own) (b : Bool) (ho : Orc C (rd C (i, b)) a)
    (hl : LowW C (rd C (i, b))) : False := by
  obtain ⟨hal, haa, _, _, _⟩ := g3b_owner C hG own cs cen hT a ha
  have hla : LowW C (26 + a) := and_low C hG a hal haa
  have hlt : rd C (i, b) < 26 + i := rd_lt C hG (i, b) hi
  obtain ⟨kq, hkq, hq⟩ := low_is_gate C (rd C (i, b)) (by omega) hl
  have hl' : LowW C (rd C (i, !b)) := g3b_low_rd C hG own cs cen hT i hi hai hno (!b)
  have hlt' : rd C (i, !b) < 26 + i := rd_lt C hG (i, !b) hi
  obtain ⟨kq', hkq', hq'⟩ := low_is_gate C (rd C (i, !b)) (by omega) hl'
  have hz' := g3b_vl_rd C hG (e2 (cen a) w) i hi hai (!b) hx
  rcases fact1 C hG (e2 (cen a) w) (rd C (i, !b)) (by omega) hz' with
    ⟨u, hu, _⟩ | ⟨g, hg, hga, hgx⟩
  · exact hl' u hu
  · obtain ⟨hgl, hge, _⟩ := orc_bounds C hG _ _ hg
    rw [hq] at hl ho
    by_cases hga' : g = a
    · rw [hga', hq'] at hg
      rw [hq'] at hl'
      rcases anc_pos C hG own cs cen hT a kq kq' hla hl hl' ho hg (i, b) (i, !b) hi hi
        hq hq' with h | h | h
      · have hb : b = !b := congrArg Prod.snd h.2
        cases b <;> simp at hb
      · exact h.1 hai
      · exact h.1 hai
    · obtain ⟨i2, b2, hi2l, hi2a, hi2x, hi2ne, hi2le, hi2o, hi2own, hi2no⟩ :=
        descent C hG own cs cen hT a ha w hw g hgl hga hgx hga'
      have hlt2 : rd C (i2, b2) < 26 + i2 := rd_lt C hG (i2, b2) hi2l
      by_cases hl2 : LowW C (rd C (i2, b2))
      · obtain ⟨k2, hk2, hq2⟩ := low_is_gate C (rd C (i2, b2)) (by omega) hl2
        rw [hq2] at hl2 hi2o
        rcases anc_pos C hG own cs cen hT a kq k2 hla hl hl2 ho hi2o (i, b) (i2, b2) hi hi2l
          hq hq2 with h | h | h
        · have hii : i = i2 := congrArg Prod.fst h.2
          omega
        · exact h.1 hai
        · exact h.1 hi2a
      · obtain ⟨p, bp, k3, hop, hpl, hpa, hpnl, hrp, hlk3, hok3⟩ :=
          low_step C hG (rd C (i2, b2)) a hi2o hl2 hla
        rcases anc_pos C hG own cs cen hT a kq k3 hla hl hlk3 ho hok3 (i, b) (p, bp) hi hpl
          hq hrp with h | h | h
        · have hip : i = p := congrArg Prod.fst h.2
          rw [hip] at hai
          exact hpa hai
        · exact h.1 hai
        · exact hpnl h.2

-- key fact (K): the owner whose centre operand has a in its OR closure is unique
theorem g3b_K (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (a : ℕ) (hla : LowW C (26 + a)) (i1 i2 : ℕ) (h1 : i1 ∈ E26.image own)
    (h2 : i2 ∈ E26.image own) (ho1 : Orc C (rd C (i1, cs i1)) a)
    (ho2 : Orc C (rd C (i2, cs i2)) a) : i1 = i2 := by
  obtain ⟨_, _, hs1, _, _⟩ := g3b_owner C hG own cs cen hT i1 h1
  obtain ⟨_, _, hs2, _, _⟩ := g3b_owner C hG own cs cen hT i2 h2
  have hn1 : ¬ LowW C (rd C (i1, cs i1)) := fun h => h (cen i1) ((hs1 (cen i1)).mpr rfl)
  have hn2 : ¬ LowW C (rd C (i2, cs i2)) := fun h => h (cen i2) ((hs2 (cen i2)).mpr rfl)
  obtain ⟨p1, b1, k1, hop1, hp1l, hp1a, hp1n, hr1, hlk1, hok1⟩ :=
    low_step C hG (rd C (i1, cs i1)) a ho1 hn1 hla
  obtain ⟨p2, b2, k2, hop2, hp2l, hp2a, hp2n, hr2, hlk2, hok2⟩ :=
    low_step C hG (rd C (i2, cs i2)) a ho2 hn2 hla
  rcases anc_pos C hG own cs cen hT a k1 k2 hla hlk1 hlk2 hok1 hok2 (p1, b1) (p2, b2)
    hp1l hp2l hr1 hr2 with h | h | h
  · have hp : p1 = p2 := congrArg Prod.fst h.2
    obtain ⟨u, hu⟩ := g3b_not_low C (26 + p1) hp1n
    have hu1 : u = cen i1 := (hs1 u).mp (orc_acc C hG _ _ hop1 u hu)
    rw [hp] at hu
    have hu2 : u = cen i2 := (hs2 u).mp (orc_acc C hG _ _ hop2 u hu)
    exact cen_inj C hG own cs cen hT i1 i2 h1 h2 (hu1.symm.trans hu2)
  · exact absurd h.2 hp1n
  · exact absurd h.2 hp2n

-- descent followed by Case A: the gate reached is an owner
theorem g3b_desc_owner (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (a : ℕ) (ha : a ∈ E26.image own) (w : Fin 26) (hw : adj (cen a) w)
    (i : ℕ) (hi : i < C.gates.length) (hai : isAnd C i)
    (hx : vl C (e2 (cen a) w) (26 + i) = true) (hne : i ≠ a) :
    ∃ i', i' ∈ E26.image own ∧ vl C (e2 (cen a) w) (26 + i') = true ∧
      i' ≠ a ∧ i' ≤ i ∧ Orc C (rd C (i', cs i')) a := by
  obtain ⟨i2, b2, hi2l, hi2a, hi2x, hi2ne, hi2le, hi2o, hi2own, hi2no⟩ :=
    descent C hG own cs cen hT a ha w hw i hi hai hx hne
  by_cases ho : i2 ∈ E26.image own
  · have hb := hi2own ho
    rw [hb] at hi2o
    exact ⟨i2, ho, hi2x, hi2ne, hi2le, hi2o⟩
  · exact (g3b_caseA C hG own cs cen hT a ha w hw i2 hi2l hi2a hi2x ho b2 hi2o
      (hi2no ho)).elim

-- Case B
theorem g3b_caseB (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (a : ℕ) (ha : a ∈ E26.image own) (s : ℕ) (hs : s ∈ E26.image own)
    (hos : Orc C (rd C (s, cs s)) a) (w : Fin 26) (hw : adj (cen a) w)
    (hnw : ¬ adj (cen s) w) (hx : vl C (e2 (cen a) w) (26 + s) = true) : False := by
  obtain ⟨hal, haa, _, _, _⟩ := g3b_owner C hG own cs cen hT a ha
  obtain ⟨hsl, hsand, hsing, hnl, hadj⟩ := g3b_owner C hG own cs cen hT s hs
  have hla : LowW C (26 + a) := and_low C hG a hal haa
  have hz := g3b_vl_rd C hG (e2 (cen a) w) s hsl hsand (!(cs s)) hx
  have hlt : rd C (s, !(cs s)) < 26 + s := rd_lt C hG (s, !(cs s)) hsl
  rcases fact1 C hG (e2 (cen a) w) (rd C (s, !(cs s))) (by omega) hz with
    ⟨u, hu, hxu⟩ | ⟨g, hg, hga, hgx⟩
  · have hau := hadj u hu
    rcases e2_mem (cen a) w u hxu with h | h
    · rw [h] at hau
      exact cen_indep C hG own cs cen hT s a hs ha hau
    · rw [h] at hau
      exact hnw hau
  · obtain ⟨hgl, hge, _⟩ := orc_bounds C hG _ _ hg
    by_cases hga' : g = a
    · rw [hga'] at hg
      have hn1 : ¬ LowW C (rd C (s, cs s)) := fun h => h (cen s) ((hsing (cen s)).mpr rfl)
      obtain ⟨p1, b1, k1, hop1, hp1l, hp1a, hp1n, hr1, hlk1, hok1⟩ :=
        low_step C hG (rd C (s, cs s)) a hos hn1 hla
      obtain ⟨p2, b2, k2, hop2, hp2l, hp2a, hp2n, hr2, hlk2, hok2⟩ :=
        low_step C hG (rd C (s, !(cs s))) a hg hnl hla
      rcases anc_pos C hG own cs cen hT a k1 k2 hla hlk1 hlk2 hok1 hok2 (p1, b1) (p2, b2)
        hp1l hp2l hr1 hr2 with h | h | h
      · have hp : p1 = p2 := congrArg Prod.fst h.2
        obtain ⟨u, hu⟩ := g3b_not_low C (26 + p1) hp1n
        have hu1 : u = cen s := (hsing u).mp (orc_acc C hG _ _ hop1 u hu)
        rw [hp] at hu
        have hu2 : adj (cen s) u := hadj u (orc_acc C hG _ _ hop2 u hu)
        rw [hu1] at hu2
        exact adj_irr _ hu2
      · exact absurd h.2 hp1n
      · exact absurd h.2 hp2n
    · obtain ⟨i', hi'o, hi'x, hi'ne, hi'le, hi'orc⟩ :=
        g3b_desc_owner C hG own cs cen hT a ha w hw g hgl hga hgx hga'
      have heq := g3b_K C hG own cs cen hT a hla i' s hi'o hs hi'orc hos
      omega

theorem top_owner (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (a : ℕ) (ha : a ∈ E26.image own) : Orc C (26 + oG C) a := by
  by_contra hno
  obtain ⟨hal, haa, _, _, _⟩ := g3b_owner C hG own cs cen hT a ha
  have hla : LowW C (26 + a) := and_low C hG a hal haa
  have hex : ∃ c' : Fin 26, cen a ≠ c' := by
    by_cases h : cen a = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, h⟩
  obtain ⟨c', hc'⟩ := hex
  obtain ⟨w0, hw0, _⟩ := nbr_diff (cen a) c' hc'
  obtain ⟨i0, hi0l, hi0a, hi0x, hi0ne⟩ := g3b_start C hG cen a hno w0 hw0
  obtain ⟨s, hs, _, hsa, _, hos⟩ :=
    g3b_desc_owner C hG own cs cen hT a ha w0 hw0 i0 hi0l hi0a hi0x hi0ne
  have hcne : cen a ≠ cen s := fun h => hsa (cen_inj C hG own cs cen hT s a hs ha h.symm)
  obtain ⟨w, hw, hnw⟩ := nbr_diff (cen a) (cen s) hcne
  obtain ⟨i1, hi1l, hi1a, hi1x, hi1ne⟩ := g3b_start C hG cen a hno w hw
  obtain ⟨s', hs', hs'x, _, _, hos'⟩ :=
    g3b_desc_owner C hG own cs cen hT a ha w hw i1 hi1l hi1a hi1x hi1ne
  have heq := g3b_K C hG own cs cen hT a hla s' s hs' hs hos' hos
  rw [heq] at hs'x
  exact g3b_caseB C hG own cs cen hT a ha s hs hos w hw hnw hs'x

theorem no_nest (C : Circuit) (hG : Good C) (own : Fin 26 × Fin 26 → ℕ)
    (cs : ℕ → Bool) (cen : ℕ → Fin 26) (hT : IsTight C own cs cen)
    (i j : ℕ) (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hai : isAnd C i) (haj : isAnd C j) : ¬ Relation.TransGen (Rdv C) j i := by
  intro hji
  obtain ⟨j', b, a, hj'l, hj'a, hao, horc⟩ :=
    nest_pair C hG own cs cen hT i j hi hj hai haj hji
  obtain ⟨hal, haa, _, _, _⟩ := g3b_owner C hG own cs cen hT a hao
  have hla : LowW C (26 + a) := and_low C hG a hal haa
  have htop := top_owner C hG own cs cen hT a hao
  have hol := out_low C hG
  have hlt : rd C (j', b) < 26 + j' := rd_lt C hG (j', b) hj'l
  by_cases hl : LowW C (rd C (j', b))
  · obtain ⟨kq, hkq, hq⟩ := low_is_gate C (rd C (j', b)) (by omega) hl
    rw [hq] at hl horc
    have hne : kq ≠ oG C := by
      intro h'
      rw [h'] at hq
      exact tight_out C own cs cen hT (j', b) hj'l hq
    rcases anc_cmp C hG own cs cen hT a kq (oG C) hla hl hol horc htop with h1 | h1
    · rcases orc_last C _ _ h1 with h2 | ⟨k, b', hk1, hkl, hka, hkr⟩
      · exact hne (by omega)
      · have hpos := uniq_pos C hG own cs cen hT kq hkq (low_not_sing C _ hl) (k, b') (j', b)
          hkl hj'l hkr hq
        have hk : k = j' := congrArg Prod.fst hpos
        rw [hk] at hka
        exact hka hj'a
    · rcases orc_last C _ _ h1 with h2 | ⟨k, b', hk1, hkl, hka, hkr⟩
      · exact hne (by omega)
      · exact tight_out C own cs cen hT (k, b') hkl hkr
  · obtain ⟨p, bp, k3, hop, hpl, hpa, hpnl, hrp, hlk3, hok3⟩ :=
      low_step C hG (rd C (j', b)) a horc hl hla
    have hk3l : k3 < C.gates.length := by
      have h3 := (orc_bounds C hG _ _ hok3).2.2
      omega
    have hne : k3 ≠ oG C := by
      intro h'
      rw [h'] at hrp
      exact tight_out C own cs cen hT (p, bp) hpl hrp
    rcases anc_cmp C hG own cs cen hT a k3 (oG C) hla hlk3 hol hok3 htop with h1 | h1
    · rcases orc_last C _ _ h1 with h2 | ⟨k, b', hk1, hkl, hka, hkr⟩
      · exact hne (by omega)
      · have hpos := uniq_pos C hG own cs cen hT k3 hk3l (low_not_sing C _ hlk3) (k, b') (p, bp)
          hkl hpl hkr hrp
        have hk : k = p := congrArg Prod.fst hpos
        rw [hk] at hk1
        exact hpnl (orc_low C hG _ _ hk1 hol)
    · rcases orc_last C _ _ h1 with h2 | ⟨k, b', hk1, hkl, hka, hkr⟩
      · exact hne (by omega)
      · exact tight_out C own cs cen hT (k, b') hkl hkr

-- GROUP END (frozen)
theorem core (C : Circuit) (hG : Good C) (hs : C.gates.length ≤ 64)
    (i j : ℕ) (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hai : isAnd C i) (haj : isAnd C j) : ¬ Relation.TransGen (Rdv C) j i := by
  obtain ⟨own, cs, cen, hT⟩ := tight_exists C hG hs
  exact no_nest C hG own cs cen hT i j hi hj hai haj

-- The star circuit of the projective plane of order 3 (13 points, 13 lines).
-- Inputs 0..12 are the points, inputs 13..25 are the lines; point p lies on the lines
-- p, p - 1, p - 3, p - 9 modulo 13, that is p, p + 12, p + 10, p + 4 modulo 13.
-- Gates 4 p, 4 p + 1, 4 p + 2 form the OR of the four lines through p, and gate 4 p + 3 is
-- its AND with the point p.
def starGate (p : ℕ) : ℕ → Gate
  | 0 => ⟨GateOp.or, [13 + p % 13, 13 + (p + 12) % 13]⟩
  | 1 => ⟨GateOp.or, [26 + 4 * p, 13 + (p + 10) % 13]⟩
  | 2 => ⟨GateOp.or, [26 + (4 * p + 1), 13 + (p + 4) % 13]⟩
  | _ => ⟨GateOp.and, [p, 26 + (4 * p + 2)]⟩

-- Gates 52..63 chain the thirteen AND gates by OR gates.
def gateFn (j : ℕ) : Gate :=
  if j < 52 then starGate (j / 4) (j % 4)
  else if j = 52 then ⟨GateOp.or, [26 + (4 * 0 + 3), 26 + (4 * 1 + 3)]⟩
  else ⟨GateOp.or, [26 + (j - 1), 26 + (4 * (j - 51) + 3)]⟩

def starC : Circuit := ⟨List.ofFn (fun i : Fin 64 => gateFn i.val), 89⟩

theorem starC_len : starC.gates.length = 64 := by
  show (List.ofFn (fun i : Fin 64 => gateFn i.val)).length = 64
  exact List.length_ofFn

theorem gates_get (j : ℕ) (hj : j < 64) : starC.gates[j]? = some (gateFn j) := by
  show (List.ofFn (fun i : Fin 64 => gateFn i.val))[j]? = some (gateFn j)
  rw [List.getElem?_ofFn]
  exact dite_eq_left hj

theorem gateFn_star (p r : ℕ) (hp : p < 13) (hr : r < 4) :
    gateFn (4 * p + r) = starGate p r := by
  unfold gateFn
  have h1 : 4 * p + r < 52 := by omega
  have h2 : (4 * p + r) / 4 = p := by omega
  have h3 : (4 * p + r) % 4 = r := by omega
  rw [ite_eq_left h1, h2, h3]

theorem gateFn_s0 (p : ℕ) (hp : p < 13) :
    gateFn (4 * p) = ⟨GateOp.or, [13 + p % 13, 13 + (p + 12) % 13]⟩ :=
  gateFn_star p 0 hp (by omega)

theorem gateFn_s1 (p : ℕ) (hp : p < 13) :
    gateFn (4 * p + 1) = ⟨GateOp.or, [26 + 4 * p, 13 + (p + 10) % 13]⟩ :=
  gateFn_star p 1 hp (by omega)

theorem gateFn_s2 (p : ℕ) (hp : p < 13) :
    gateFn (4 * p + 2) = ⟨GateOp.or, [26 + (4 * p + 1), 13 + (p + 4) % 13]⟩ :=
  gateFn_star p 2 hp (by omega)

theorem gateFn_s3 (p : ℕ) (hp : p < 13) :
    gateFn (4 * p + 3) = ⟨GateOp.and, [p, 26 + (4 * p + 2)]⟩ :=
  gateFn_star p 3 hp (by omega)

theorem gateFn_c0 :
    gateFn (52 + 0) = ⟨GateOp.or, [26 + (4 * 0 + 3), 26 + (4 * 1 + 3)]⟩ := by
  unfold gateFn
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

theorem gateFn_c (k : ℕ) :
    gateFn (52 + (k + 1)) = ⟨GateOp.or, [26 + (52 + k), 26 + (4 * (k + 2) + 3)]⟩ := by
  unfold gateFn
  have h1 : 52 + (k + 1) - 1 = 52 + k := by omega
  have h2 : 52 + (k + 1) - 51 = k + 2 := by omega
  rw [ite_eq_right (by omega), ite_eq_right (by omega), h1, h2]

theorem gateFn_op (j : ℕ) : (gateFn j).op = GateOp.and ∨ (gateFn j).op = GateOp.or := by
  unfold gateFn starGate
  split_ifs
  · split <;> simp
  · simp
  · simp

theorem gateFn_len (j : ℕ) : (gateFn j).inputs.length = 2 := by
  unfold gateFn starGate
  split_ifs
  · split <;> rfl
  · rfl
  · rfl

theorem gateFn_back (j : ℕ) (hj : j < 64) : ∀ i ∈ (gateFn j).inputs, i < 26 + j := by
  intro i hi
  by_cases h52 : j < 52
  · obtain ⟨p, r, hp, hr, rfl⟩ : ∃ p r, p < 13 ∧ r < 4 ∧ j = 4 * p + r :=
      ⟨j / 4, j % 4, by omega, by omega, by omega⟩
    rw [gateFn_star p r hp hr] at hi
    have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr4 with rfl | rfl | rfl | rfl <;>
      simp only [starGate, List.mem_cons, List.not_mem_nil, or_false] at hi <;> omega
  · obtain ⟨k, rfl⟩ : ∃ k, j = 52 + k := ⟨j - 52, by omega⟩
    rcases k with _ | k
    · rw [gateFn_c0] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    · rw [gateFn_c k] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega

theorem starC_ao2 : PEqualNP.TopForm.IsAO2 26 starC := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact gateFn_op i.val
  · intro j hj i hi
    have hj64 : j < 64 := lt_of_lt_of_eq hj starC_len
    have hga : NestedCover.gateAt starC j = gateFn j := by
      unfold NestedCover.gateAt
      rw [List.getD_eq_getElem?_getD, gates_get j hj64]
      rfl
    rw [hga] at hi
    exact gateFn_back j hj64 i hi
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact gateFn_len i.val

theorem starC_size : starC.size = 64 := starC_len

-- The value of an OR gate and of an AND gate reading two earlier wires.
theorem or_gate (x : Fin 26 → Bool) (j a b : ℕ) (hj : j < 64)
    (hg : gateFn j = ⟨GateOp.or, [a, b]⟩) (ha : a < 26 + j) (hb : b < 26 + j) :
    val starC 26 x (26 + j) = true ↔
      (val starC 26 x a = true ∨ val starC 26 x b = true) := by
  rw [val_or starC 26 x j (gateFn j) (gates_get j hj) (by rw [hg]), hg]
  constructor
  · rintro ⟨w, hw, _, hv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro (hv | hv)
    · exact ⟨a, by simp, ha, hv⟩
    · exact ⟨b, by simp, hb, hv⟩

theorem and_gate (x : Fin 26 → Bool) (j a b : ℕ) (hj : j < 64)
    (hg : gateFn j = ⟨GateOp.and, [a, b]⟩) (ha : a < 26 + j) (hb : b < 26 + j) :
    val starC 26 x (26 + j) = true ↔
      (val starC 26 x a = true ∧ val starC 26 x b = true) := by
  rw [val_and starC 26 x j (gateFn j) (gates_get j hj) (by rw [hg]), hg]
  constructor
  · intro h
    exact ⟨(h a (by simp)).2, (h b (by simp)).2⟩
  · rintro ⟨hva, hvb⟩ w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨ha, hva⟩
    · exact ⟨hb, hvb⟩

-- The AND gate of point p: the point is true and one of its four lines is true.
theorem star_val (x : Fin 26 → Bool) (p : ℕ) (hp : p < 13) :
    val starC 26 x (26 + (4 * p + 3)) = true ↔
      (val starC 26 x p = true ∧
        (val starC 26 x (13 + p % 13) = true ∨ val starC 26 x (13 + (p + 12) % 13) = true ∨
          val starC 26 x (13 + (p + 10) % 13) = true ∨
          val starC 26 x (13 + (p + 4) % 13) = true)) := by
  have h0 : val starC 26 x (26 + 4 * p) = true ↔
      (val starC 26 x (13 + p % 13) = true ∨ val starC 26 x (13 + (p + 12) % 13) = true) :=
    or_gate x (4 * p) (13 + p % 13) (13 + (p + 12) % 13) (by omega) (gateFn_s0 p hp)
      (by omega) (by omega)
  have h1 : val starC 26 x (26 + (4 * p + 1)) = true ↔
      (val starC 26 x (26 + 4 * p) = true ∨ val starC 26 x (13 + (p + 10) % 13) = true) :=
    or_gate x (4 * p + 1) (26 + 4 * p) (13 + (p + 10) % 13) (by omega) (gateFn_s1 p hp)
      (by omega) (by omega)
  have h2 : val starC 26 x (26 + (4 * p + 2)) = true ↔
      (val starC 26 x (26 + (4 * p + 1)) = true ∨
        val starC 26 x (13 + (p + 4) % 13) = true) :=
    or_gate x (4 * p + 2) (26 + (4 * p + 1)) (13 + (p + 4) % 13) (by omega) (gateFn_s2 p hp)
      (by omega) (by omega)
  have h3 : val starC 26 x (26 + (4 * p + 3)) = true ↔
      (val starC 26 x p = true ∧ val starC 26 x (26 + (4 * p + 2)) = true) :=
    and_gate x (4 * p + 3) p (26 + (4 * p + 2)) (by omega) (gateFn_s3 p hp)
      (by omega) (by omega)
  rw [h3, h2, h1, h0, or_assoc, or_assoc]

-- Chain gate k is the OR of the AND gates of the points 0..k+1.
theorem chain_val (x : Fin 26 → Bool) (k : ℕ) (hk : k < 12) :
    val starC 26 x (26 + (52 + k)) = true ↔
      ∃ p, p ≤ k + 1 ∧ val starC 26 x (26 + (4 * p + 3)) = true := by
  induction k with
  | zero =>
    rw [or_gate x (52 + 0) (26 + (4 * 0 + 3)) (26 + (4 * 1 + 3)) (by omega) gateFn_c0
      (by omega) (by omega)]
    constructor
    · rintro (h | h)
      · exact ⟨0, by omega, h⟩
      · exact ⟨1, by omega, h⟩
    · rintro ⟨p, hp, h⟩
      have hp01 : p = 0 ∨ p = 1 := by omega
      rcases hp01 with rfl | rfl
      · exact Or.inl h
      · exact Or.inr h
  | succ k ih =>
    rw [or_gate x (52 + (k + 1)) (26 + (52 + k)) (26 + (4 * (k + 2) + 3)) (by omega)
      (gateFn_c k) (by omega) (by omega), ih (by omega)]
    constructor
    · rintro (⟨p, hp, h⟩ | h)
      · exact ⟨p, by omega, h⟩
      · exact ⟨k + 2, by omega, h⟩
    · rintro ⟨p, hp, h⟩
      by_cases hpk : p ≤ k + 1
      · exact Or.inl ⟨p, hpk, h⟩
      · have hp2 : p = k + 2 := by omega
        subst hp2
        exact Or.inr h

-- Incidence in the plane: the four lines through a point, as numbers.
theorem inc_iff : ∀ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ↔
    (l.val = p.val % 13 ∨ l.val = (p.val + 12) % 13 ∨ l.val = (p.val + 10) % 13 ∨
      l.val = (p.val + 4) % 13) := by
  decide

theorem val_point (x : Fin 26 → Bool) (p : Fin 13) :
    val starC 26 x p.val = x (Fin.castAdd 13 p) := by
  rw [val_input starC 26 x p.val (by have := p.isLt; omega)]
  rfl

theorem val_line (x : Fin 26 → Bool) (l : Fin 13) :
    val starC 26 x (13 + l.val) = x (Fin.natAdd 13 l) := by
  rw [val_input starC 26 x (13 + l.val) (by have := l.isLt; omega)]
  rfl

theorem star_circuit :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 26 C ∧ C.size = 64 ∧
      ∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
  refine ⟨starC, starC_ao2, starC_size, fun x => ?_⟩
  have hev : starC.eval (List.ofFn x) = val starC 26 x (26 + (52 + 11)) := rfl
  rw [hev, chain_val x 11 (by omega)]
  constructor
  · rintro ⟨p, hp, hv⟩
    have hp13 : p < 13 := by omega
    obtain ⟨hxp, hl⟩ := (star_val x p hp13).mp hv
    have key : ∀ l : ℕ, ∀ hl13 : l < 13,
        (l = p % 13 ∨ l = (p + 12) % 13 ∨ l = (p + 10) % 13 ∨ l = (p + 4) % 13) →
        val starC 26 x (13 + l) = true →
        ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
      intro l hl13 hinc hvl
      refine ⟨⟨p, hp13⟩, ⟨l, hl13⟩, (inc_iff ⟨p, hp13⟩ ⟨l, hl13⟩).mpr hinc, ?_, ?_⟩
      · rw [← val_point x ⟨p, hp13⟩]
        exact hxp
      · rw [← val_line x ⟨l, hl13⟩]
        exact hvl
    have h13 : 0 < 13 := by omega
    rcases hl with h | h | h | h
    · exact key (p % 13) (Nat.mod_lt _ h13) (Or.inl rfl) h
    · exact key ((p + 12) % 13) (Nat.mod_lt _ h13) (Or.inr (Or.inl rfl)) h
    · exact key ((p + 10) % 13) (Nat.mod_lt _ h13) (Or.inr (Or.inr (Or.inl rfl))) h
    · exact key ((p + 4) % 13) (Nat.mod_lt _ h13) (Or.inr (Or.inr (Or.inr rfl))) h
  · rintro ⟨p, l, hinc, hxp, hxl⟩
    have hvp : val starC 26 x p.val = true := by
      rw [val_point x p]
      exact hxp
    have hvl : val starC 26 x (13 + l.val) = true := by
      rw [val_line x l]
      exact hxl
    refine ⟨p.val, by have := p.isLt; omega, (star_val x p.val p.isLt).mpr ⟨hvp, ?_⟩⟩
    rcases (inc_iff p l).mp hinc with h | h | h | h
    · rw [← h]
      exact Or.inl hvl
    · rw [← h]
      exact Or.inr (Or.inl hvl)
    · rw [← h]
      exact Or.inr (Or.inr (Or.inl hvl))
    · rw [← h]
      exact Or.inr (Or.inr (Or.inr hvl))

-- ===================== PART C: from the statement to the setting =====================

theorem gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates :=
  List.mem_of_getElem? (gateAt_get C j hj)

theorem two_list (l : List ℕ) (h : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at h
  · simp at h
  · rfl
  · simp at h

theorem ao2_inputs (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 26 C) (j : ℕ)
    (hj : j < C.gates.length) :
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [gA C j, gB C j] := by
  unfold gA gB
  exact two_list _ (hAO.2.2 _ (gateAt_mem C j hj))

theorem ao2_back (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 26 C) (j : ℕ)
    (hj : j < C.gates.length) : gA C j < 26 + j ∧ gB C j < 26 + j := by
  have hin := ao2_inputs C hAO j hj
  have hb := hAO.2.1 j hj
  constructor
  · exact hb (gA C j) (by rw [hin]; simp)
  · exact hb (gB C j) (by rw [hin]; simp)

theorem vl_gate_and (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 26 C) (x : Fin 26 → Bool)
    (j : ℕ) (hj : j < C.gates.length) (ha : isAnd C j) :
    vl C x (26 + j) = (vl C x (gA C j) && vl C x (gB C j)) := by
  have hin := ao2_inputs C hAO j hj
  obtain ⟨h1, h2⟩ := ao2_back C hAO j hj
  unfold isAnd at ha
  unfold vl
  rw [val_gate C 26 x j _ (gateAt_get C j hj), hin, ha]
  simp [GateOp.eval, h1, h2]

theorem vl_gate_or (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 26 C) (x : Fin 26 → Bool)
    (j : ℕ) (hj : j < C.gates.length) (ha : ¬ isAnd C j) :
    vl C x (26 + j) = (vl C x (gA C j) || vl C x (gB C j)) := by
  have hin := ao2_inputs C hAO j hj
  obtain ⟨h1, h2⟩ := ao2_back C hAO j hj
  have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or := by
    rcases hAO.1 _ (gateAt_mem C j hj) with h | h
    · exact absurd h ha
    · exact h
  unfold vl
  rw [val_gate C 26 x j _ (gateAt_get C j hj), hin, hop]
  simp [GateOp.eval, h1, h2]

theorem adj_stmt (u v : Fin 26) :
    adj u v ↔ ∃ (x6 : Fin 13) (x7 : Fin 13),
      (x6 = x7 ∨ x6 = x7 + 1 ∨ x6 = x7 + 3 ∨ x6 = x7 + 9) ∧
      (u = Fin.castAdd 13 x6 ∧ v = Fin.natAdd 13 x7 ∨
        v = Fin.castAdd 13 x6 ∧ u = Fin.natAdd 13 x7) := by
  have hdiff : ∀ a b : Fin 13, (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) ↔
      a - b ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by decide
  have hpt : ∀ p : Fin 13, (Fin.castAdd 13 p : Fin 26) = pt p := fun p => Fin.ext rfl
  have hln : ∀ l : Fin 13, (Fin.natAdd 13 l : Fin 26) = ln l := fun l => Fin.ext rfl
  constructor
  · rintro ⟨p, l, hpl, h | h⟩
    · exact ⟨p, l, (hdiff p l).mpr hpl, Or.inl ⟨by rw [hpt]; exact h.1, by rw [hln]; exact h.2⟩⟩
    · exact ⟨p, l, (hdiff p l).mpr hpl, Or.inr ⟨by rw [hpt]; exact h.2, by rw [hln]; exact h.1⟩⟩
  · rintro ⟨p, l, hpl, h | h⟩
    · exact ⟨p, l, (hdiff p l).mp hpl, Or.inl ⟨by rw [← hpt]; exact h.1, by rw [← hln]; exact h.2⟩⟩
    · exact ⟨p, l, (hdiff p l).mp hpl, Or.inr ⟨by rw [← hln]; exact h.2, by rw [← hpt]; exact h.1⟩⟩

theorem gfun_iff (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hA : ∀ u v : Fin 26, G.Adj u v ↔ adj u v) (x : Fin 26 → Bool) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true ↔
      ∃ u v : Fin 26, adj u v ∧ x u = true ∧ x v = true := by
  unfold PEqualNP.MetaComplexity.NestedCover.graphFun
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · rintro (⟨a, ha, _⟩ | ⟨u, v, h, hu, hv⟩)
    · simp at ha
    · exact ⟨u, v, (hA u v).mp h, hu, hv⟩
  · rintro ⟨u, v, h, hu, hv⟩
    exact Or.inr ⟨u, v, (hA u v).mpr h, hu, hv⟩

theorem fp_stmt (x : Fin 26 → Bool) :
    (∃ u v : Fin 26, adj u v ∧ x u = true ∧ x v = true) ↔
      ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    obtain ⟨p, l, hpl, h1 | h1⟩ := (adj_stmt u v).mp h
    · exact ⟨p, l, hpl, by rw [← h1.1]; exact hu, by rw [← h1.2]; exact hv⟩
    · exact ⟨p, l, hpl, by rw [← h1.1]; exact hv, by rw [← h1.2]; exact hu⟩
  · rintro ⟨p, l, hpl, hp, hl⟩
    exact ⟨Fin.castAdd 13 p, Fin.natAdd 13 l,
      (adj_stmt _ _).mpr ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩

theorem good_of (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit)
    (hA : ∀ u v : Fin 26, G.Adj u v ↔ adj u v)
    (hAO : PEqualNP.TopForm.IsAO2 26 C)
    (hfun : PEqualNP.MetaComplexity.circuitFun 26 C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (hjunk : PEqualNP.TopForm.junk G C = ∅) : Good C := by
  have hval : ∀ x : Fin 26 → Bool,
      val C 26 x C.output = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := by
    intro x
    exact congrFun hfun x
  have hF := gfun_iff G hA
  have hrejF : ∀ u : Fin 26,
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (e1 u) = false := by
    intro u
    cases hc : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (e1 u)
    · rfl
    · exfalso
      obtain ⟨a, b, hab, ha, hb⟩ := (hF (e1 u)).mp hc
      rw [e1_mem u a ha, e1_mem u b hb] at hab
      exact adj_irr u hab
  have hout1 : 26 ≤ C.output := by
    by_contra hlt
    have hlt' : C.output < 26 := by omega
    have h1 := hval (e1 ⟨C.output, hlt'⟩)
    rw [val_input C 26 _ C.output hlt', hrejF] at h1
    simp [e1] at h1
  have hout2 : C.output - 26 < C.gates.length := by
    by_contra hge
    have hnone : C.gates[C.output - 26]? = none := List.getElem?_eq_none (by omega)
    have h1 := hval (e2 (pt 0) (ln 0))
    have h2 : val C 26 (e2 (pt 0) (ln 0)) (26 + (C.output - 26)) = false :=
      val_none C 26 _ _ hnone
    rw [show 26 + (C.output - 26) = C.output by omega] at h2
    rw [h2] at h1
    have h3 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (e2 (pt 0) (ln 0)) = true :=
      (hF _).mpr ⟨pt 0, ln 0, (adj_pl 0 0).mpr (by decide), e2_left _ _, e2_right _ _⟩
    rw [h3] at h1
    exact Bool.false_ne_true h1
  have hoeq : 26 + oG C = C.output := by
    unfold oG
    omega
  refine ⟨fun j hj => ao2_back C hAO j hj, fun x j hj ha => vl_gate_and C hAO x j hj ha,
    fun x j hj ha => vl_gate_or C hAO x j hj ha, hout2, ?_, ?_, ?_⟩
  · intro u v huv
    unfold vl
    rw [hoeq, hval]
    exact (hF _).mpr ⟨u, v, huv, e2_left u v, e2_right u v⟩
  · intro u
    unfold vl
    rw [hoeq, hval]
    exact hrejF u
  · intro j hj ha x hx
    by_contra hno
    have hfalse : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false := by
      cases hc : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
      · rfl
      · exact absurd ((hF x).mp hc) hno
    have hmem : j ∈ PEqualNP.TopForm.junk G C := by
      unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ha, hj, x, hx, hfalse⟩
    rw [hjunk] at hmem
    simp at hmem

theorem cone_path (C : Circuit)
    (hin : ∀ j, j < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [gA C j, gB C j])
    (i : ℕ) : ∀ j, j < C.gates.length → PEqualNP.EdgeOwnership.InCone 26 C i j →
      Relation.TransGen (Rdv C) j i := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hc
    have hc' : i ∈ cn 26 C.gates j := hc
    rw [cn_mem 26 C.gates j _ (gateAt_get C j hj) i] at hc'
    obtain ⟨w, hw, h1, h2, h3⟩ := hc'
    rw [hin j hj] at hw
    have hr : Rdv C j (w - 26) := by
      refine ⟨hj, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with hw | hw
      · left
        omega
      · right
        omega
    rcases h3 with h3 | h3
    · rw [h3]
      exact Relation.TransGen.single hr
    · exact Relation.TransGen.head hr (ih (w - 26) (by omega) (by omega) h3)

theorem main (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit)
    (hadj : ∀ (x4 x5 : Fin 26), G.Adj x4 x5 ↔ ∃ (x6 : Fin 13) (x7 : Fin 13),
      (x6 = x7 ∨ x6 = x7 + 1 ∨ x6 = x7 + 3 ∨ x6 = x7 + 9) ∧
      (x4 = Fin.castAdd 13 x6 ∧ x5 = Fin.natAdd 13 x7 ∨
        x5 = Fin.castAdd 13 x6 ∧ x4 = Fin.natAdd 13 x7))
    (hleast : PEqualNP.TopForm.IsLeastAO G C) (hjunk : PEqualNP.TopForm.junk G C = ∅) :
    PEqualNP.TopForm.andPairs 26 C = 0 := by
  have hA : ∀ u v : Fin 26, G.Adj u v ↔ adj u v :=
    fun u v => (hadj u v).trans (adj_stmt u v).symm
  obtain ⟨hAO, hfun, hmin⟩ := hleast
  have hG : Good C := good_of G C hA hAO hfun hjunk
  have hs : C.gates.length ≤ 64 := by
    obtain ⟨S, hS1, hS2, hS3⟩ := star_circuit
    have hSf : PEqualNP.MetaComplexity.circuitFun 26 S =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      rw [gfun_iff G hA x, fp_stmt x]
      exact hS3 x
    have hle := hmin S hS1 hSf
    rw [hS2] at hle
    exact hle
  by_contra hne
  have hpos : 0 < PEqualNP.TopForm.andPairs 26 C := Nat.pos_of_ne_zero hne
  unfold PEqualNP.TopForm.andPairs at hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  let _inst : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  obtain ⟨hmem, ha1, ha2, hc⟩ := Finset.mem_filter.mp hp
  obtain ⟨hm1, hm2⟩ := Finset.mem_product.mp hmem
  have h1 := Finset.mem_range.mp hm1
  have h2 := Finset.mem_range.mp hm2
  exact core C hG hs p.1 p.2 h1 h2 ha1 ha2
    (cone_path C (fun j hj => ao2_inputs C hAO j hj) p.1 p.2 h2 hc)

end PEqualNP.Outside.L_meta_2393_aux

theorem PEqualNP.Outside.L_meta_2393 : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 = ∅ → PEqualNP.TopForm.andPairs (26 : ℕ) x3 = (0 : ℕ) := by
  intro x1 x2 x3 h hl hj
  exact @PEqualNP.Outside.L_meta_2393_aux.main x1 x2 x3 h hl hj
