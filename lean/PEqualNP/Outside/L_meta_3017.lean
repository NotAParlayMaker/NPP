import Mathlib
import PEqualNP.Defs

-- Fork-share removal. Write F for the edge function of G and red for the map sending the wire
-- of gate c to the bit s. Gate c is true at the unit vector of s, so it is above the bit s, the
-- redirected circuit C0 is below C, and they agree wherever gate c equals the bit s. An edge zy
-- is lost when C0 is false at its pair vector: then gate c is true there and s is neither z nor y.
-- (1) Gate c is true at the pair vector of a lost edge zy and false at the unit vector of z, so
-- its cone reads the bit y, and it reads the bit s; a cone of k gates of fan-in two reads at most
-- k + 1 bits (count the operand slots), so the vertices on lost edges are at most k.
-- (2) Walking down from the output at a lost edge through the gates that fall under the redirect
-- reaches a top AND with an operand above gate c; the last hypothesis makes the other operand true
-- at one of the two vertices, so that vertex is adjacent to s. The 2-colouring and the absence of
-- 4-cycles make the lost edges stars centred at neighbours of s. The cone of c is unread in C0:
-- delete it (top index first, renaming wires) and append, for each star, an OR chain of the
-- leaves, an AND with the centre and an OR with the running output.

namespace PEqualNP.Outside.L_meta_3017

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.SplitCount

-- Wire values of a gate list and the deletion of one gate: after L_meta_2006.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

lemma wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wiresFrom (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false) := by
  have h1 : wiresFrom (pre ++ g :: post) X = wiresFrom post
      (wiresFrom pre X ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre X).length = n + pre.length := by
    rw [length_wiresFrom]; omega
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

-- The value of wire w.
def V (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (wiresFrom gs x).getD w false

lemma V_app (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
    V (pre ++ post) x w = V pre x w := by
  unfold V
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; exact h)]

lemma gate_val_aux {n : ℕ} (gs : List Gate) (x : List Bool) (hx : x.length = n) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < n + i) :
    V gs x (n + i) = g.op.eval (g.inputs.map (V gs x)) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := split_at gs i g hg
  subst hsplit
  subst hlen
  have h1 : V (pre ++ g :: post) x (n + pre.length)
      = g.op.eval (g.inputs.map fun w => (wiresFrom pre x).getD w false) :=
    wire_at n pre post g x hx
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro w hwm
  exact (V_app pre (g :: post) x w (by rw [hx]; exact hw w hwm)).symm

lemma V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)

lemma V_inp (gs : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
    V gs x w = x.getD w false := by
  unfold V
  rw [getD_wiresFrom _ _ _ h]

-- Wire renaming after the deletion of gate j.
def sg (n : ℕ) (j : ℕ) (u : ℕ) : ℕ := if n + j < u then u - 1 else u

lemma sg_le (n j u : ℕ) (h : u ≤ n + j) : sg n j u = u := by
  have h' : ¬ n + j < u := by omega
  simp [sg, h']

lemma sg_gt (n j u : ℕ) (h : n + j < u) : sg n j u = u - 1 := by
  simp [sg, h]

def sh (n j : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sg n j)⟩

def del (n : ℕ) (j : ℕ) (gs : List Gate) : List Gate :=
  (gs.eraseIdx j).map (sh n j)

lemma del_get (n : ℕ) (j : ℕ) (gs : List Gate) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hij : i ≠ j) :
    ∃ i', sg n j (n + i) = n + i' ∧ (del n j gs)[i']? = some (sh n j g) ∧
      ((i' = i ∧ i < j) ∨ (i' + 1 = i ∧ j ≤ i')) := by
  by_cases h : i < j
  · refine ⟨i, sg_le n j _ (by omega), ?_, Or.inl ⟨rfl, h⟩⟩
    simp [del, List.getElem?_eraseIdx, h, hg]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : ¬ k < j := by omega
    refine ⟨k, ?_, ?_, Or.inr ⟨rfl, by omega⟩⟩
    · rw [sg_gt n j _ (by omega)]; omega
    · simp [del, List.getElem?_eraseIdx, hk, hg]

lemma del_inv (n : ℕ) (j : ℕ) (gs : List Gate) (i' : ℕ) (g' : Gate)
    (h : (del n j gs)[i']? = some g') :
    ∃ i g, gs[i]? = some g ∧ g' = sh n j g ∧ ((i' = i ∧ i < j) ∨ (i' + 1 = i ∧ j ≤ i')) := by
  by_cases h3 : i' < j
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i', g, hg, rfl, Or.inl ⟨rfl, h3⟩⟩
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i' + 1, g, hg, rfl, Or.inr ⟨rfl, by omega⟩⟩

def Back (n : ℕ) (gs : List Gate) : Prop :=
  ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < n + i

lemma del_back (n : ℕ) (j : ℕ) (gs : List Gate)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < n + i ∧ u ≠ n + j) :
    Back n (del n j gs) := by
  intro i' g' h
  obtain ⟨i, g, hg, rfl, hi⟩ := del_inv n j gs i' g' h
  intro u hu
  simp only [sh, List.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have h1 := hfb i g hg v hv
  unfold sg
  split_ifs <;> omega

lemma del_val (n : ℕ) (j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (x : List Bool) (hx : x.length = n)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < n + i ∧ u ≠ n + j) :
    ∀ u, u ≠ n + j → V (del n j gs) x (sg n j u) = V gs x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    have hlen : (del n j gs).length = gs.length - 1 := by
      simp [del, List.length_eraseIdx, hj]
    by_cases h1 : u < n
    · rw [sg_le n j u (by omega), V_inp _ x u (by omega), V_inp _ x u (by omega)]
    · obtain ⟨i, rfl⟩ : ∃ i, u = n + i := ⟨u - n, by omega⟩
      have hij : i ≠ j := by omega
      by_cases h2 : i < gs.length
      · have hg : gs[i]? = some gs[i] := List.getElem?_eq_getElem h2
        obtain ⟨i', hs, hd, _⟩ := del_get n j gs i gs[i] hg hij
        rw [hs, gate_val_aux _ x hx i' _ hd (del_back n j gs hfb i' _ hd),
          gate_val_aux gs x hx i _ hg (fun w hw => (hfb i _ hg w hw).1)]
        simp only [sh, List.map_map]
        congr 1
        apply List.map_congr_left
        intro w hw
        exact ih w (hfb i _ hg w hw).1 (hfb i _ hg w hw).2
      · rw [V_out gs x _ (by omega)]
        apply V_out
        rw [hlen]
        unfold sg
        split_ifs <;> omega
-- Cones and OR closures, gate by gate: after L_meta_1490.
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

lemma gateAt_some {C : Circuit} {i : ℕ} {g : Gate} (h : C.gates[i]? = some g) : gateAt C i = g := by
  simp [gateAt, List.getD_eq_getElem?_getD, h]

lemma gateAt_get {C : Circuit} {i : ℕ} (h : i < C.gates.length) :
    C.gates[i]? = some (gateAt C i) := by
  simp [gateAt, List.getD_eq_getElem?_getD, h]

lemma gateAt_mem {C : Circuit} {i : ℕ} (h : i < C.gates.length) : gateAt C i ∈ C.gates :=
  List.mem_of_getElem? (gateAt_get h)

lemma gateAt_ge {C : Circuit} {i : ℕ} (h : C.gates.length ≤ i) :
    gateAt C i = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma back_of {n : ℕ} {C : Circuit} (h : ReadsBack n C) : Back n C.gates := by
  intro i g hg u hu
  have hi : i < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have e : gateAt C i = g := gateAt_some hg
  exact h i hi u (e ▸ hu)

lemma inCone_lt {n : ℕ} {C : Circuit} : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with rfl | h3
    · exact hk
    · exact lt_trans (ih k hk i h3) hk

lemma inCone_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length :=
  ((inCone_iff n C i j).mp h).1

lemma inCone_read {n : ℕ} {C : Circuit} {j k : ℕ} (hj : j < C.gates.length) (hk : k < j)
    (h : n + k ∈ (gateAt C j).inputs) : InCone n C k j :=
  (inCone_iff n C k j).mpr ⟨hj, k, hk, h, Or.inl rfl⟩

lemma inCone_trans {n : ℕ} {C : Circuit} {a b : ℕ} (hab : InCone n C a b) :
    ∀ c, InCone n C b c → InCone n C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro h
    obtain ⟨hc, k, hk, hin, h3⟩ := (inCone_iff n C b c).mp h
    rcases h3 with rfl | h3
    · exact (inCone_iff n C a c).mpr ⟨hc, b, hk, hin, Or.inr hab⟩
    · exact (inCone_iff n C a c).mpr ⟨hc, k, hk, hin, Or.inr (ih k hk h3)⟩

lemma inCone_parent {n : ℕ} {C : Circuit} : ∀ j i, InCone n C i j →
    ∃ k, (k = j ∨ InCone n C k j) ∧ k < C.gates.length ∧ i < k ∧
      n + i ∈ (gateAt C k).inputs := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨hj, k, hk, hin, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with rfl | h3
    · exact ⟨j, Or.inl rfl, hj, hk, hin⟩
    · obtain ⟨k', hk', hlen, hlt, hin'⟩ := ih k hk i h3
      refine ⟨k', Or.inr ?_, hlen, hlt, hin'⟩
      have hkj : InCone n C k j := inCone_read hj hk hin
      rcases hk' with rfl | hk'
      · exact hkj
      · exact inCone_trans hk' j hkj

-- Monotone operations: after L_meta_1490.
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

lemma opMono_rev : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

lemma eval_and_map (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ u ∈ l, f u = true := by
  simp [GateOp.eval]

lemma eval_or_map (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ u ∈ l, f u = true := by
  simp [GateOp.eval]

def AOp (gs : List Gate) : Prop := ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

-- Two gate lists of one shape, the second reading through a wire map: values stay related.
lemma V_sim {n : ℕ} (R : Bool → Bool → Prop) (hR : OpMono R) (hff : R false false)
    (gs gs' : List Gate) (ρ : ℕ → ℕ) (x x' : List Bool) (hx : x.length = n) (hx' : x'.length = n)
    (hB : Back n gs) (hB' : Back n gs') (hAO : AOp gs)
    (hlen : gs'.length = gs.length)
    (hg : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → gs'[i]? = some (⟨g.op, g.inputs.map ρ⟩ : Gate))
    (hin : ∀ w, w < n → R (x.getD w false) (x'.getD w false))
    (hρ : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, ρ u ≠ u →
      R (V gs x u) (V gs' x' (ρ u))) :
    ∀ w, R (V gs x w) (V gs' x' w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < n
    · rw [V_inp _ x w (by omega), V_inp _ x' w (by omega)]
      exact hin w h1
    · obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
      by_cases h2 : i < gs.length
      · have hgi : gs[i]? = some gs[i] := List.getElem?_eq_getElem h2
        have hgi' := hg i _ hgi
        rw [gate_val_aux gs x hx i _ hgi (hB i _ hgi),
          gate_val_aux gs' x' hx' i _ hgi' (hB' i _ hgi')]
        simp only [List.map_map]
        apply hR _ (hAO _ (List.mem_of_getElem? hgi))
        intro u hu
        by_cases hu' : ρ u = u
        · simp only [Function.comp_apply, hu']
          exact ih u (hB i _ hgi u hu)
        · exact hρ i _ hgi u hu hu'
      · rw [V_out gs x _ (by omega), V_out gs' x' _ (by omega)]
        exact hff

-- Every wire of an AND/OR gate list is monotone in the bits.
lemma V_mono {n : ℕ} (gs : List Gate) (x x' : List Bool) (hx : x.length = n) (hx' : x'.length = n)
    (hB : Back n gs) (hAO : AOp gs)
    (hin : ∀ w, w < n → x.getD w false = true → x'.getD w false = true) :
    ∀ w, V gs x w = true → V gs x' w = true := by
  apply V_sim (fun a b => a = true → b = true) opMono_imp (fun h => h) gs gs id x x' hx hx' hB hB
    hAO rfl _ hin
  · intro i g hg u hu h
    exact (h rfl).elim
  · intro i g hg
    rw [hg, List.map_id]

-- The redirect of every read of wire n + c to the wire s.
def rdw (n c s : ℕ) (w : ℕ) : ℕ := if w = n + c then s else w

def rdg (n c s : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rdw n c s)⟩

lemma rd_get {n c s : ℕ} (gs : List Gate) (i : ℕ) (g : Gate) (h : gs[i]? = some g) :
    (gs.map (rdg n c s))[i]? = some (rdg n c s g) := by
  simp [h]

lemma rd_inv {n c s : ℕ} (gs : List Gate) (i : ℕ) (g' : Gate)
    (h : (gs.map (rdg n c s))[i]? = some g') : ∃ g, gs[i]? = some g ∧ g' = rdg n c s g := by
  rw [List.getElem?_map] at h
  cases hgi : gs[i]? with
  | none => rw [hgi] at h; simp at h
  | some g =>
    rw [hgi] at h
    simp at h
    exact ⟨g, rfl, h.symm⟩

lemma rd_back {n c s : ℕ} (hs : s < n) (gs : List Gate) (hB : Back n gs) :
    Back n (gs.map (rdg n c s)) := by
  intro i g' h u hu
  obtain ⟨g, hg, rfl⟩ := rd_inv gs i g' h
  simp only [rdg, List.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have := hB i g hg v hv
  unfold rdw
  split_ifs <;> omega

lemma rd_le {n c s : ℕ} (hs : s < n) (gs : List Gate) (hB : Back n gs) (hAO : AOp gs)
    (x : List Bool) (hx : x.length = n)
    (hcs : x.getD s false = true → V gs x (n + c) = true) :
    ∀ w, V (gs.map (rdg n c s)) x w = true → V gs x w = true := by
  apply V_sim (fun a b => b = true → a = true) opMono_rev (fun h => h) gs (gs.map (rdg n c s))
    (rdw n c s) x x hx hx hB (rd_back hs gs hB) hAO (by simp) (fun i g h => rd_get gs i g h)
    (fun w _ h => h)
  intro i g hg u hu hne
  have huc : u = n + c := by
    by_contra h; exact hne (by simp [rdw, h])
  subst huc
  have e : rdw n c s (n + c) = s := by simp [rdw]
  rw [e, V_inp _ x s (by omega)]
  exact hcs

lemma rd_eq {n c s : ℕ} (hs : s < n) (gs : List Gate) (hB : Back n gs) (hAO : AOp gs)
    (x : List Bool) (hx : x.length = n)
    (hcs : V gs x (n + c) = x.getD s false) :
    ∀ w, V gs x w = V (gs.map (rdg n c s)) x w := by
  apply V_sim Eq opMono_eq rfl gs (gs.map (rdg n c s))
    (rdw n c s) x x hx hx hB (rd_back hs gs hB) hAO (by simp) (fun i g h => rd_get gs i g h)
    (fun w _ => rfl)
  intro i g hg u hu hne
  have huc : u = n + c := by
    by_contra h; exact hne (by simp [rdw, h])
  subst huc
  have e : rdw n c s (n + c) = s := by simp [rdw]
  rw [e, V_inp _ x s (by omega)]
  exact hcs

lemma rd_step {n c s : ℕ} (hs : s < n) (gs : List Gate) (hB : Back n gs) (hAO : AOp gs)
    (x : List Bool) (hx : x.length = n) (i : ℕ) (g : Gate) (hg : gs[i]? = some g)
    (h1 : V gs x (n + i) = true) (h0 : V (gs.map (rdg n c s)) x (n + i) = false) :
    ∃ u ∈ g.inputs, V gs x u = true ∧ V (gs.map (rdg n c s)) x (rdw n c s u) = false := by
  rw [gate_val_aux gs x hx i g hg (hB i g hg)] at h1
  rw [gate_val_aux _ x hx i _ (rd_get gs i g hg) (rd_back hs gs hB i _ (rd_get gs i g hg))] at h0
  simp only [rdg, List.map_map] at h0
  rcases hAO g (List.mem_of_getElem? hg) with hop | hop
  · rw [hop] at h1 h0
    rw [eval_and_map] at h1
    have hne : ¬ (∀ u ∈ g.inputs, (V (gs.map (rdg n c s)) x ∘ rdw n c s) u = true) := by
      rw [← eval_and_map, h0]; simp
    push Not at hne
    obtain ⟨u, hu, hf⟩ := hne
    exact ⟨u, hu, h1 u hu, by simpa using hf⟩
  · rw [hop] at h1 h0
    rw [eval_or_map] at h1
    obtain ⟨u, hu, hu1⟩ := h1
    have hne : ¬ (∃ u ∈ g.inputs, (V (gs.map (rdg n c s)) x ∘ rdw n c s) u = true) := by
      rw [← eval_or_map, h0]; simp
    push Not at hne
    exact ⟨u, hu, hu1, by simpa using hne u hu⟩

-- Every node of the OR tree is below its root.
lemma tree_up {n : ℕ} {C : Circuit} {T L : Finset ℕ} {ρ : ℕ} (hRB : ReadsBack n C)
    (hT : IsOrTree n C T L ρ) (x : List Bool) (hx : x.length = n) :
    ∀ m w, n + C.gates.length - w ≤ m → (w ∈ L ∨ (n ≤ w ∧ w - n ∈ T)) →
      V C.gates x w = true → V C.gates x ρ = true := by
  intro m
  induction m with
  | zero =>
    intro w hm hw hv
    rw [V_out _ x w (by omega)] at hv; cases hv
  | succ m ih =>
    intro w hm hw hv
    by_cases hwρ : w = ρ
    · rw [← hwρ]; exact hv
    · have hreads : readsIn C T w = 1 := by
        rcases hw with hw | ⟨hw1, hw2⟩
        · have h := (hT.2.1 w hw).2
          simpa [hwρ] using h
        · have h := hT.2.2.1 (w - n) hw2
          rw [show n + (w - n) = w by omega] at h
          simpa [hwρ] using h
      have hex : ∃ j ∈ T, w ∈ (gateAt C j).inputs := by
        by_contra hcon
        push Not at hcon
        have h0 : readsIn C T w = 0 := by
          unfold readsIn
          apply Finset.sum_eq_zero
          intro j hj
          exact List.count_eq_zero.mpr (hcon j hj)
        omega
      obtain ⟨j, hjT, hjw⟩ := hex
      obtain ⟨hjop, hjlen, _⟩ := hT.1 j hjT
      have hj : j < C.gates.length := by
        by_contra hge
        rw [gateAt_ge (by omega)] at hjlen
        simp at hjlen
      have hwj : w < n + j := hRB j hj w hjw
      have hvj : V C.gates x (n + j) = true := by
        rw [gate_val_aux C.gates x hx j _ (gateAt_get hj) (hRB j hj), hjop, eval_or_map]
        exact ⟨w, hjw, hv⟩
      exact ih (n + j) (by omega)
        (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hjT⟩) hvj

-- A wire that reaches gate c through OR gates is above gate c.
lemma orReaches_val {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (x : List Bool)
    (hx : x.length = n) (c : ℕ) (hv : V C.gates x (n + c) = true) :
    ∀ k, OrReaches n C (n + k) c → V C.gates x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k c).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hik, hic⟩
    · exact hv
    · have hni : n ≤ i := hic.1
      obtain ⟨r, rfl⟩ : ∃ r, i = n + r := ⟨i - n, by omega⟩
      have hr := ih r (by omega) hic
      rw [gate_val_aux C.gates x hx k _ (gateAt_get hk) (hRB k hk), hop, eval_or_map]
      exact ⟨n + r, hi, hr⟩

lemma outCone_down {n : ℕ} {C : Circuit} {k r : ℕ} (h : InOutputCone n C k)
    (hr : InCone n C r k) : InOutputCone n C r := by
  obtain ⟨hk, h⟩ := h
  refine ⟨lt_trans (inCone_lt k r hr) hk, Or.inr ?_⟩
  rcases h with h | ⟨h1, h2⟩
  · refine ⟨by omega, ?_⟩
    rw [h, Nat.add_sub_cancel_left]; exact hr
  · exact ⟨h1, inCone_trans hr _ h2⟩

-- Walking down from a gate that falls under the redirect, through OR gates, to gate c.
lemma chain {n : ℕ} {C : Circuit} {T L : Finset ℕ} {c s : ℕ} (hs : s < n)
    (hRB : ReadsBack n C) (hAO : AOp C.gates) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hT : IsOrTree n C T L C.output)
    (hL : ∀ w ∈ L, n ≤ w ∧ (gateAt C (w - n)).op = GateOp.and)
    (hc : c < C.gates.length) (hcT : c ∉ T) (hcL : n + c ∉ L)
    (hpriv : ∀ k < C.gates.length, InCone n C c k → InOutputCone n C k →
      k ∈ T ∨ n + k ∈ L ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ w ∈ L, ∃ a ∈ (gateAt C (w - n)).inputs, OrReaches n C a k))
    (x : List Bool) (hx : x.length = n) (P : Prop)
    (hP : ∀ w ∈ L, ∀ a b : ℕ, ((gateAt C (w - n)).inputs = [a, b] ∨
        (gateAt C (w - n)).inputs = [b, a]) →
      OrReaches n C a c → V C.gates x (n + (w - n)) = true → P) :
    ∀ k, k < C.gates.length → V C.gates x (n + k) = true →
      V (C.gates.map (rdg n c s)) x (n + k) = false → InOutputCone n C k →
      P ∨ ((k = c ∨ ((gateAt C k).op = GateOp.or ∧ k ∉ T)) ∧ OrReaches n C (n + k) c ∧
        (k = c ∨ InCone n C c k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk h1 h0 hout
    by_cases hkc : k = c
    · subst hkc
      exact Or.inr ⟨Or.inl rfl, (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, Or.inl rfl⟩
    · have hgk := gateAt_get hk
      obtain ⟨u, hu, hu1, hu0⟩ := rd_step hs C.gates (back_of hRB) hAO x hx k _ hgk h1 h0
      have hult : u < n + k := hRB k hk u hu
      have key : P ∨ ∃ r, r < k ∧ n + r ∈ (gateAt C k).inputs ∧ OrReaches n C (n + r) c ∧
          InCone n C c k ∧ r ∉ T ∧ n + r ∉ L := by
        by_cases huc : u = n + c
        · subst huc
          have hck : c < k := by omega
          exact Or.inr ⟨c, hck, hu, (orReaches_iff n C c c).mpr ⟨hc, Or.inl rfl⟩,
            inCone_read hk hck hu, hcT, hcL⟩
        · have e : rdw n c s u = u := by simp [rdw, huc]
          rw [e] at hu0
          have hun : n ≤ u := by
            by_contra hlt
            push Not at hlt
            rw [V_inp _ x u (by omega)] at hu1 hu0
            rw [hu1] at hu0; cases hu0
          obtain ⟨r, rfl⟩ : ∃ r, u = n + r := ⟨u - n, by omega⟩
          have hrk : r < k := by omega
          have hrlen : r < C.gates.length := by omega
          have hrk' : InCone n C r k := inCone_read hk hrk hu
          have hrout : InOutputCone n C r := outCone_down hout hrk'
          rcases ih r hrk hrlen hu1 hu0 hrout with hP' | ⟨hr1, hr2, hr3⟩
          · exact Or.inl hP'
          · refine Or.inr ⟨r, hrk, hu, hr2, ?_, ?_, ?_⟩
            · rcases hr3 with rfl | hr3
              · exact hrk'
              · exact inCone_trans hr3 k hrk'
            · rcases hr1 with rfl | ⟨_, hrT⟩
              · exact hcT
              · exact hrT
            · rcases hr1 with rfl | ⟨hrop, _⟩
              · exact hcL
              · intro hmem
                have hand := (hL _ hmem).2
                rw [Nat.add_sub_cancel_left] at hand
                rw [hand] at hrop; cases hrop
      rcases key with hP' | ⟨r, hrk, hrin, hror, hck, hrT, hrL⟩
      · exact Or.inl hP'
      · by_cases hkT : k ∈ T
        · exfalso
          rcases (hT.1 k hkT).2.2 (n + r) hrin with h | ⟨_, h⟩
          · exact hrL h
          · rw [Nat.add_sub_cancel_left] at h; exact hrT h
        · by_cases hkL : n + k ∈ L
          · left
            have hlen2 := h2 _ (gateAt_mem hk)
            obtain ⟨p, q, hpq⟩ : ∃ p q, (gateAt C k).inputs = [p, q] :=
              List.length_eq_two.mp hlen2
            have e : n + k - n = k := by omega
            rw [hpq] at hrin
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hrin
            rcases hrin with h | h
            · refine hP (n + k) hkL (n + r) q (Or.inl ?_) hror ?_
              · rw [e, hpq, h]
              · rw [e]; exact h1
            · refine hP (n + k) hkL (n + r) p (Or.inr ?_) hror ?_
              · rw [e, hpq, h]
              · rw [e]; exact h1
          · rcases hpriv k hk hck hout with h | h | ⟨hop, _⟩
            · exact (hkT h).elim
            · exact (hkL h).elim
            · exact Or.inr ⟨Or.inr ⟨hop, hkT⟩,
                (orReaches_iff n C k c).mpr ⟨hk, Or.inr ⟨hop, n + r, hrin, by omega, hror⟩⟩,
                Or.inr hck⟩

-- At an input where the redirect makes the output fall, a top AND reads gate c through ORs.
lemma lost_good {n : ℕ} {C : Circuit} {T L : Finset ℕ} {c s : ℕ} (hs : s < n)
    (hRB : ReadsBack n C) (hAO : AOp C.gates) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hT : IsOrTree n C T L C.output)
    (hL : ∀ w ∈ L, n ≤ w ∧ (gateAt C (w - n)).op = GateOp.and)
    (hc : c < C.gates.length) (hcT : c ∉ T) (hcL : n + c ∉ L) (hco : C.output ≠ n + c)
    (hpriv : ∀ k < C.gates.length, InCone n C c k → InOutputCone n C k →
      k ∈ T ∨ n + k ∈ L ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ w ∈ L, ∃ a ∈ (gateAt C (w - n)).inputs, OrReaches n C a k))
    (x : List Bool) (hx : x.length = n) (P : Prop)
    (hP : ∀ w ∈ L, ∀ a b : ℕ, ((gateAt C (w - n)).inputs = [a, b] ∨
        (gateAt C (w - n)).inputs = [b, a]) →
      OrReaches n C a c → V C.gates x (n + (w - n)) = true → P)
    (h1 : V C.gates x C.output = true)
    (h0 : V (C.gates.map (rdg n c s)) x C.output = false) : P := by
  have hon : n ≤ C.output := by
    by_contra hlt
    push Not at hlt
    rw [V_inp _ x _ (by omega)] at h1 h0
    rw [h1] at h0; cases h0
  have holen : C.output < n + C.gates.length := by
    by_contra hge
    push Not at hge
    rw [V_out _ x _ (by omega)] at h1; cases h1
  obtain ⟨o, ho⟩ : ∃ o, C.output = n + o := ⟨C.output - n, by omega⟩
  have hol : o < C.gates.length := by omega
  rw [ho] at h1 h0
  rcases chain hs hRB hAO h2 hT hL hc hcT hcL hpriv x hx P hP o hol h1 h0 ⟨hol, Or.inl ho⟩ with
    hP' | ⟨hr1, _, _⟩
  · exact hP'
  · exfalso
    rcases hr1 with rfl | ⟨hop, hoT⟩
    · exact hco ho
    · have h4 := hT.2.2.2
      by_cases hTe : T = ∅
      · simp only [hTe, ite_true] at h4
        have hmem : C.output ∈ L := by rw [h4]; simp
        have hand := (hL _ hmem).2
        rw [ho, Nat.add_sub_cancel_left] at hand
        rw [hand] at hop; cases hop
      · simp only [hTe, ite_false] at h4
        obtain ⟨j, hj, hjo⟩ := h4
        have : o = j := by omega
        subst this
        exact hoT hj

-- Bits of an input given as a function.
lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp [List.getD_eq_getElem?_getD, hw]

lemma getD_ofFn_fin {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

lemma V_ofFn_mono {n : ℕ} (gs : List Gate) (hB : Back n gs) (hAO : AOp gs) (x x' : Fin n → Bool)
    (h : ∀ i, x i = true → x' i = true) :
    ∀ w, V gs (List.ofFn x) w = true → V gs (List.ofFn x') w = true := by
  apply V_mono gs _ _ (by simp) (by simp) hB hAO
  intro w hw
  rw [getD_ofFn x w hw, getD_ofFn x' w hw]
  exact h _

-- Pair inputs and the edge function: after L_meta_1490.
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma unitInput_true {n : ℕ} (p w : Fin n) : unitInput p w = true ↔ w = p := by
  simp [unitInput]

lemma graphFun_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_true]
  simp only [pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma graphFun_unit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : Fin n) :
    graphFun G ∅ (unitInput s) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [graphFun_true] at h
  obtain ⟨a, b, hab, ha, hb⟩ := h
  rw [unitInput_true] at ha hb
  subst ha
  subst hb
  exact G.irrefl hab

-- Gate c is above the bit s.
lemma c_above {n : ℕ} {C : Circuit} {c : ℕ} (s : Fin n) (hRB : ReadsBack n C) (hAO : AOp C.gates)
    (hc1 : V C.gates (List.ofFn (unitInput s)) (n + c) = true) (x : Fin n → Bool)
    (hxs : x s = true) : V C.gates (List.ofFn x) (n + c) = true := by
  refine V_ofFn_mono C.gates (back_of hRB) hAO (unitInput s) x ?_ _ hc1
  intro i hi
  rw [unitInput_true] at hi
  subst hi
  exact hxs

-- The redirected circuit is below the circuit.
lemma rd_le_fn {n : ℕ} {C : Circuit} {c : ℕ} (s : Fin n) (hRB : ReadsBack n C) (hAO : AOp C.gates)
    (hc1 : V C.gates (List.ofFn (unitInput s)) (n + c) = true) (x : Fin n → Bool) :
    ∀ w, V (C.gates.map (rdg n c s)) (List.ofFn x) w = true → V C.gates (List.ofFn x) w = true := by
  apply rd_le s.isLt C.gates (back_of hRB) hAO (List.ofFn x) (by simp)
  intro h
  rw [getD_ofFn_fin] at h
  exact c_above s hRB hAO hc1 x h

-- Where the redirect makes the output fall, gate c is true and the bit s is false.
lemma lost_c {n : ℕ} {C : Circuit} {c : ℕ} (s : Fin n) (hRB : ReadsBack n C) (hAO : AOp C.gates)
    (hc1 : V C.gates (List.ofFn (unitInput s)) (n + c) = true) (x : Fin n → Bool)
    (h1 : V C.gates (List.ofFn x) C.output = true)
    (h0 : V (C.gates.map (rdg n c s)) (List.ofFn x) C.output = false) :
    x s = false ∧ V C.gates (List.ofFn x) (n + c) = true := by
  have key : V C.gates (List.ofFn x) (n + c) ≠ x s := by
    intro hcs
    have e := rd_eq (c := c) s.isLt C.gates (back_of hRB) hAO (List.ofFn x) (by simp)
      (by rw [getD_ofFn_fin]; exact hcs) C.output
    rw [e, h0] at h1
    cases h1
  by_cases hxs : x s = true
  · exact (key (by rw [c_above s hRB hAO hc1 x hxs, hxs])).elim
  · have hxs' : x s = false := by simpa using hxs
    refine ⟨hxs', ?_⟩
    rw [hxs'] at key
    simpa using key

-- A top AND with an operand above gate c and the other operand true at one vertex t.
lemma leaf_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    {T L : Finset ℕ} {c : ℕ} (s : Fin n)
    (hRB : ReadsBack n C) (hAO : AOp C.gates) (hfun : circuitFun n C = graphFun G ∅)
    (hT : IsOrTree n C T L C.output)
    (hL : ∀ w ∈ L, n ≤ w ∧ (gateAt C (w - n)).op = GateOp.and)
    (hc1 : V C.gates (List.ofFn (unitInput s)) (n + c) = true)
    (w : ℕ) (hw : w ∈ L) (a b : ℕ)
    (hin : (gateAt C (w - n)).inputs = [a, b] ∨ (gateAt C (w - n)).inputs = [b, a])
    (hor : OrReaches n C a c) (t : Fin n)
    (hb : V C.gates (List.ofFn (unitInput t)) b = true) : G.Adj s t := by
  have hB := back_of hRB
  have hc' : V C.gates (List.ofFn (pairInput s t)) (n + c) = true :=
    c_above s hRB hAO hc1 _ (by rw [pairInput_true]; exact Or.inl rfl)
  have ha : V C.gates (List.ofFn (pairInput s t)) a = true := by
    have hna : n ≤ a := hor.1
    obtain ⟨k, rfl⟩ : ∃ k, a = n + k := ⟨a - n, by omega⟩
    exact orReaches_val hRB _ (by simp) c hc' k hor
  have hb' : V C.gates (List.ofFn (pairInput s t)) b = true := by
    refine V_ofFn_mono C.gates hB hAO (unitInput t) _ ?_ _ hb
    intro i hi
    rw [unitInput_true] at hi
    rw [pairInput_true]
    exact Or.inr hi
  obtain ⟨hwn, hand⟩ := hL w hw
  have hk : w - n < C.gates.length := by
    by_contra hge
    rw [gateAt_ge (by omega)] at hin
    simp at hin
  have hval : V C.gates (List.ofFn (pairInput s t)) (n + (w - n)) = true := by
    rw [gate_val_aux C.gates _ (by simp) (w - n) _ (gateAt_get hk) (hRB _ hk), hand,
      eval_and_map]
    intro u hu
    rcases hin with h | h <;> rw [h] at hu <;> simp at hu <;> rcases hu with rfl | rfl <;>
      assumption
  rw [show n + (w - n) = w by omega] at hval
  have hout := tree_up hRB hT (List.ofFn (pairInput s t)) (by simp) _ w le_rfl (Or.inl hw) hval
  have hF : circuitFun n C (pairInput s t) = true := hout
  rw [hfun] at hF
  exact (graphFun_pair G s t).mp hF

-- Gate c is no node of the OR tree and is not the output.
lemma c_not_tree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    {T L : Finset ℕ} {c : ℕ} (s : Fin n)
    (hRB : ReadsBack n C) (hfun : circuitFun n C = graphFun G ∅)
    (hT : IsOrTree n C T L C.output)
    (hc1 : V C.gates (List.ofFn (unitInput s)) (n + c) = true) :
    c ∉ T ∧ n + c ∉ L ∧ C.output ≠ n + c := by
  have hF : V C.gates (List.ofFn (unitInput s)) C.output = false := by
    have h : circuitFun n C (unitInput s) = false := by rw [hfun]; exact graphFun_unit G s
    exact h
  have hno : ¬ (n + c ∈ L ∨ (n ≤ n + c ∧ n + c - n ∈ T)) := by
    intro h
    have hout := tree_up hRB hT (List.ofFn (unitInput s)) (by simp) _ (n + c) le_rfl h hc1
    rw [hF] at hout
    cases hout
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hno (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact h⟩)
  · intro h
    exact hno (Or.inl h)
  · intro h
    rw [h, hc1] at hF
    cases hF

-- Every edge lost under the redirect has an end adjacent to s.
lemma lost_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    {T L : Finset ℕ} {c : ℕ} (s : Fin n)
    (hRB : ReadsBack n C) (hAO : AOp C.gates) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hfun : circuitFun n C = graphFun G ∅)
    (hT : IsOrTree n C T L C.output)
    (hL : ∀ w ∈ L, n ≤ w ∧ (gateAt C (w - n)).op = GateOp.and)
    (hc : c < C.gates.length)
    (hc1 : V C.gates (List.ofFn (unitInput s)) (n + c) = true)
    (hpriv : ∀ k < C.gates.length, InCone n C c k → InOutputCone n C k →
      k ∈ T ∨ n + k ∈ L ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ w ∈ L, ∃ a ∈ (gateAt C (w - n)).inputs, OrReaches n C a k))
    (u v : Fin n) (huv : G.Adj u v)
    (hlost : V (C.gates.map (rdg n c s)) (List.ofFn (pairInput u v)) C.output = false)
    (hleaf : ∀ w ∈ L, gateVal n C (w - n) (pairInput u v) = true →
      ∀ a b : ℕ, ((gateAt C (w - n)).inputs = [a, b] ∨ (gateAt C (w - n)).inputs = [b, a]) →
        OrReaches n C a c →
          wireVal n C b (unitInput u) = true ∨ wireVal n C b (unitInput v) = true) :
    G.Adj s u ∨ G.Adj s v := by
  obtain ⟨hcT, hcL, hco⟩ := c_not_tree G s hRB hfun hT hc1
  have h1 : V C.gates (List.ofFn (pairInput u v)) C.output = true := by
    have h : circuitFun n C (pairInput u v) = true := by
      rw [hfun]; exact (graphFun_pair G u v).mpr huv
    exact h
  refine lost_good s.isLt hRB hAO h2 hT hL hc hcT hcL hco hpriv (List.ofFn (pairInput u v))
    (by simp) _ ?_ h1 hlost
  intro w hw a b hin hor hval
  rcases hleaf w hw hval a b hin hor with hb | hb
  · exact Or.inl (leaf_adj G s hRB hAO hfun hT hL hc1 w hw a b hin hor u hb)
  · exact Or.inr (leaf_adj G s hRB hAO hfun hT hL hc1 w hw a b hin hor v hb)

lemma mem_coneSet {n : ℕ} {C : Circuit} {c k : ℕ} :
    k ∈ coneSet n C c ↔ k = c ∨ (k < C.gates.length ∧ InCone n C k c) := by
  simp [coneSet]

-- The value of gate c is fixed by the bits its cone reads.
lemma cone_support {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (c : ℕ) (x x' : List Bool)
    (hx : x.length = n) (hx' : x'.length = n)
    (hagree : ∀ k, (k = c ∨ InCone n C k c) → k < C.gates.length →
      ∀ u ∈ (gateAt C k).inputs, u < n → x.getD u false = x'.getD u false) :
    ∀ k, (k = c ∨ InCone n C k c) → V C.gates x (n + k) = V C.gates x' (n + k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hkl : k < C.gates.length
    · rw [gate_val_aux C.gates x hx k _ (gateAt_get hkl) (hRB k hkl),
        gate_val_aux C.gates x' hx' k _ (gateAt_get hkl) (hRB k hkl)]
      congr 1
      apply List.map_congr_left
      intro u hu
      by_cases hun : u < n
      · rw [V_inp _ x u (by omega), V_inp _ x' u (by omega)]
        exact hagree k hk hkl u hu hun
      · have hult : u < n + k := hRB k hkl u hu
        obtain ⟨j, rfl⟩ : ∃ j, u = n + j := ⟨u - n, by omega⟩
        have hjk : InCone n C j k := inCone_read hkl (by omega) hu
        refine ih j (by omega) (Or.inr ?_)
        rcases hk with rfl | hk
        · exact hjk
        · exact inCone_trans hjk c hk
    · rw [V_out _ x _ (by omega), V_out _ x' _ (by omega)]

lemma support_at {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (c : ℕ) (y : Fin n)
    (hno : ∀ k ∈ coneSet n C c, y.val ∉ (gateAt C k).inputs) (x x' : Fin n → Bool)
    (hxx : ∀ i, i ≠ y → x i = x' i) :
    V C.gates (List.ofFn x) (n + c) = V C.gates (List.ofFn x') (n + c) := by
  refine cone_support hRB c _ _ (by simp) (by simp) ?_ c (Or.inl rfl)
  intro k hk hkl u hu hun
  rw [getD_ofFn x u hun, getD_ofFn x' u hun]
  apply hxx
  intro h
  have hk' : k ∈ coneSet n C c := by
    rw [mem_coneSet]
    rcases hk with rfl | hk
    · exact Or.inl rfl
    · exact Or.inr ⟨hkl, hk⟩
  apply hno k hk'
  rw [← h]
  exact hu

-- A cone of fan-in two gates reads at most one bit more than it has gates.
lemma cone_count {n : ℕ} {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (c : ℕ)
    (hc : c < C.gates.length) (R : Finset ℕ)
    (hR : ∀ u ∈ R, u < n ∧ ∃ k ∈ coneSet n C c, u ∈ (gateAt C k).inputs) :
    R.card ≤ (coneSet n C c).card + 1 := by
  classical
  have hKlen : ∀ k ∈ coneSet n C c, k < C.gates.length := by
    intro k hk
    rw [mem_coneSet] at hk
    rcases hk with rfl | ⟨hk, _⟩
    · exact hc
    · exact hk
  have hcK : c ∈ coneSet n C c := mem_coneSet.mpr (Or.inl rfl)
  have hU : ((coneSet n C c).biUnion (fun k => (gateAt C k).inputs.toFinset)).card
      ≤ (coneSet n C c).card * 2 := by
    refine le_trans Finset.card_biUnion_le ?_
    have := Finset.sum_le_card_nsmul (coneSet n C c)
      (fun k => ((gateAt C k).inputs.toFinset).card) 2 (by
        intro k hk
        have := h2 _ (gateAt_mem (hKlen k hk))
        exact le_trans (List.toFinset_card_le _) (le_of_eq this))
    simpa using this
  have hsub : ((coneSet n C c).erase c).image (fun k => n + k) ∪ R ⊆
      (coneSet n C c).biUnion (fun k => (gateAt C k).inputs.toFinset) := by
    intro w hw
    rw [Finset.mem_union] at hw
    rw [Finset.mem_biUnion]
    rcases hw with hw | hw
    · rw [Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [Finset.mem_erase, mem_coneSet] at hk
      obtain ⟨hkc, hk⟩ := hk
      rcases hk with rfl | ⟨_, hk⟩
      · exact (hkc rfl).elim
      · obtain ⟨k', hk', hlen, _, hin⟩ := inCone_parent c k hk
        refine ⟨k', ?_, by simpa using hin⟩
        rw [mem_coneSet]
        rcases hk' with rfl | hk'
        · exact Or.inl rfl
        · exact Or.inr ⟨hlen, hk'⟩
    · obtain ⟨_, k, hk, hu⟩ := hR w hw
      exact ⟨k, hk, by simpa using hu⟩
  have hdisj : Disjoint (((coneSet n C c).erase c).image (fun k => n + k)) R := by
    rw [Finset.disjoint_left]
    intro w hw hwR
    rw [Finset.mem_image] at hw
    obtain ⟨k, _, rfl⟩ := hw
    have := (hR _ hwR).1
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_erase_of_mem hcK] at hcard
  have hpos : 0 < (coneSet n C c).card := Finset.card_pos.mpr ⟨c, hcK⟩
  omega

-- Conclusion one: the cone has at least as many gates as there are vertices on lost edges.
lemma concl_one {n : ℕ} {C : Circuit} {c : ℕ} (s : Fin n) (hRB : ReadsBack n C)
    (hAO : AOp C.gates) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hc : c < C.gates.length)
    (hc1 : V C.gates (List.ofFn (unitInput s)) (n + c) = true)
    (hc0 : ∀ z : Fin n, z ≠ s → V C.gates (List.ofFn (unitInput z)) (n + c) = false)
    (Y : Finset (Fin n))
    (hY : ∀ y ∈ Y, ∃ z : Fin n, z ≠ s ∧ y ≠ s ∧
      V C.gates (List.ofFn (pairInput z y)) (n + c) = true) :
    Y.card ≤ (coneSet n C c).card := by
  classical
  rcases Finset.eq_empty_or_nonempty Y with hYe | ⟨y0, hy0⟩
  · rw [hYe]; simp
  · obtain ⟨z0, hz0, _, _⟩ := hY y0 hy0
    have hsY : s ∉ Y := by
      intro h
      obtain ⟨_, _, hss, _⟩ := hY s h
      exact hss rfl
    have hreads : ∀ y ∈ insert s Y, ∃ k ∈ coneSet n C c, y.val ∈ (gateAt C k).inputs := by
      intro y hy
      by_contra hcon
      push Not at hcon
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · have e := support_at hRB c y hcon (pairInput z0 y) (unitInput z0) (by
          intro i hi
          simp [pairInput, unitInput, hi])
        rw [c_above y hRB hAO hc1 _ (by rw [pairInput_true]; exact Or.inr rfl), hc0 z0 hz0] at e
        cases e
      · obtain ⟨z, hz, _, hv⟩ := hY y hy
        have e := support_at hRB c y hcon (pairInput z y) (unitInput z) (by
          intro i hi
          simp [pairInput, unitInput, hi])
        rw [hv, hc0 z hz] at e
        cases e
    have hcount := cone_count h2 c hc ((insert s Y).image Fin.val) (by
      intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨y, hy, rfl⟩ := hu
      exact ⟨y.isLt, hreads y hy⟩)
    rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_insert_of_notMem hsY]
      at hcount
    omega

def Good (n : ℕ) (gs : List Gate) : Prop :=
  Back n gs ∧ ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

-- Deleting a set of gates that no other gate reads, top index first.
lemma prune (n : ℕ) (K : Finset ℕ) : ∀ (gs : List Gate) (out : ℕ), Good n gs →
    (∀ k ∈ K, k < gs.length) →
    (∀ (i : ℕ) (g : Gate), gs[i]? = some g → i ∉ K → ∀ u ∈ g.inputs, ∀ k ∈ K, u ≠ n + k) →
    (∀ k ∈ K, out ≠ n + k) →
    ∃ (gs' : List Gate) (out' : ℕ), Good n gs' ∧ gs'.length + K.card = gs.length ∧
      (out < n + gs.length → out' < n + gs'.length) ∧
      ∀ x : List Bool, x.length = n → V gs' x out' = V gs x out := by
  induction K using Finset.induction_on_max with
  | empty =>
    intro gs out hG _ _ _
    exact ⟨gs, out, hG, by simp, fun h => h, fun _ _ => rfl⟩
  | insert a K' hmax ih =>
    intro gs out hG hlen hread hout
    have haK : a ∉ K' := fun h => lt_irrefl a (hmax a h)
    have haI : a ∈ insert a K' := Finset.mem_insert_self a K'
    have ha : a < gs.length := hlen a haI
    have hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < n + i ∧ u ≠ n + a := by
      intro i g hg u hu
      have hb := hG.1 i g hg u hu
      refine ⟨hb, ?_⟩
      by_cases hi : i ∈ insert a K'
      · rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · omega
        · have := hmax i hi
          omega
      · exact hread i g hg hi u hu a haI
    have hG1 : Good n (del n a gs) := by
      refine ⟨del_back n a gs hfb, ?_⟩
      intro g' hg'
      obtain ⟨i', hi'⟩ := List.getElem?_of_mem hg'
      obtain ⟨i, g, hg, rfl, _⟩ := del_inv n a gs i' g' hi'
      have h := hG.2 g (List.mem_of_getElem? hg)
      exact ⟨h.1, by simpa [sh] using h.2⟩
    have hlen1 : (del n a gs).length = gs.length - 1 := by
      simp [del, List.length_eraseIdx, ha]
    have hsgne : ∀ u, u ≠ n + a → (∀ k ∈ K', u ≠ n + k) → ∀ k ∈ K', sg n a u ≠ n + k := by
      intro u hua hu k hk
      have hka := hmax k hk
      have hne := hu k hk
      unfold sg
      split_ifs <;> omega
    have hA : ∀ k ∈ K', k < (del n a gs).length := by
      intro k hk
      have := hmax k hk
      rw [hlen1]
      omega
    have hBr : ∀ (i : ℕ) (g : Gate), (del n a gs)[i]? = some g → i ∉ K' →
        ∀ u ∈ g.inputs, ∀ k ∈ K', u ≠ n + k := by
      intro i' g' hi' hi'K u' hu' k hk
      obtain ⟨i, g, hg, rfl, hi⟩ := del_inv n a gs i' g' hi'
      simp only [sh, List.mem_map] at hu'
      obtain ⟨u, hu, rfl⟩ := hu'
      have hiK : i ∉ insert a K' := by
        rw [Finset.mem_insert]
        rintro (h | h)
        · omega
        · have hia := hmax i h
          rcases hi with ⟨h1, _⟩ | ⟨h1, h2⟩
          · rw [h1] at hi'K
            exact hi'K h
          · omega
      exact hsgne u (hread i g hg hiK u hu a haI)
        (fun k hk => hread i g hg hiK u hu k (Finset.mem_insert_of_mem hk)) k hk
    have hCo : ∀ k ∈ K', sg n a out ≠ n + k :=
      hsgne out (hout a haI) (fun k hk => hout k (Finset.mem_insert_of_mem hk))
    obtain ⟨gs', out', hG', hcard, hov, hval⟩ := ih (del n a gs) (sg n a out) hG1 hA hBr hCo
    refine ⟨gs', out', hG', ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem haK]
      omega
    · intro ho
      apply hov
      have hne := hout a haI
      rw [hlen1]
      unfold sg
      split_ifs <;> omega
    · intro x hx
      rw [hval x hx, del_val n a gs ha x hx hfb out (hout a haI)]

lemma good_snoc {n : ℕ} {gs : List Gate} (hG : Good n gs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (ha : a < n + gs.length)
    (hb : b < n + gs.length) : Good n (gs ++ [⟨op, [a, b]⟩]) := by
  constructor
  · intro i g hg u hu
    by_cases hi : i < gs.length
    · rw [List.getElem?_append_left hi] at hg
      exact hG.1 i g hg u hu
    · rw [List.getElem?_append_right (by omega)] at hg
      have hi0 : i - gs.length = 0 := by
        by_contra h
        rw [List.getElem?_eq_none (by simp; omega)] at hg
        cases hg
      rw [hi0] at hg
      simp at hg
      subst hg
      simp at hu
      rcases hu with rfl | rfl <;> omega
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hG.2 g hg
    · simp at hg
      subst hg
      exact ⟨hop, rfl⟩

lemma V_snoc {n : ℕ} {gs : List Gate} (hG : Good n gs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (ha : a < n + gs.length)
    (hb : b < n + gs.length) (x : List Bool) (hx : x.length = n) :
    V (gs ++ [⟨op, [a, b]⟩]) x (n + gs.length) = op.eval [V gs x a, V gs x b] := by
  have hG' := good_snoc hG op hop a b ha hb
  have hget : (gs ++ [(⟨op, [a, b]⟩ : Gate)])[gs.length]? = some ⟨op, [a, b]⟩ := by simp
  rw [gate_val_aux _ x hx gs.length ⟨op, [a, b]⟩ hget (hG'.1 gs.length _ hget)]
  simp only [List.map_cons, List.map_nil]
  rw [V_app gs _ x a (by omega), V_app gs _ x b (by omega)]

-- An OR chain over a list of bits, started from a wire.
lemma or_chain {n : ℕ} (zs : List ℕ) (hzs : ∀ z ∈ zs, z < n) :
    ∀ (gs : List Gate) (o : ℕ), Good n gs → o < n + gs.length →
    ∃ (t : List Gate) (o' : ℕ), Good n (gs ++ t) ∧ t.length = zs.length ∧
      o' < n + (gs ++ t).length ∧
      ∀ x : List Bool, x.length = n →
        (V (gs ++ t) x o' = true ↔ (V gs x o = true ∨ ∃ z ∈ zs, x.getD z false = true)) := by
  induction zs with
  | nil =>
    intro gs o hG ho
    exact ⟨[], o, by simpa using hG, rfl, by simpa using ho, fun x hx => by simp⟩
  | cons z zs ih =>
    intro gs o hG ho
    have hz : z < n := hzs z (by simp)
    have hG1 := good_snoc hG GateOp.or (Or.inr rfl) o z ho (by omega)
    obtain ⟨t, o', hG', hlen, ho', hval⟩ :=
      ih (fun z' hz' => hzs z' (List.mem_cons_of_mem _ hz'))
        (gs ++ [⟨GateOp.or, [o, z]⟩]) (n + gs.length) hG1 (by simp)
    have e : gs ++ (⟨GateOp.or, [o, z]⟩ : Gate) :: t = (gs ++ [⟨GateOp.or, [o, z]⟩]) ++ t := by
      simp
    refine ⟨⟨GateOp.or, [o, z]⟩ :: t, o', ?_, by simp [hlen], ?_, ?_⟩
    · rw [e]; exact hG'
    · rw [e]; exact ho'
    · intro x hx
      rw [e, hval x hx, V_snoc hG GateOp.or (Or.inr rfl) o z ho (by omega) x hx,
        V_inp gs x z (by omega)]
      simp [GateOp.eval, or_assoc]

-- One star: the centre bit AND an OR of leaf bits, joined to the running output by an OR.
lemma star_add {n : ℕ} (gs : List Gate) (acc y z0 : ℕ) (zs : List ℕ) (hG : Good n gs)
    (hacc : acc < n + gs.length) (hy : y < n) (hz0 : z0 < n) (hzs : ∀ z ∈ zs, z < n) :
    ∃ (gs' : List Gate) (acc' : ℕ), Good n gs' ∧ gs'.length = gs.length + zs.length + 2 ∧
      acc' < n + gs'.length ∧
      ∀ x : List Bool, x.length = n → (V gs' x acc' = true ↔ (V gs x acc = true ∨
        (x.getD y false = true ∧ (x.getD z0 false = true ∨ ∃ z ∈ zs, x.getD z false = true)))) := by
  obtain ⟨t, o, hG1, hlen, ho, hval⟩ := or_chain zs hzs gs z0 hG (by omega)
  have hl1 : (gs ++ t).length = gs.length + zs.length := by simp [hlen]
  have hG2 := good_snoc hG1 GateOp.and (Or.inl rfl) o y ho (by omega)
  have hl2 : ((gs ++ t) ++ [(⟨GateOp.and, [o, y]⟩ : Gate)]).length = gs.length + zs.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen]
  have hG3 := good_snoc hG2 GateOp.or (Or.inr rfl) acc (n + (gs ++ t).length)
    (by rw [hl2]; omega) (by rw [hl2, hl1]; omega)
  refine ⟨((gs ++ t) ++ [⟨GateOp.and, [o, y]⟩]) ++ [⟨GateOp.or, [acc, n + (gs ++ t).length]⟩],
    n + ((gs ++ t) ++ [(⟨GateOp.and, [o, y]⟩ : Gate)]).length, hG3, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
  · simp
  · intro x hx
    rw [V_snoc hG2 GateOp.or (Or.inr rfl) acc (n + (gs ++ t).length)
      (by rw [hl2]; omega) (by rw [hl2, hl1]; omega) x hx,
      V_snoc hG1 GateOp.and (Or.inl rfl) o y ho (by omega) x hx,
      V_app (gs ++ t) _ x acc (by rw [hl1]; omega), V_app gs t x acc (by omega),
      V_app gs t x y (by omega), V_inp gs x y (by omega)]
    have hv := hval x hx
    rw [V_inp gs x z0 (by omega)] at hv
    simp only [GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq,
      Bool.or_false, Bool.and_true, Bool.or_eq_true, Bool.and_eq_true]
    rw [hv]
    tauto

-- All stars.
lemma stars_add {n : ℕ} (Z : Fin n → Finset (Fin n)) (S : Finset (Fin n))
    (hZ : ∀ y ∈ S, (Z y).Nonempty) :
    ∀ (gs : List Gate) (acc : ℕ), Good n gs → acc < n + gs.length →
    ∃ (gs' : List Gate) (acc' : ℕ), Good n gs' ∧
      gs'.length = gs.length + ∑ y ∈ S, ((Z y).card + 1) ∧ acc' < n + gs'.length ∧
      ∀ x : Fin n → Bool, (V gs' (List.ofFn x) acc' = true ↔
        (V gs (List.ofFn x) acc = true ∨ ∃ y ∈ S, x y = true ∧ ∃ z ∈ Z y, x z = true)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro gs acc hG hacc
    exact ⟨gs, acc, hG, by simp, hacc, fun x => by simp⟩
  | insert y S hyS ih =>
    intro gs acc hG hacc
    obtain ⟨gs1, acc1, hG1, hlen1, hacc1, hval1⟩ :=
      ih (fun y' hy' => hZ y' (Finset.mem_insert_of_mem hy')) gs acc hG hacc
    obtain ⟨z0, hz0⟩ := hZ y (Finset.mem_insert_self y S)
    obtain ⟨gs2, acc2, hG2, hlen2, hacc2, hval2⟩ :=
      star_add gs1 acc1 y.val z0.val ((((Z y).erase z0).toList).map Fin.val) hG1 hacc1 y.isLt
        z0.isLt (by
          intro z hz
          rw [List.mem_map] at hz
          obtain ⟨w, _, rfl⟩ := hz
          exact w.isLt)
    refine ⟨gs2, acc2, hG2, ?_, hacc2, ?_⟩
    · have hpos : 0 < (Z y).card := Finset.card_pos.mpr ⟨z0, hz0⟩
      rw [Finset.sum_insert hyS, hlen2, hlen1, List.length_map, Finset.length_toList,
        Finset.card_erase_of_mem hz0]
      omega
    · intro x
      have hlist : (∃ z ∈ (((Z y).erase z0).toList).map Fin.val,
          (List.ofFn x).getD z false = true) ↔ ∃ z ∈ (Z y).erase z0, x z = true := by
        constructor
        · rintro ⟨w, hw, hv⟩
          rw [List.mem_map] at hw
          obtain ⟨z, hz, rfl⟩ := hw
          rw [getD_ofFn_fin] at hv
          exact ⟨z, by simpa using hz, hv⟩
        · rintro ⟨z, hz, hv⟩
          exact ⟨z.val, List.mem_map.mpr ⟨z, by simpa using hz, rfl⟩,
            by rw [getD_ofFn_fin]; exact hv⟩
      rw [hval2 (List.ofFn x) (by simp), hval1 x, hlist, getD_ofFn_fin, getD_ofFn_fin]
      constructor
      · rintro ((h | ⟨y', hy', h⟩) | ⟨hxy, hz⟩)
        · exact Or.inl h
        · exact Or.inr ⟨y', Finset.mem_insert_of_mem hy', h⟩
        · refine Or.inr ⟨y, Finset.mem_insert_self y S, hxy, ?_⟩
          rcases hz with hz | ⟨z, hz, hv⟩
          · exact ⟨z0, hz0, hz⟩
          · exact ⟨z, Finset.mem_of_mem_erase hz, hv⟩
      · rintro (h | ⟨y', hy', hxy, z, hz, hv⟩)
        · exact Or.inl (Or.inl h)
        · rw [Finset.mem_insert] at hy'
          rcases hy' with h | hy'
          · rw [h] at hxy hz
            right
            refine ⟨hxy, ?_⟩
            by_cases hzz : z = z0
            · left
              rw [← hzz]
              exact hv
            · right
              exact ⟨z, Finset.mem_erase.mpr ⟨hzz, hz⟩, hv⟩
          · exact Or.inl (Or.inr ⟨y', hy', hxy, z, hz, hv⟩)

lemma readsBack_of {n : ℕ} {gs : List Gate} (out : ℕ) (h : Back n gs) :
    ReadsBack n ⟨gs, out⟩ := by
  intro j hj i hi
  exact h j _ (gateAt_get (C := ⟨gs, out⟩) hj) i hi

lemma pairInput_comm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp [pairInput, or_comm]

-- The statement, with the lost edges and their vertices named.
lemma main_aux {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (col : Fin n → Bool)
    (C : Circuit) (T L : Finset ℕ) (c : ℕ) (s : Fin n)
    (hcol : ∀ u v : Fin n, G.Adj u v → col u ≠ col v)
    (h4 : NoFourCycle G) (hAO2 : IsAO2 n C) (hRB : ReadsBack n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (hT : IsOrTree n C T L C.output)
    (hL : ∀ w ∈ L, n ≤ w ∧ (gateAt C (w - n)).op = GateOp.and)
    (hc : c < C.gates.length) (hcone : InOutputCone n C c)
    (hsing : singletonSet n C c = {s})
    (hpriv : ∀ k < C.gates.length, InCone n C c k → InOutputCone n C k →
      k ∈ T ∨ n + k ∈ L ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ w ∈ L, ∃ a ∈ (gateAt C (w - n)).inputs, OrReaches n C a k))
    (hpriv2 : ∀ j < C.gates.length, InCone n C j c → ∀ k < C.gates.length,
      n + j ∈ (gateAt C k).inputs → k = c ∨ InCone n C k c)
    (lost : Fin n → Fin n → Prop)
    (hlost : ∀ u v, lost u v ↔
      V (C.gates.map (rdg n c s)) (List.ofFn (pairInput u v)) C.output = false)
    (hleaf : ∀ u v : Fin n, G.Adj u v → lost u v →
      ∀ w ∈ L, gateVal n C (w - n) (pairInput u v) = true →
      ∀ a b : ℕ, ((gateAt C (w - n)).inputs = [a, b] ∨ (gateAt C (w - n)).inputs = [b, a]) →
        OrReaches n C a c →
          wireVal n C b (unitInput u) = true ∨ wireVal n C b (unitInput v) = true)
    (Y : Finset (Fin n)) (hY : ∀ y, y ∈ Y ↔ ∃ z, G.Adj z y ∧ lost z y) :
    Y.card ≤ (coneSet n C c).card ∧
    ∃ C' : Circuit, IsAO2 n C' ∧ ReadsBack n C' ∧ circuitFun n C' = graphFun G ∅ ∧
      C'.size + (coneSet n C c).card ≤ C.size + Y.card := by
  classical
  obtain ⟨hAO, _, h2⟩ := hAO2
  have hB := back_of hRB
  have hc1 : V C.gates (List.ofFn (unitInput s)) (n + c) = true := by
    have hmem : s ∈ singletonSet n C c := by rw [hsing]; simp
    have h : gateVal n C c (unitInput s) = true := by simpa [singletonSet] using hmem
    exact h
  have hc0 : ∀ z : Fin n, z ≠ s → V C.gates (List.ofFn (unitInput z)) (n + c) = false := by
    intro z hz
    have hmem : z ∉ singletonSet n C c := by rw [hsing]; simpa using hz
    have h : gateVal n C c (unitInput z) = false := by simpa [singletonSet] using hmem
    exact h
  have hC1 : ∀ x : Fin n → Bool, V C.gates (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun hfun x
  have hL1 : ∀ u v, G.Adj u v → lost u v →
      u ≠ s ∧ v ≠ s ∧ V C.gates (List.ofFn (pairInput u v)) (n + c) = true := by
    intro u v huv hl
    have h1 : V C.gates (List.ofFn (pairInput u v)) C.output = true := by
      rw [hC1]; exact (graphFun_pair G u v).mpr huv
    obtain ⟨hs0, hv⟩ := lost_c s hRB hAO hc1 (pairInput u v) h1 ((hlost u v).mp hl)
    refine ⟨?_, ?_, hv⟩
    · intro h
      simp [pairInput, h] at hs0
    · intro h
      simp [pairInput, h] at hs0
  have hsymm : ∀ u v, lost u v → lost v u := by
    intro u v h
    rw [hlost] at h ⊢
    rw [pairInput_comm v u]
    exact h
  have hAdj : ∀ u v, G.Adj u v → lost u v → G.Adj s u ∨ G.Adj s v := by
    intro u v huv hl
    exact lost_adj G s hRB hAO h2 hfun hT hL hc hc1 hpriv u v huv ((hlost u v).mp hl)
      (hleaf u v huv hl)
  refine ⟨?_, ?_⟩
  · apply concl_one s hRB hAO h2 hc hc1 hc0 Y
    intro y hy
    obtain ⟨z, hzy, hl⟩ := (hY y).mp hy
    obtain ⟨hz, hy', hv⟩ := hL1 z y hzy hl
    exact ⟨z, hz, hy', hv⟩
  · obtain ⟨hcT, hcL, hco⟩ := c_not_tree G s hRB hfun hT hc1
    have hout_lt : C.output < n + C.gates.length := by
      obtain ⟨_, h | ⟨h1, h2'⟩⟩ := hcone
      · omega
      · have := inCone_len h2'
        omega
    have hKlen : ∀ k ∈ coneSet n C c, k < (C.gates.map (rdg n c s)).length := by
      intro k hk
      rw [mem_coneSet] at hk
      rw [List.length_map]
      rcases hk with rfl | ⟨hk, _⟩
      · exact hc
      · exact hk
    have hKread : ∀ (i : ℕ) (g : Gate), (C.gates.map (rdg n c s))[i]? = some g →
        i ∉ coneSet n C c → ∀ u ∈ g.inputs, ∀ k ∈ coneSet n C c, u ≠ n + k := by
      intro i g' hg' hiK u' hu' k hk heq
      obtain ⟨g, hg, rfl⟩ := rd_inv C.gates i g' hg'
      simp only [rdg, List.mem_map] at hu'
      obtain ⟨u, hu, rfl⟩ := hu'
      have hi : i < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      have hgi : gateAt C i = g := gateAt_some hg
      by_cases huc : u = n + c
      · have e : rdw n c s u = s := by simp [rdw, huc]
        rw [e] at heq
        have := s.isLt
        omega
      · have e : rdw n c s u = u := by simp [rdw, huc]
        rw [e] at heq
        rw [mem_coneSet] at hk
        rcases hk with rfl | ⟨hkl, hkc⟩
        · exact huc heq
        · have hr := hpriv2 k hkl hkc i hi (by rw [hgi, ← heq]; exact hu)
          apply hiK
          rw [mem_coneSet]
          rcases hr with h | h
          · exact Or.inl h
          · exact Or.inr ⟨hi, h⟩
    have hKout : ∀ k ∈ coneSet n C c, C.output ≠ n + k := by
      intro k hk heq
      rw [mem_coneSet] at hk
      rcases hk with rfl | ⟨_, hkc⟩
      · exact hco heq
      · have hkc' := inCone_lt _ _ hkc
        obtain ⟨_, h | ⟨_, h⟩⟩ := hcone
        · omega
        · rw [heq, Nat.add_sub_cancel_left] at h
          have hck := inCone_lt _ _ h
          omega
    have hG0 : Good n (C.gates.map (rdg n c s)) := by
      refine ⟨rd_back s.isLt C.gates hB, ?_⟩
      intro g' hg'
      rw [List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      exact ⟨hAO g hg, by simpa [rdg] using h2 g hg⟩
    have hAO0 : AOp (C.gates.map (rdg n c s)) := fun g hg => (hG0.2 g hg).1
    obtain ⟨gs1, out1, hG1, hlen1, hout1, hval1⟩ :=
      prune n (coneSet n C c) _ C.output hG0 hKlen hKread hKout
    rw [List.length_map] at hlen1 hout1
    have hZne : ∀ y ∈ Y.filter (fun y => G.Adj s y),
        (Finset.univ.filter (fun z => G.Adj z y ∧ lost z y)).Nonempty := by
      intro y hy
      obtain ⟨z, hz⟩ := (hY y).mp (Finset.mem_filter.mp hy).1
      exact ⟨z, by simp [hz]⟩
    obtain ⟨gs2, out2, hG2, hlen2, hout2, hval2⟩ :=
      stars_add (fun y => Finset.univ.filter (fun z => G.Adj z y ∧ lost z y))
        (Y.filter (fun y => G.Adj s y)) hZne gs1 out1 hG1 (hout1 hout_lt)
    refine ⟨⟨gs2, out2⟩, ⟨fun g hg => (hG2.2 g hg).1, readsBack_of out2 hG2.1,
      fun g hg => (hG2.2 g hg).2⟩, readsBack_of out2 hG2.1, ?_, ?_⟩
    · funext x
      have hval : (V gs2 (List.ofFn x) out2 = true ↔ graphFun G ∅ x = true) := by
        rw [hval2 x, hval1 (List.ofFn x) (by simp), graphFun_true]
        constructor
        · rintro (h | ⟨y, hy, hxy, z, hz, hxz⟩)
          · have h' := rd_le_fn s hRB hAO hc1 x _ h
            rw [hC1, graphFun_true] at h'
            exact h'
          · have hz' := (Finset.mem_filter.mp hz).2
            exact ⟨z, y, hz'.1, hxz, hxy⟩
        · rintro ⟨u, v, huv, hxu, hxv⟩
          by_cases hl : lost u v
          · right
            have hlv : lost v u := hsymm u v hl
            rcases hAdj u v huv hl with h | h
            · exact ⟨u, Finset.mem_filter.mpr ⟨(hY u).mpr ⟨v, huv.symm, hlv⟩, h⟩, hxu, v,
                by simp [huv.symm, hlv], hxv⟩
            · exact ⟨v, Finset.mem_filter.mpr ⟨(hY v).mpr ⟨u, huv, hl⟩, h⟩, hxv, u,
                by simp [huv, hl], hxu⟩
          · left
            have h0 : V (C.gates.map (rdg n c s)) (List.ofFn (pairInput u v)) C.output = true := by
              have hne := (hlost u v).not.mp hl
              simpa using hne
            refine V_ofFn_mono _ hG0.1 hAO0 (pairInput u v) x ?_ _ h0
            intro i hi
            rw [pairInput_true] at hi
            rcases hi with h | h <;> rw [h] <;> assumption
      show V gs2 (List.ofFn x) out2 = graphFun G ∅ x
      exact Bool.eq_iff_iff.mpr hval
    · have hdisjZ : ∀ y ∈ Y.filter (fun y => G.Adj s y), ∀ y' ∈ Y.filter (fun y => G.Adj s y),
          y ≠ y' → Disjoint (Finset.univ.filter (fun z => G.Adj z y ∧ lost z y))
            (Finset.univ.filter (fun z => G.Adj z y' ∧ lost z y')) := by
        intro y hy y' hy' hne
        rw [Finset.disjoint_left]
        intro z hz hz'
        obtain ⟨hzy, hl⟩ := (Finset.mem_filter.mp hz).2
        obtain ⟨hzy', hl'⟩ := (Finset.mem_filter.mp hz').2
        have hsy := (Finset.mem_filter.mp hy).2
        have hsy' := (Finset.mem_filter.mp hy').2
        have hzs : z ≠ s := (hL1 z y hzy hl).1
        exact hne (Finset.card_le_one.mp (h4 s z (Ne.symm hzs)) y (by simp [hsy, hzy]) y'
          (by simp [hsy', hzy']))
      have hZsub : (Y.filter (fun y => G.Adj s y)).biUnion
          (fun y => Finset.univ.filter (fun z => G.Adj z y ∧ lost z y)) ∪
            Y.filter (fun y => G.Adj s y) ⊆ Y := by
        intro w hw
        rw [Finset.mem_union, Finset.mem_biUnion] at hw
        rcases hw with ⟨y, hy, hz⟩ | hw
        · obtain ⟨hzy, hl⟩ := (Finset.mem_filter.mp hz).2
          exact (hY w).mpr ⟨y, hzy.symm, hsymm w y hl⟩
        · exact (Finset.mem_filter.mp hw).1
      have hdisj2 : Disjoint ((Y.filter (fun y => G.Adj s y)).biUnion
          (fun y => Finset.univ.filter (fun z => G.Adj z y ∧ lost z y)))
            (Y.filter (fun y => G.Adj s y)) := by
        rw [Finset.disjoint_left]
        intro w hw hwY
        rw [Finset.mem_biUnion] at hw
        obtain ⟨y, hy, hz⟩ := hw
        obtain ⟨hzy, _⟩ := (Finset.mem_filter.mp hz).2
        have hsy := (Finset.mem_filter.mp hy).2
        have hsw := (Finset.mem_filter.mp hwY).2
        have e1 := hcol s y hsy
        have e2 := hcol s w hsw
        have e3 := hcol w y hzy
        revert e1 e2 e3
        cases col s <;> cases col y <;> cases col w <;> simp
      have hsum : ∑ y ∈ Y.filter (fun y => G.Adj s y),
          ((Finset.univ.filter (fun z => G.Adj z y ∧ lost z y)).card + 1) ≤ Y.card := by
        rw [Finset.sum_add_distrib, ← Finset.card_biUnion hdisjZ]
        simp only [Finset.sum_const, smul_eq_mul, mul_one]
        rw [← Finset.card_union_of_disjoint hdisj2]
        exact Finset.card_le_card hZsub
      show gs2.length + (coneSet n C c).card ≤ C.gates.length + Y.card
      omega

-- The posted statement.
lemma main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (col : Fin n → Bool) (C C0 : PEqualNP.CircuitLowerBounds.Circuit) (T L : Finset ℕ) (c : ℕ) (s : Fin n),
  (∀ u v : Fin n, G.Adj u v → col u ≠ col v) →
  PEqualNP.TopForm.NoFourCycle G →
  PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  PEqualNP.MetaComplexity.NestedCover.IsOrTree n C T L C.output →
  (∀ w ∈ L, n ≤ w ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
  c < C.gates.length → PEqualNP.Core.InOutputCone n C c →
  PEqualNP.SplitCount.singletonSet n C c = {s} →
  (∀ k < C.gates.length, n + c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  (∀ k < C.gates.length, PEqualNP.EdgeOwnership.InCone n C c k → PEqualNP.Core.InOutputCone n C k →
    k ∈ T ∨ n + k ∈ L ∨ ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      ∃ w ∈ L, ∃ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs, PEqualNP.CleanedNonEdge.OrReaches n C a k)) →
  (∀ j < C.gates.length, PEqualNP.EdgeOwnership.InCone n C j c → ∀ k < C.gates.length,
    n + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k = c ∨ PEqualNP.EdgeOwnership.InCone n C k c) →
  C0 = ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun ww => if ww = n + c then (s : ℕ) else ww) } : PEqualNP.CircuitLowerBounds.Gate)), output := C.output } : PEqualNP.CircuitLowerBounds.Circuit) →
  (∀ u v : Fin n, G.Adj u v → PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput u v) = false →
    ∀ w ∈ L, PEqualNP.EdgeOwnership.gateVal n C (w - n) (PEqualNP.EdgeOwnership.pairInput u v) = true →
      ∀ a b : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs = [a, b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs = [b, a]) →
        PEqualNP.CleanedNonEdge.OrReaches n C a c →
          PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.SplitCount.unitInput u) = true ∨ PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.SplitCount.unitInput v) = true) →
  (Finset.univ.filter fun y : Fin n => ∃ z : Fin n, G.Adj z y ∧ PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput z y) = false).card ≤ (PEqualNP.Core.coneSet n C c).card ∧
  ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C' ∧
    PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
    C'.size + (PEqualNP.Core.coneSet n C c).card ≤ C.size + (Finset.univ.filter fun y2 : Fin n => ∃ z2 : Fin n, G.Adj z2 y2 ∧ PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput z2 y2) = false).card := by
  intro n G _ col C C0 T L c s hcol h4 hAO2 hRB hfun hT hL hc hcone hsing hread hpriv hpriv2 hC0 hleaf
  subst hC0
  exact main_aux G col C T L c s hcol h4 hAO2 hRB hfun hT hL hc hcone hsing hpriv hpriv2
    (fun u v => circuitFun n ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun ww => if ww = n + c then (s : ℕ) else ww) } : PEqualNP.CircuitLowerBounds.Gate)), output := C.output } : PEqualNP.CircuitLowerBounds.Circuit) (pairInput u v) = false)
    (fun u v => Iff.rfl) hleaf _ (fun y => by simp)

end PEqualNP.Outside.L_meta_3017

theorem PEqualNP.Outside.L_meta_3017 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (col : Fin n → Bool) (C C0 : PEqualNP.CircuitLowerBounds.Circuit) (T L : Finset ℕ) (c : ℕ) (s : Fin n),
  (∀ u v : Fin n, G.Adj u v → col u ≠ col v) →
  PEqualNP.TopForm.NoFourCycle G →
  PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  PEqualNP.MetaComplexity.NestedCover.IsOrTree n C T L C.output →
  (∀ w ∈ L, n ≤ w ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
  c < C.gates.length → PEqualNP.Core.InOutputCone n C c →
  PEqualNP.SplitCount.singletonSet n C c = {s} →
  (∀ k < C.gates.length, n + c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  (∀ k < C.gates.length, PEqualNP.EdgeOwnership.InCone n C c k → PEqualNP.Core.InOutputCone n C k →
    k ∈ T ∨ n + k ∈ L ∨ ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      ∃ w ∈ L, ∃ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs, PEqualNP.CleanedNonEdge.OrReaches n C a k)) →
  (∀ j < C.gates.length, PEqualNP.EdgeOwnership.InCone n C j c → ∀ k < C.gates.length,
    n + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k = c ∨ PEqualNP.EdgeOwnership.InCone n C k c) →
  C0 = ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun ww => if ww = n + c then (s : ℕ) else ww) } : PEqualNP.CircuitLowerBounds.Gate)), output := C.output } : PEqualNP.CircuitLowerBounds.Circuit) →
  (∀ u v : Fin n, G.Adj u v → PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput u v) = false →
    ∀ w ∈ L, PEqualNP.EdgeOwnership.gateVal n C (w - n) (PEqualNP.EdgeOwnership.pairInput u v) = true →
      ∀ a b : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs = [a, b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs = [b, a]) →
        PEqualNP.CleanedNonEdge.OrReaches n C a c →
          PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.SplitCount.unitInput u) = true ∨ PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.SplitCount.unitInput v) = true) →
  (Finset.univ.filter fun y : Fin n => ∃ z : Fin n, G.Adj z y ∧ PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput z y) = false).card ≤ (PEqualNP.Core.coneSet n C c).card ∧
  ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C' ∧
    PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
    C'.size + (PEqualNP.Core.coneSet n C c).card ≤ C.size + (Finset.univ.filter fun y2 : Fin n => ∃ z2 : Fin n, G.Adj z2 y2 ∧ PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput z2 y2) = false).card :=
  PEqualNP.Outside.L_meta_3017.main
