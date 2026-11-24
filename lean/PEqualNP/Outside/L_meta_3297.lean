import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3297

open PEqualNP.CircuitLowerBounds

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def V (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gates.foldl stp (List.ofFn x)).getD i false

lemma getD_lt (w : List Bool) (v : Bool) (i : ℕ) (h : i < w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  first
    | exact List.getD_append _ _ _ _ h
    | simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_last (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  first
    | exact List.getD_eq_default _ _ h
    | simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma len_fold (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stp w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp only [stp, List.length_append, List.length_cons, List.length_nil]
    omega

lemma pre_fold (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (gs.foldl stp w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have h1 : i < (stp w g).length := by
      simp only [stp, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.foldl_cons, ih (stp w g) i h1]
    exact getD_lt w _ i hi

lemma gate_fold (gs : List Gate) :
    ∀ (w : List Bool) (k : ℕ) (hk : k < gs.length),
      (gs.foldl stp w).getD (w.length + k) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i => ((gs.take k).foldl stp w).getD i false) := by
  induction gs with
  | nil => intro w k hk; simp at hk
  | cons g gs ih =>
    intro w k hk
    cases k with
    | zero =>
      have h1 : w.length < (stp w g).length := by
        simp only [stp, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, Nat.add_zero, pre_fold gs (stp w g) w.length h1]
      simp only [stp, List.take_zero, List.foldl_nil, List.getElem_cons_zero]
      exact getD_last w _
    | succ k =>
      have hk' : k < gs.length := by
        simp only [List.length_cons] at hk
        omega
      have h := ih (stp w g) k hk'
      have hl : (stp w g).length + k = w.length + (k + 1) := by
        simp only [stp, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hl] at h
      simpa only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ] using h

lemma V_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    V gates x i = x ⟨i, hi⟩ := by
  unfold V
  rw [pre_fold gates (List.ofFn x) i (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma V_ge (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : n + gates.length ≤ i) :
    V gates x i = false := by
  unfold V
  apply getD_big
  rw [len_fold, List.length_ofFn]
  exact hi

lemma V_gate (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length) :
    V gates x (n + k) =
      (gates[k]).op.eval ((gates[k]).inputs.map fun i => if i < n + k then V gates x i else false) := by
  unfold V
  have h := gate_fold gates (List.ofFn x) k hk
  rw [List.length_ofFn] at h
  rw [h]
  have hlen : ((gates.take k).foldl stp (List.ofFn x)).length = n + k := by
    rw [len_fold, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hsplit : gates.foldl stp (List.ofFn x) =
      (gates.drop k).foldl stp ((gates.take k).foldl stp (List.ofFn x)) := by
    rw [← List.foldl_append, List.take_append_drop]
  have hmap : ((gates[k]).inputs.map fun i => ((gates.take k).foldl stp (List.ofFn x)).getD i false) =
      (gates[k]).inputs.map fun i =>
        if i < n + k then (gates.foldl stp (List.ofFn x)).getD i false else false := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < n + k
    · rw [if_pos hi, hsplit,
        pre_fold (gates.drop k) ((gates.take k).foldl stp (List.ofFn x)) i (by rw [hlen]; exact hi)]
    · rw [if_neg hi]
      exact getD_big _ i (by rw [hlen]; omega)
  rw [hmap]

lemma and_map {α : Type} (l : List α) (f : α → Bool) :
    GateOp.eval GateOp.and (l.map f) = true ↔ ∀ a ∈ l, f a = true := by
  simp [GateOp.eval]

lemma or_map {α : Type} (l : List α) (f : α → Bool) :
    GateOp.eval GateOp.or (l.map f) = true ↔ ∃ a ∈ l, f a = true := by
  simp [GateOp.eval]


lemma eval_and2 (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by simp [GateOp.eval]
lemma eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by simp [GateOp.eval]
lemma eval_and1 (a : Bool) : GateOp.eval GateOp.and [a] = a := by simp [GateOp.eval]
lemma eval_or1 (a : Bool) : GateOp.eval GateOp.or [a] = a := by simp [GateOp.eval]
lemma eval_and0 : GateOp.eval GateOp.and [] = true := by simp [GateOp.eval]
lemma eval_or0 : GateOp.eval GateOp.or [] = false := by simp [GateOp.eval]

-- the wire list, the output and the function of a circuit in terms of V (all by unfolding)
lemma wires_V (C : Circuit) {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = V C.gates x i := rfl

lemma eval_V (C : Circuit) {n : ℕ} (x : Fin n → Bool) :
    C.eval (List.ofFn x) = V C.gates x C.output := rfl

lemma fun_V (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n C x = V C.gates x C.output := rfl

lemma V_gate_some (G : List Gate) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (h : G[j]? = some g) :
    V G x (n + j) = g.op.eval (g.inputs.map fun i => if i < n + j then V G x i else false) := by
  obtain ⟨hj, hg⟩ := List.getElem?_eq_some_iff.mp h
  rw [V_gate G x j hj, hg]

-- two gate lists that agree below gate k have the same wires below n + k
lemma V_prefix (G H : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ)
    (h : ∀ j, j < k → H[j]? = G[j]?) : ∀ i, i < n + k → V H x i = V G x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hik
    by_cases hi : i < n
    · rw [V_input H x i hi, V_input G x i hi]
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hjk : j < k := by omega
      have hjj := h j hjk
      cases hG : G[j]? with
      | none =>
        rw [hG] at hjj
        have h1 : G.length ≤ j := List.getElem?_eq_none_iff.mp hG
        have h2 : H.length ≤ j := List.getElem?_eq_none_iff.mp hjj
        rw [V_ge H x _ (by omega), V_ge G x _ (by omega)]
      | some g =>
        rw [hG] at hjj
        rw [V_gate_some H x j g hjj, V_gate_some G x j g hG]
        congr 1
        apply List.map_congr_left
        intro t _
        by_cases ht : t < n + j
        · rw [if_pos ht, if_pos ht]
          exact ih t ht (by omega)
        · rw [if_neg ht, if_neg ht]

-- if every gate of H, read on the wires of G, gives the wire of G, the two lists have the same wires
lemma V_congr (G H : List Gate) {n : ℕ} (x : Fin n → Bool) (hlen : H.length = G.length)
    (h : ∀ (j : ℕ) (hj : j < H.length),
      (H[j]).op.eval ((H[j]).inputs.map fun i => if i < n + j then V G x i else false) =
        V G x (n + j)) :
    ∀ i : ℕ, V H x i = V G x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < n
    · rw [V_input H x i hi, V_input G x i hi]
    · by_cases hi2 : i < n + H.length
      · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
        have hj : j < H.length := by omega
        rw [V_gate H x j hj, ← h j hj]
        congr 1
        apply List.map_congr_left
        intro t _
        by_cases ht : t < n + j
        · rw [if_pos ht, if_pos ht]
          exact ih t ht
        · rw [if_neg ht, if_neg ht]
      · rw [V_ge H x i (by omega), V_ge G x i (by omega)]

-- overwriting gate j leaves the wires below n + j as they were
lemma V_set_lt (G : List Gate) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (g' : Gate) :
    ∀ i, i < n + j → V (G.set j g') x i = V G x i := by
  apply V_prefix
  intro k hk
  have hne : j ≠ k := by omega
  first
    | rw [List.getElem?_set_ne hne]
    | simp [List.getElem?_set, hne]

-- overwriting gate j by a gate with the same value at x changes no wire at x
lemma V_set (G : List Gate) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (g' : Gate)
    (h : j < G.length →
      g'.op.eval (g'.inputs.map fun i => if i < n + j then V G x i else false) = V G x (n + j)) :
    ∀ i : ℕ, V (G.set j g') x i = V G x i := by
  apply V_congr G (G.set j g') x (by simp)
  intro k hk
  have hk' : k < G.length := by simpa using hk
  by_cases hkj : j = k
  · subst hkj
    rw [List.getElem_set_self]
    exact h hk'
  · rw [List.getElem_set_ne hkj]
    exact (V_gate G x k hk').symm

-- two overwrites of the same gate with the same value at x give the same wires at x
lemma V_set_set (L : List Gate) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (g1 g2 : Gate)
    (h : j < L.length →
      g2.op.eval (g2.inputs.map fun i => if i < n + j then V (L.set j g1) x i else false) =
        g1.op.eval (g1.inputs.map fun i => if i < n + j then V (L.set j g1) x i else false)) :
    ∀ i : ℕ, V (L.set j g2) x i = V (L.set j g1) x i := by
  apply V_congr (L.set j g1) (L.set j g2) x (by simp)
  intro k hk
  have hk' : k < L.length := by simpa using hk
  have hk1 : k < (L.set j g1).length := by simpa using hk'
  have e := V_gate (L.set j g1) x k hk1
  by_cases hkj : j = k
  · subst hkj
    rw [List.getElem_set_self] at e
    rw [List.getElem_set_self]
    exact (h hk').trans e.symm
  · rw [List.getElem_set_ne hkj] at e
    rw [List.getElem_set_ne hkj]
    exact e.symm

-- the same groundwork for an arbitrary starting wire list w (V is the case w = List.ofFn x)
def W (G : List Gate) (w : List Bool) (i : ℕ) : Bool := (G.foldl stp w).getD i false

lemma V_eq_W (G : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) : V G x i = W G (List.ofFn x) i := rfl

lemma wires_W (C : Circuit) (w : List Bool) (i : ℕ) : (C.wires w).getD i false = W C.gates w i := rfl

lemma eval_W (C : Circuit) (w : List Bool) : C.eval w = W C.gates w C.output := rfl

lemma W_input (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    W G w i = w.getD i false := pre_fold G w i hi

lemma W_ge (G : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + G.length ≤ i) :
    W G w i = false := by
  unfold W
  apply getD_big
  rw [len_fold]
  exact hi

lemma W_gate (G : List Gate) (w : List Bool) (k : ℕ) (hk : k < G.length) :
    W G w (w.length + k) =
      (G[k]).op.eval ((G[k]).inputs.map fun i => if i < w.length + k then W G w i else false) := by
  unfold W
  rw [gate_fold G w k hk]
  have hlen : ((G.take k).foldl stp w).length = w.length + k := by
    rw [len_fold, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hsplit : G.foldl stp w = (G.drop k).foldl stp ((G.take k).foldl stp w) := by
    rw [← List.foldl_append, List.take_append_drop]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w.length + k
  · rw [if_pos hi, hsplit,
      pre_fold (G.drop k) ((G.take k).foldl stp w) i (by rw [hlen]; exact hi)]
  · rw [if_neg hi]
    exact getD_big _ i (by rw [hlen]; omega)

lemma W_gate_some (G : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (h : G[j]? = some g) :
    W G w (w.length + j) =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then W G w i else false) := by
  obtain ⟨hj, hg⟩ := List.getElem?_eq_some_iff.mp h
  rw [W_gate G w j hj, hg]

-- same starting list: if every gate of H, read on the wires of G, gives the wire of G, all wires agree
lemma W_congr (G H : List Gate) (w : List Bool) (hlen : H.length = G.length)
    (h : ∀ (j : ℕ) (hj : j < H.length),
      (H[j]).op.eval ((H[j]).inputs.map fun i => if i < w.length + j then W G w i else false) =
        W G w (w.length + j)) :
    ∀ i : ℕ, W H w i = W G w i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < w.length
    · rw [W_input H w i hi, W_input G w i hi]
    · by_cases hi2 : i < w.length + H.length
      · obtain ⟨j, rfl⟩ : ∃ j, i = w.length + j := ⟨i - w.length, by omega⟩
        have hj : j < H.length := by omega
        rw [W_gate H w j hj, ← h j hj]
        congr 1
        apply List.map_congr_left
        intro t _
        by_cases ht : t < w.length + j
        · rw [if_pos ht, if_pos ht]
          exact ih t ht
        · rw [if_neg ht, if_neg ht]
      · rw [W_ge H w i (by omega), W_ge G w i (by omega)]

-- same gates, two starting lists of the same length: wires agree wherever every wire read agrees
lemma W_two (G : List Gate) (w w' : List Bool) (hl : w'.length = w.length) (m : ℕ)
    (h0 : ∀ i, i < w.length → i < m → w'.getD i false = w.getD i false)
    (hread : ∀ (j : ℕ) (hj : j < G.length), w.length + j < m → ∀ i ∈ (G[j]).inputs, i < m) :
    ∀ i : ℕ, i < m → W G w' i = W G w i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro him
    by_cases hi : i < w.length
    · rw [W_input G w' i (by omega), W_input G w i hi]
      exact h0 i hi him
    · by_cases hi2 : i < w.length + G.length
      · obtain ⟨j, rfl⟩ : ∃ j, i = w.length + j := ⟨i - w.length, by omega⟩
        have hj : j < G.length := by omega
        have e1 := W_gate G w' j hj
        rw [hl] at e1
        rw [e1, W_gate G w j hj]
        congr 1
        apply List.map_congr_left
        intro t ht
        by_cases htj : t < w.length + j
        · rw [if_pos htj, if_pos htj]
          exact ih t htj (hread j hj him t ht)
        · rw [if_neg htj, if_neg htj]
      · rw [W_ge G w' i (by omega), W_ge G w i (by omega)]

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.TopForm PEqualNP.FactorSubst

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


lemma gateAt_get (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hk]

lemma sub_len (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n c sigma).gates.length = C.gates.length := by
  simp [substReads]

lemma sub_get (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) (k : ℕ) (hk : k < C.gates.length)
    (hk' : k < (substReads C n c sigma).gates.length) :
    (substReads C n c sigma).gates[k] =
      ⟨(C.gates[k]).op, (C.gates[k]).inputs.map fun i => if i = n + c then sigma k else i⟩ := by
  simp [substReads]

-- a gate in the OR closure of wire i has its wire at or below i
lemma orReaches_ge (n : ℕ) (C : Circuit) (g : ℕ) : ∀ i, OrReaches n C i g → n + g ≤ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    have hn : n ≤ i := h.1
    obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    rcases (orReaches_iff n C k g).mp h with ⟨_, h1 | ⟨_, j, _, hj, hjr⟩⟩
    · omega
    · have := ih j hj hjr
      omega

-- values flow up an OR closure
lemma orReaches_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ) :
    ∀ i, OrReaches n C i g → V C.gates x (n + g) = true → V C.gates x i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h hv
    have hn : n ≤ i := h.1
    obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    rcases (orReaches_iff n C k g).mp h with ⟨hk, h1 | ⟨hop, j, hjm, hj, hjr⟩⟩
    · rw [h1] at hv
      exact hv
    · have hvj := ih j hj hjr hv
      rw [V_gate C.gates x k hk, ← gateAt_get C k hk, hop, or_map]
      exact ⟨j, hjm, by rw [if_pos hj]; exact hvj⟩

-- the value part: outside the OR closure nothing changes; inside it values only grow, and a new
-- true value comes from the chosen factor of a reader below
lemma sem (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hA : IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (H1 : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b)
    (H2 : ∀ g ∈ frontier n C c, (gateAt C g).op = GateOp.and → ∀ u y : ℕ,
      ((gateAt C g).inputs = [u, y] ∨ (gateAt C g).inputs = [y, u]) →
      (∃ w ∈ insert c (orClosure n C c), u = n + w) →
      (∀ w' ∈ insert c (orClosure n C c), y ≠ n + w') ∧
      ∀ r ∈ readers n C c, (r = g ∨ OrReaches n C u r) →
        (sigma r = b → ∀ x : Fin n → Bool, wireVal n C y x = true → wireVal n C a x = true) ∧
        (sigma r = a → ∀ x' : Fin n → Bool, wireVal n C y x' = true → wireVal n C b x' = true))
    (z : Fin n → Bool) :
    ∀ i : ℕ,
      ((¬ ∃ k ∈ orClosure n C c, i = n + k) →
        V (substReads C n c sigma).gates z i = V C.gates z i) ∧
      ((∃ k ∈ orClosure n C c, i = n + k) →
        (V C.gates z i = true → V (substReads C n c sigma).gates z i = true) ∧
        (V (substReads C n c sigma).gates z i = true → V C.gates z i = true ∨
          ∃ r ∈ readers n C c, OrReaches n C i r ∧ V C.gates z (sigma r) = true)) := by
  obtain ⟨hao, hrb, hlen2⟩ := hA
  have hab : a < n + c ∧ b < n + c := by
    have h := hrb c hc
    rw [hcin] at h
    exact ⟨h a (by simp), h b (by simp)⟩
  have hOgt : ∀ k ∈ orClosure n C c, c < k ∧ k < C.gates.length ∧ OrReaches n C (n + k) c := by
    intro k hk
    simp only [orClosure, Finset.mem_filter, Finset.mem_range] at hk
    have := orReaches_ge n C c (n + k) hk.2.2
    exact ⟨by omega, hk.1, hk.2.2⟩
  have hVc : V C.gates z (n + c) = (V C.gates z a && V C.gates z b) := by
    rw [V_gate C.gates z c hc, ← gateAt_get C c hc, hcop, hcin]
    simp only [List.map_cons, List.map_nil, if_pos hab.1, if_pos hab.2, eval_and2]
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hin : i < n
    · refine ⟨fun _ => ?_, ?_⟩
      · rw [V_input _ z i hin, V_input _ z i hin]
      · rintro ⟨k, _, hik⟩
        omega
    · by_cases hilen : i < n + C.gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < C.gates.length := by omega
        have hk' : k < (substReads C n c sigma).gates.length := by rw [sub_len]; exact hk
        have hl2 : (gateAt C k).inputs.length = 2 := by
          rw [gateAt_get C k hk]
          exact hlen2 _ (List.getElem_mem hk)
        obtain ⟨i1, i2, hi12⟩ := List.length_eq_two.mp hl2
        have hm1 : i1 ∈ (gateAt C k).inputs := by rw [hi12]; simp
        have hm2 : i2 ∈ (gateAt C k).inputs := by rw [hi12]; simp
        have hr1 : i1 < n + k := hrb k hk i1 hm1
        have hr2 : i2 < n + k := hrb k hk i2 hm2
        have hopk : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
          rw [gateAt_get C k hk]
          exact hao _ (List.getElem_mem hk)
        have hV : V C.gates z (n + k) =
            (gateAt C k).op.eval [V C.gates z i1, V C.gates z i2] := by
          rw [V_gate C.gates z k hk, ← gateAt_get C k hk, hi12]
          simp only [List.map_cons, List.map_nil, if_pos hr1, if_pos hr2]
        -- what a read of wire t becomes
        have rd : ∀ t, t ∈ (gateAt C k).inputs → t < n + k →
            (if (if t = n + c then sigma k else t) < n + k then
              V (substReads C n c sigma).gates z (if t = n + c then sigma k else t) else false) =
            (if t = n + c then V C.gates z (sigma k)
              else V (substReads C n c sigma).gates z t) := by
          intro t htm ht
          by_cases htc : t = n + c
          · have hkr : k ∈ readers n C c := by
              simp only [readers, Finset.mem_filter, Finset.mem_range]
              exact ⟨hk, htc ▸ htm⟩
            have hs := H1 k hkr
            have hslt : sigma k < n + k := by
              rcases hs with h | h <;> omega
            rw [if_pos htc, if_pos htc, if_pos hslt]
            have hno : ¬ ∃ k2 ∈ orClosure n C c, sigma k = n + k2 := by
              rintro ⟨k2, hk2, e⟩
              have := (hOgt k2 hk2).1
              rcases hs with h | h <;> omega
            exact (ih (sigma k) hslt).1 hno
          · rw [if_neg htc, if_neg htc, if_pos ht]
        have hV' : V (substReads C n c sigma).gates z (n + k) =
            (gateAt C k).op.eval
              [(if i1 = n + c then V C.gates z (sigma k)
                  else V (substReads C n c sigma).gates z i1),
               (if i2 = n + c then V C.gates z (sigma k)
                  else V (substReads C n c sigma).gates z i2)] := by
          rw [V_gate _ z k hk', sub_get C n c sigma k hk hk', ← gateAt_get C k hk, hi12]
          simp only [List.map_cons, List.map_nil]
          rw [rd i1 hm1 hr1, rd i2 hm2 hr2]
        have lo : ∀ t, t ∈ (gateAt C k).inputs → t < n + k → V C.gates z t = true →
            (if t = n + c then V C.gates z (sigma k)
              else V (substReads C n c sigma).gates z t) = true := by
          intro t htm ht hv
          by_cases htc : t = n + c
          · rw [if_pos htc]
            have hkr : k ∈ readers n C c := by
              simp only [readers, Finset.mem_filter, Finset.mem_range]
              exact ⟨hk, htc ▸ htm⟩
            rw [htc, hVc] at hv
            have hv2 : V C.gates z a = true ∧ V C.gates z b = true := by simpa using hv
            rcases H1 k hkr with hs | hs
            · rw [hs]; exact hv2.1
            · rw [hs]; exact hv2.2
          · rw [if_neg htc]
            by_cases hto : ∃ k2 ∈ orClosure n C c, t = n + k2
            · exact ((ih t ht).2 hto).1 hv
            · rw [(ih t ht).1 hto]; exact hv
        have up : ∀ t, t ∈ (gateAt C k).inputs → t < n + k →
            (if t = n + c then V C.gates z (sigma k)
              else V (substReads C n c sigma).gates z t) = true →
            V C.gates z t = true ∨
              ((∃ w ∈ insert c (orClosure n C c), t = n + w) ∧
                ∃ r ∈ readers n C c, (r = k ∨ OrReaches n C t r) ∧
                  V C.gates z (sigma r) = true) := by
          intro t htm ht hv
          by_cases htc : t = n + c
          · rw [if_pos htc] at hv
            have hkr : k ∈ readers n C c := by
              simp only [readers, Finset.mem_filter, Finset.mem_range]
              exact ⟨hk, htc ▸ htm⟩
            exact Or.inr ⟨⟨c, Finset.mem_insert_self _ _, htc⟩, k, hkr, Or.inl rfl, hv⟩
          · rw [if_neg htc] at hv
            by_cases hto : ∃ k2 ∈ orClosure n C c, t = n + k2
            · rcases ((ih t ht).2 hto).2 hv with h | ⟨r, hr, hreach, hrv⟩
              · exact Or.inl h
              · obtain ⟨k2, hk2, e⟩ := hto
                exact Or.inr ⟨⟨k2, Finset.mem_insert_of_mem hk2, e⟩, r, hr, Or.inr hreach, hrv⟩
            · rw [(ih t ht).1 hto] at hv
              exact Or.inl hv
        -- a wire of c or of the closure read by gate k puts k at or above c
        have habove : ∀ t, t ∈ (gateAt C k).inputs →
            (∃ w ∈ insert c (orClosure n C c), t = n + w) → k ≠ c := by
          rintro t htm ⟨w, hw, e⟩ rfl
          have htlt : t < n + k := hrb k hk t htm
          rcases Finset.mem_insert.mp hw with h | h
          · omega
          · have := (hOgt w h).1
            omega
        by_cases hkO : k ∈ orClosure n C c
        · have hor : (gateAt C k).op = GateOp.or := by
            have h3 := hOgt k hkO
            rcases (orReaches_iff n C k c).mp h3.2.2 with ⟨_, h | ⟨hop, _⟩⟩
            · omega
            · exact hop
          have hfin : ∀ t, t ∈ (gateAt C k).inputs → t < n + k → V C.gates z t = true →
              V C.gates z (n + k) = true := by
            intro t htm ht h
            rw [V_gate C.gates z k hk, ← gateAt_get C k hk, hor, or_map]
            exact ⟨t, htm, by rw [if_pos ht]; exact h⟩
          refine ⟨fun hno => absurd ⟨k, hkO, rfl⟩ hno, fun _ => ⟨?_, ?_⟩⟩
          · intro hv
            rw [hV, hor, eval_or2, Bool.or_eq_true] at hv
            rw [hV', hor, eval_or2, Bool.or_eq_true]
            rcases hv with h | h
            · exact Or.inl (lo i1 hm1 hr1 h)
            · exact Or.inr (lo i2 hm2 hr2 h)
          · intro hv
            rw [hV', hor, eval_or2, Bool.or_eq_true] at hv
            have step : ∀ t, t ∈ (gateAt C k).inputs → t < n + k →
                (if t = n + c then V C.gates z (sigma k)
                  else V (substReads C n c sigma).gates z t) = true →
                V C.gates z (n + k) = true ∨
                  ∃ r ∈ readers n C c, OrReaches n C (n + k) r ∧
                    V C.gates z (sigma r) = true := by
              intro t htm ht h
              rcases up t htm ht h with h1 | ⟨_, r, hr, hrr, hrv⟩
              · exact Or.inl (hfin t htm ht h1)
              · refine Or.inr ⟨r, hr, ?_, hrv⟩
                rcases hrr with hrk | hrr
                · rw [hrk]
                  exact (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩
                · exact (orReaches_iff n C k r).mpr ⟨hk, Or.inr ⟨hor, t, htm, ht, hrr⟩⟩
            rcases hv with h | h
            · exact step i1 hm1 hr1 h
            · exact step i2 hm2 hr2 h
        · refine ⟨fun _ => ?_, ?_⟩
          swap
          · rintro ⟨k2, hk2, e⟩
            have hkk : k2 = k := by omega
            rw [hkk] at hk2
            exact absurd hk2 hkO
          rw [hV, hV']
          apply Bool.eq_iff_iff.mpr
          rcases hopk with hand | hor
          · -- an AND gate: a new true value of a closure wire is paid for by the other operand
            have bad : ∀ u y, ((gateAt C k).inputs = [u, y] ∨ (gateAt C k).inputs = [y, u]) →
                y < n + k →
                (∃ w ∈ insert c (orClosure n C c), u = n + w) →
                (∃ r ∈ readers n C c, (r = k ∨ OrReaches n C u r) ∧
                  V C.gates z (sigma r) = true) →
                (if y = n + c then V C.gates z (sigma k)
                  else V (substReads C n c sigma).gates z y) = true →
                V C.gates z u = true := by
              rintro u y hin hy ⟨w, hw, huw⟩ ⟨r, hrm, hrr, hrv⟩ hny
              have hum : u ∈ (gateAt C k).inputs := by
                rcases hin with h | h <;> rw [h] <;> simp
              have hkc : k ≠ c := habove u hum ⟨w, hw, huw⟩
              have hfr : k ∈ frontier n C c := by
                simp only [PEqualNP.FactorSubst.frontier, Finset.mem_filter, Finset.mem_range]
                exact ⟨hk, hkc, hkO, w, hw, huw ▸ hum⟩
              obtain ⟨hy', hr'⟩ := H2 k hfr hand u y hin ⟨w, hw, huw⟩
              have hyc : y ≠ n + c := hy' c (Finset.mem_insert_self _ _)
              have hyo : ¬ ∃ k2 ∈ orClosure n C c, y = n + k2 := by
                rintro ⟨k2, hk2, e⟩
                exact hy' k2 (Finset.mem_insert_of_mem hk2) e
              have hvy : V C.gates z y = true := by
                rw [if_neg hyc] at hny
                rw [← (ih y hy).1 hyo]
                exact hny
              obtain ⟨h1, h2⟩ := hr' r hrm hrr
              have hvc : V C.gates z (n + c) = true := by
                rw [hVc]
                rcases H1 r hrm with hs | hs
                · have hb : V C.gates z b = true := h2 hs z hvy
                  rw [hs] at hrv
                  rw [hrv, hb]
                  rfl
                · have ha : V C.gates z a = true := h1 hs z hvy
                  rw [hs] at hrv
                  rw [hrv, ha]
                  rfl
              rw [huw]
              rcases Finset.mem_insert.mp hw with h | h
              · rw [h]; exact hvc
              · exact orReaches_val n C z c (n + w) (hOgt w h).2.2 hvc
            rw [hand, eval_and2, eval_and2, Bool.and_eq_true, Bool.and_eq_true]
            constructor
            · rintro ⟨h1, h2⟩
              have g1 : V C.gates z i1 = true := by
                rcases up i1 hm1 hr1 h1 with h | ⟨hw, hr⟩
                · exact h
                · exact bad i1 i2 (Or.inl hi12) hr2 hw hr h2
              have g2 : V C.gates z i2 = true := by
                rcases up i2 hm2 hr2 h2 with h | ⟨hw, hr⟩
                · exact h
                · exact bad i2 i1 (Or.inr hi12) hr1 hw hr h1
              exact ⟨g1, g2⟩
            · rintro ⟨h1, h2⟩
              exact ⟨lo i1 hm1 hr1 h1, lo i2 hm2 hr2 h2⟩
          · -- an OR gate outside the closure reads no wire of c or of the closure
            have nob : ∀ t, t ∈ (gateAt C k).inputs → t < n + k →
                ¬ ∃ w ∈ insert c (orClosure n C c), t = n + w := by
              rintro t htm ht ⟨w, hw, e⟩
              apply hkO
              have hkc : k ≠ c := habove t htm ⟨w, hw, e⟩
              simp only [orClosure, Finset.mem_filter, Finset.mem_range]
              refine ⟨hk, hkc, (orReaches_iff n C k c).mpr ⟨hk, Or.inr ⟨hor, t, htm, ht, ?_⟩⟩⟩
              rw [e]
              rcases Finset.mem_insert.mp hw with h | h
              · rw [h]
                exact (orReaches_iff n C c c).mpr ⟨hc, Or.inl rfl⟩
              · exact (hOgt w h).2.2
            rw [hor, eval_or2, eval_or2, Bool.or_eq_true, Bool.or_eq_true]
            constructor
            · rintro (h | h)
              · rcases up i1 hm1 hr1 h with h' | ⟨hw, _⟩
                · exact Or.inl h'
                · exact absurd hw (nob i1 hm1 hr1)
              · rcases up i2 hm2 hr2 h with h' | ⟨hw, _⟩
                · exact Or.inr h'
                · exact absurd hw (nob i2 hm2 hr2)
            · rintro (h | h)
              · exact Or.inl (lo i1 hm1 hr1 h)
              · exact Or.inr (lo i2 hm2 hr2 h)
      · refine ⟨fun _ => ?_, ?_⟩
        · rw [V_ge _ z i (by rw [sub_len]; omega), V_ge _ z i (by omega)]
        · rintro ⟨k, hk, hik⟩
          have := (hOgt k hk).2.1
          omega

-- the size part: cones only shrink, and gate c leaves every cone
lemma cone_sub (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hrb : ReadsBack n C) (hc : c < C.gates.length) (hcin : (gateAt C c).inputs = [a, b])
    (H1 : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ m j, InCone n (substReads C n c sigma) j m → InCone n C j m ∧ j ≠ c := by
  have hab : a < n + c ∧ b < n + c := by
    have h := hrb c hc
    rw [hcin] at h
    exact ⟨h a (by simp), h b (by simp)⟩
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro j h
    rcases (inCone_iff n (substReads C n c sigma) j m).mp h with ⟨hm', k, hkm, hkin, hjk⟩
    have hm : m < C.gates.length := by rw [sub_len] at hm'; exact hm'
    rw [gateAt_get _ m hm', sub_get C n c sigma m hm hm'] at hkin
    simp only [List.mem_map] at hkin
    obtain ⟨i, him, hi⟩ := hkin
    rw [← gateAt_get C m hm] at him
    have hilt : i < n + m := hrb m hm i him
    by_cases hic : i = n + c
    · rw [if_pos hic] at hi
      have hmr : m ∈ readers n C c := by
        simp only [readers, Finset.mem_filter, Finset.mem_range]
        exact ⟨hm, hic ▸ him⟩
      have hkc : k < c := by
        rcases H1 m hmr with h | h <;> omega
      have hkin2 : n + k ∈ (gateAt C c).inputs := by
        rw [hcin, ← hi]
        rcases H1 m hmr with h | h <;> simp [h]
      have hcm : c < m := by omega
      have hkc2 : InCone n C k c := (inCone_iff n C k c).mpr ⟨hc, k, hkc, hkin2, Or.inl rfl⟩
      have hcin2 : n + c ∈ (gateAt C m).inputs := hic ▸ him
      rcases hjk with hjk | hjk
      · rw [hjk]
        exact ⟨(inCone_iff n C k m).mpr ⟨hm, c, hcm, hcin2, Or.inr hkc2⟩, by omega⟩
      · obtain ⟨h1, h2⟩ := ih k hkm j hjk
        have hjc : InCone n C j c := (inCone_iff n C j c).mpr ⟨hc, k, hkc, hkin2, Or.inr h1⟩
        exact ⟨(inCone_iff n C j m).mpr ⟨hm, c, hcm, hcin2, Or.inr hjc⟩, h2⟩
    · rw [if_neg hic] at hi
      have hkin2 : n + k ∈ (gateAt C m).inputs := hi ▸ him
      have hkne : k ≠ c := by omega
      rcases hjk with hjk | hjk
      · rw [hjk]
        exact ⟨(inCone_iff n C k m).mpr ⟨hm, k, hkm, hkin2, Or.inl rfl⟩, hkne⟩
      · obtain ⟨h1, h2⟩ := ih k hkm j hjk
        exact ⟨(inCone_iff n C j m).mpr ⟨hm, k, hkm, hkin2, Or.inr h1⟩, h2⟩

lemma live_drop (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hrb : ReadsBack n C) (hc : c < C.gates.length) (hcin : (gateAt C c).inputs = [a, b])
    (H1 : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b)
    (H3 : C.output ≠ n + c) (H4 : c ∈ liveGates n C) :
    liveSize n (substReads C n c sigma) + 1 ≤ liveSize n C := by
  have hout : (substReads C n c sigma).output = C.output := rfl
  have hsub : liveGates n (substReads C n c sigma) ⊆ (liveGates n C).erase c := by
    intro j hj
    simp only [liveGates, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjl, hno, hj2⟩ := hj
    rw [sub_len] at hjl
    rw [hout] at hno hj2
    rw [Finset.mem_erase]
    rcases hj2 with hj2 | hj2
    · refine ⟨by omega, ?_⟩
      simp only [liveGates, Finset.mem_filter, Finset.mem_range]
      exact ⟨hjl, hno, Or.inl hj2⟩
    · obtain ⟨h1, h2⟩ := cone_sub n C c a b sigma hrb hc hcin H1 _ j hj2
      refine ⟨h2, ?_⟩
      simp only [liveGates, Finset.mem_filter, Finset.mem_range]
      exact ⟨hjl, hno, Or.inr h1⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_erase_add_one H4
  unfold liveSize
  omega

theorem main : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C := by
  intro n C c a b sigma hA hc hcop hcin H1 H2 _ H3 H4
  refine ⟨?_, ?_⟩
  · intro k hk hkc hkO z
    have h := (sem n C c a b sigma hA hc hcop hcin H1 H2 z (n + k)).1 (by
      rintro ⟨k2, hk2, e⟩
      have hkk : k2 = k := by omega
      rw [hkk] at hk2
      exact hkO hk2)
    exact h
  · exact live_drop n C c a b sigma hA.2.1 hc hcin H1 (H3 c (Finset.mem_insert_self _ _)) H4

end PEqualNP.Outside.L_meta_3297

theorem PEqualNP.Outside.L_meta_3297 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C :=
  PEqualNP.Outside.L_meta_3297.main
