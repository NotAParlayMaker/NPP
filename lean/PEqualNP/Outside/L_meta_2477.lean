import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2477

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_pre (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_pre _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_or2 (C : Circuit) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (u1 u2 : ℕ) (hin : (gateAt C k).inputs = [u1, u2])
    (u : ℕ) (hu : u = u1 ∨ u = u2) (hlt : u < n + k) (hv : val C.gates u x = true) :
    val C.gates (n + k) x = true := by
  rw [gateAt_eq C k hk] at hop hin
  exact (val_or C.gates x k hk hop).mpr ⟨u, by rw [hin]; simpa using hu, hlt, hv⟩

def rcell (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def rf (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    List (List (List ℕ)) :=
  gs.foldl (fun R g => R ++ [rcell S k R g]) R

def ini (S : List ℕ) (n : ℕ) : List (List (List ℕ)) := (List.range n).map (leafVectors S 2)

lemma rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) :
    readVectors C n S 2 = rf S 2 C.gates (ini S n) := rfl

lemma rf_len (S : List ℕ) (k : ℕ) (gs : List Gate) :
    ∀ R : List (List (List ℕ)), (rf S k gs R).length = R.length + gs.length := by
  induction gs with
  | nil => intro R; simp [rf]
  | cons g gs ih =>
    intro R
    have := ih (R ++ [rcell S k R g])
    simp only [rf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma rf_keep (S : List ℕ) (k : ℕ) (gs : List Gate) :
    ∀ (R : List (List (List ℕ))) (i : ℕ), i < R.length →
      (rf S k gs R).getD i [] = R.getD i [] := by
  induction gs with
  | nil => intro R i _; rfl
  | cons g gs ih =>
    intro R i hi
    have := ih (R ++ [rcell S k R g]) i (by simp; omega)
    simp only [rf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma rcell_congr (S : List ℕ) (k : ℕ) (R R2 : List (List (List ℕ))) (g : Gate)
    (h : ∀ i ∈ g.inputs, R.getD i [] = R2.getD i []) : rcell S k R g = rcell S k R2 g := by
  unfold rcell
  rw [List.map_congr_left h]

def V (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S 2).getD w []

lemma V_gate (C : Circuit) (n : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    V C n S (n + j) = rcell S 2 (readVectors C n S 2) (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre, hgj⟩ := split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [gateAt_eq C j hj]; exact hgj
  rw [hga] at hrb ⊢
  have hc : readVectors C n S 2
      = rf S 2 post (rf S 2 pre (ini S n) ++ [rcell S 2 (rf S 2 pre (ini S n)) gj]) := by
    rw [rv_eq, hgs]
    simp only [rf, List.foldl_append, List.foldl_cons]
  have hl : (rf S 2 pre (ini S n)).length = n + j := by
    rw [rf_len]; simp [ini, hpre]
  have h1 : V C n S (n + j) = rcell S 2 (rf S 2 pre (ini S n)) gj := by
    unfold V
    rw [hc, rf_keep _ _ _ _ _ (by simp; omega), ← hl]
    simp [List.getD_eq_getElem?_getD]
  rw [h1]
  apply rcell_congr
  intro i hi
  have hlt : i < (rf S 2 pre (ini S n)).length := by rw [hl]; exact hrb i hi
  rw [hc, rf_keep S 2 post _ i (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]

lemma V_leaf (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) (hw : w < n) :
    V C n S w = leafVectors S 2 w := by
  unfold V
  rw [rv_eq, rf_keep _ _ _ _ _ (by simp [ini]; exact hw)]
  simp [ini, List.getD_eq_getElem?_getD, hw]

lemma V_big (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    V C n S w = [] := by
  unfold V
  rw [List.getD_eq_default _ _ (by rw [rv_eq, rf_len]; simp [ini]; exact hw)]

lemma mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h1 | rfl)
      · exact h1
      · exact h
  · simp

lemma mem_foldl_insertNew (L : List (List ℕ)) :
    ∀ (acc : List (List ℕ)) (x : List ℕ), x ∈ L.foldl insertNew acc ↔ x ∈ acc ∨ x ∈ L := by
  induction L with
  | nil => intro acc x; simp
  | cons v L ih =>
    intro acc x
    rw [List.foldl_cons, ih, mem_insertNew]
    simp [or_assoc]

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (x : List ℕ) :
    x ∈ andStep k A B ↔ ∃ p ∈ A, ∃ q ∈ B, capAdd k p q = x := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp [List.mem_flatMap, List.mem_map]

lemma V_or (C : Circuit) (n : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (u1 u2 : ℕ) (hin : (gateAt C j).inputs = [u1, u2])
    (h1 : u1 < n + j) (h2 : u2 < n + j) (x : List ℕ) :
    x ∈ V C n S (n + j) ↔ x ∈ V C n S u1 ∨ x ∈ V C n S u2 := by
  rw [V_gate C n S j hj (by rw [hin]; intro i hi; simp at hi; omega)]
  simp only [rcell, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    mem_foldl_insertNew]
  simp [V]

lemma V_and (C : Circuit) (n : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (u1 u2 : ℕ) (hin : (gateAt C j).inputs = [u1, u2])
    (h1 : u1 < n + j) (h2 : u2 < n + j) (x : List ℕ) :
    x ∈ V C n S (n + j) ↔ ∃ p ∈ V C n S u1, ∃ q ∈ V C n S u2,
      capAdd 2 (capAdd 2 (S.map fun _ => 0) p) q = x := by
  rw [V_gate C n S j hj (by rw [hin]; intro i hi; simp at hi; omega)]
  simp only [rcell, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    mem_andStep, List.mem_singleton]
  constructor
  · rintro ⟨p2, ⟨z, rfl, p, hp, rfl⟩, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨_, ⟨_, rfl, p, hp, rfl⟩, q, hq, rfl⟩

lemma cap2 (a b x y x2 y2 : ℕ) :
    capAdd 2 (capAdd 2 (([a, b] : List ℕ).map fun _ => 0) [x, y]) [x2, y2]
      = [min (min x 3 + x2) 3, min (min y 3 + y2) 3] := by
  simp [capAdd]

lemma mem_leaf (a b w : ℕ) (v : List ℕ) :
    v ∈ leafVectors [a, b] 2 w ↔
      (w = a ∨ w = b) ∧ v = [if a = w then 1 else 0, if b = w then 1 else 0] := by
  unfold leafVectors
  by_cases h : w = a ∨ w = b
  · simp [h]
  · simp [h]

lemma wire_cases (n : ℕ) (C : Circuit) (h : IsAO2 n C) (w : ℕ) :
    w < n ∨ n + C.gates.length ≤ w ∨ ∃ k, k < C.gates.length ∧ w = n + k ∧
      ∃ u1 u2, (gateAt C k).inputs = [u1, u2] ∧ u1 < n + k ∧ u2 < n + k ∧
        ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) := by
  obtain ⟨hao, hrb, hlen⟩ := h
  by_cases h1 : w < n
  · exact Or.inl h1
  by_cases h2 : n + C.gates.length ≤ w
  · exact Or.inr (Or.inl h2)
  right; right
  have hk : w - n < C.gates.length := by omega
  have hmem : gateAt C (w - n) ∈ C.gates := by
    rw [gateAt_eq C _ hk]; exact List.getElem_mem hk
  obtain ⟨u1, u2, hab⟩ := List.length_eq_two.mp (hlen _ hmem)
  exact ⟨w - n, hk, by omega, u1, u2, hab, hrb _ hk u1 (by rw [hab]; simp),
    hrb _ hk u2 (by rw [hab]; simp), hao _ hmem⟩


lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w, (w ∈ g.inputs ∧ n ≤ w ∧ w < n + cs.length) ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp [orStep, List.getD_eq_getElem?_getD, hop]
  · simp [orStep, List.getD_eq_getElem?_getD, hop]

lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

lemma orReaches_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ OrReaches n C w g) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : ∀ x, x ∈ (orSets n C).getD k [] ↔ x = k ∨ (gk.op = GateOp.or ∧
      ∃ w, (w ∈ gk.inputs ∧ n ≤ w ∧ w < n + k) ∧
        x ∈ (pre.foldl (orStep n) []).getD (w - n) []) := by
    intro x
    rw [hc, orFold_getD_lt n post _ k (by omega)]
    have h := orStep_mem_last n (pre.foldl (orStep n) []) gk x
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have e : n + k - n = k := by omega
  unfold OrReaches
  rw [e, h1 g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, ⟨hw, hn, hlt⟩, h⟩⟩
    · exact Or.inl h
    · right
      refine ⟨hop, w, hw, hn, hlt, hn, ?_⟩
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro (h | ⟨hop, w, hw, hn, hlt, _, h⟩)
    · exact ⟨by omega, Or.inl h⟩
    · refine ⟨by omega, Or.inr ⟨hop, w, ⟨hw, hn, hlt⟩, ?_⟩⟩
      rw [← h2 (w - n) (by omega)]
      exact h


lemma swp (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) :
    ∀ t, ∀ v ∈ V C n [a, b] t, ∃ x y : ℕ, v = [x, y] ∧ [y, x] ∈ V C n [b, a] t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v hv
    rcases wire_cases n C h t with ht | ht | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · rw [V_leaf C n _ t ht] at hv
      obtain ⟨hm, rfl⟩ := (mem_leaf a b t v).mp hv
      refine ⟨_, _, rfl, ?_⟩
      rw [V_leaf C n _ t ht]
      exact (mem_leaf b a t _).mpr ⟨hm.symm, rfl⟩
    · rw [V_big C n _ t ht] at hv
      simp at hv
    · obtain ⟨p, hp, q, hq, rfl⟩ := (V_and C n _ k hk hop u1 u2 hin h1 h2 v).mp hv
      obtain ⟨x, y, rfl, hs⟩ := ih u1 (by omega) p hp
      obtain ⟨x2, y2, rfl, hs2⟩ := ih u2 (by omega) q hq
      rw [cap2]
      refine ⟨_, _, rfl, ?_⟩
      exact (V_and C n _ k hk hop u1 u2 hin h1 h2 _).mpr ⟨_, hs, _, hs2, cap2 b a y x y2 x2⟩
    · rcases (V_or C n _ k hk hop u1 u2 hin h1 h2 v).mp hv with h3 | h3
      · obtain ⟨x, y, rfl, hs⟩ := ih u1 h1 v h3
        exact ⟨x, y, rfl, (V_or C n _ k hk hop u1 u2 hin h1 h2 _).mpr (Or.inl hs)⟩
      · obtain ⟨x, y, rfl, hs⟩ := ih u2 h2 v h3
        exact ⟨x, y, rfl, (V_or C n _ k hk hop u1 u2 hin h1 h2 _).mpr (Or.inr hs)⟩


lemma nz (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) :
    ∀ w, ∀ v ∈ V C n [a, b] w, ∃ x y : ℕ, v = [x, y] ∧ 1 ≤ x + y := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    rcases wire_cases n C h w with hw | hw | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · rw [V_leaf C n _ w hw] at hv
      obtain ⟨hm, rfl⟩ := (mem_leaf a b w v).mp hv
      refine ⟨_, _, rfl, ?_⟩
      rcases hm with hm | hm
      · simp [hm]
      · simp [hm]
    · rw [V_big C n _ w hw] at hv
      simp at hv
    · obtain ⟨p, hp, q, hq, rfl⟩ := (V_and C n _ k hk hop u1 u2 hin h1 h2 v).mp hv
      obtain ⟨x, y, rfl, hxy⟩ := ih u1 (by omega) p hp
      obtain ⟨x2, y2, rfl, hxy2⟩ := ih u2 (by omega) q hq
      rw [cap2]
      exact ⟨_, _, rfl, by omega⟩
    · rcases (V_or C n _ k hk hop u1 u2 hin h1 h2 v).mp hv with h3 | h3
      · exact ih u1 (by omega) v h3
      · exact ih u2 (by omega) v h3

lemma climb (n : ℕ) (C : Circuit) (h : IsAO2 n C) (S : List ℕ) (v : List ℕ) (P : ℕ → Prop)
    (hleaf : ∀ t, t < n → v ∈ V C n S t → P t)
    (hand : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
      v ∈ V C n S (n + k) → P (n + k))
    (hor : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ ui, ui ∈ (gateAt C k).inputs → ui < n + k → P ui → P (n + k)) :
    ∀ t, v ∈ V C n S t → P t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hv
    rcases wire_cases n C h t with ht | ht | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · exact hleaf t ht hv
    · rw [V_big C n S t ht] at hv
      simp at hv
    · exact hand k hk hop hv
    · rcases (V_or C n S k hk hop u1 u2 hin h1 h2 v).mp hv with h3 | h3
      · exact hor k hk hop u1 (by rw [hin]; simp) h1 (ih u1 h1 h3)
      · exact hor k hk hop u2 (by rw [hin]; simp) h2 (ih u2 h2 h3)

lemma leaf_vec (n : ℕ) (C : Circuit) (a b t : ℕ) (ht : t < n) (s r : ℕ)
    (hv : [s, r] ∈ V C n [a, b] t) :
    (t = a ∨ t = b) ∧ s = (if a = t then 1 else 0) ∧ r = (if b = t then 1 else 0) := by
  rw [V_leaf C n _ t ht] at hv
  obtain ⟨hm, he⟩ := (mem_leaf a b t _).mp hv
  injection he with e1 e2
  injection e2 with e2 e3
  exact ⟨hm, e1, e2⟩

lemma and_split (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (s r : ℕ) (hv : [s, r] ∈ V C n [a, b] (n + k)) :
    ∃ u1 u2 x y x2 y2 : ℕ, (gateAt C k).inputs = [u1, u2] ∧ [x, y] ∈ V C n [a, b] u1 ∧
      [x2, y2] ∈ V C n [a, b] u2 ∧ 1 ≤ x + y ∧ 1 ≤ x2 + y2 ∧
      min (min x 3 + x2) 3 = s ∧ min (min y 3 + y2) 3 = r := by
  rcases wire_cases n C h (n + k) with hw | hw | ⟨k2, hk2, e, u1, u2, hin, h1, h2, _⟩
  · omega
  · omega
  · have hkk : k2 = k := by omega
    subst hkk
    obtain ⟨p, hp, q, hq, he⟩ := (V_and C n _ k2 hk2 hop u1 u2 hin h1 h2 _).mp hv
    obtain ⟨x, y, rfl, hxy⟩ := nz n C h a b u1 p hp
    obtain ⟨x2, y2, rfl, hxy2⟩ := nz n C h a b u2 q hq
    rw [cap2] at he
    injection he with e1 e2
    injection e2 with e2 e3
    exact ⟨u1, u2, x, y, x2, y2, hin, hp, hq, hxy, hxy2, e1, e2⟩

def Reach (n : ℕ) (C : Circuit) (a t : ℕ) : Prop :=
  ∃ i : Fin n, i.val = a ∧ i ∈ orIn n C t

def AG (C : Circuit) (j K F : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
    ((gateAt C j).inputs = [K, F] ∨ (gateAt C j).inputs = [F, K])

def T0 (n : ℕ) (C : Circuit) (a b t : ℕ) : Prop :=
  ∃ j K F, AG C j K F ∧ Reach n C a K ∧ Reach n C b F ∧ OrReaches n C t j

def DD (n : ℕ) (C : Circuit) (b t : ℕ) : Prop :=
  ∃ j F4 F5, AG C j F4 F5 ∧ Reach n C b F4 ∧ Reach n C b F5 ∧ OrReaches n C t j

def T1 (n : ℕ) (C : Circuit) (a b t : ℕ) : Prop :=
  ∃ j2 j3 K F V1 F3, AG C j2 K F ∧ Reach n C a K ∧ Reach n C b F ∧ OrReaches n C V1 j2 ∧
    AG C j3 V1 F3 ∧ Reach n C b F3 ∧ OrReaches n C t j3

def T2 (n : ℕ) (C : Circuit) (a b t : ℕ) : Prop :=
  ∃ j4 j5 F4 F5 U1 K, AG C j4 F4 F5 ∧ Reach n C b F4 ∧ Reach n C b F5 ∧ OrReaches n C U1 j4 ∧
    AG C j5 K U1 ∧ Reach n C a K ∧ OrReaches n C t j5

lemma OrR_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := (orReaches_iff n C k k hk).mpr (Or.inl rfl)

lemma OrR_up (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (ui : ℕ) (hin2 : ui ∈ (gateAt C k).inputs)
    (hlt : ui < n + k) (j : ℕ) (hr : OrReaches n C ui j) : OrReaches n C (n + k) j :=
  (orReaches_iff n C j k hk).mpr
    (Or.inr ⟨hop, ui, hin2, (show n ≤ ui ∧ _ from hr).1, hlt, hr⟩)

lemma Reach_leaf (n : ℕ) (C : Circuit) (t : ℕ) (ht : t < n) : Reach n C t t := by
  refine ⟨⟨t, ht⟩, rfl, ?_⟩
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  first | exact Or.inl rfl | exact Or.inl trivial

lemma Reach_up (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (ui : ℕ) (hin2 : ui ∈ (gateAt C k).inputs)
    (hlt : ui < n + k) (a : ℕ) (hr : Reach n C a ui) : Reach n C a (n + k) := by
  obtain ⟨i, hi, ho⟩ := hr
  refine ⟨i, hi, ?_⟩
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
  right
  rcases ho with ho | ⟨k2, hk2, hr2, hop2, hmem2⟩
  · exact ⟨k, hk, OrR_self n C k hk, hop, by rw [ho]; exact hin2⟩
  · exact ⟨k2, hk2, OrR_up n C k hk hop ui hin2 hlt k2 hr2, hop2, hmem2⟩

lemma RA (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) :
    ∀ t, [1, 0] ∈ V C n [a, b] t → Reach n C a t := by
  apply climb n C h [a, b] [1, 0] (fun t => Reach n C a t)
  · intro t ht hv
    obtain ⟨_, e1, _⟩ := leaf_vec n C a b t ht 1 0 hv
    have hat : a = t := by
      by_contra hne
      simp [hne] at e1
    subst hat
    exact Reach_leaf n C a ht
  · intro k hk hop hv
    exfalso
    obtain ⟨u1, u2, x, y, x2, y2, _, _, _, hxy, hxy2, e1, e2⟩ :=
      and_split n C h a b k hk hop 1 0 hv
    omega
  · intro k hk hop ui hin2 hlt hP
    exact Reach_up n C k hk hop ui hin2 hlt a hP

lemma swp1 (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b t s r : ℕ)
    (hv : [s, r] ∈ V C n [a, b] t) : [r, s] ∈ V C n [b, a] t := by
  obtain ⟨x, y, e, hs⟩ := swp n C h a b t _ hv
  injection e with e1 e2
  injection e2 with e2 e3
  subst e1
  subst e2
  exact hs

lemma RB (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) :
    ∀ t, [0, 1] ∈ V C n [a, b] t → Reach n C b t := by
  intro t hv
  exact RA n C h b a t (swp1 n C h a b t 0 1 hv)

lemma P0 (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) (hne : a ≠ b) :
    ∀ t, [1, 1] ∈ V C n [a, b] t → T0 n C a b t := by
  apply climb n C h [a, b] [1, 1] (fun t => T0 n C a b t)
  · intro t ht hv
    exfalso
    obtain ⟨_, e1, e2⟩ := leaf_vec n C a b t ht 1 1 hv
    by_cases c1 : a = t
    · by_cases c2 : b = t
      · exact hne (c1.trans c2.symm)
      · simp [c2] at e2
    · simp [c1] at e1
  · intro k hk hop hv
    obtain ⟨u1, u2, x, y, x2, y2, hin, hp, hq, hxy, hxy2, e1, e2⟩ :=
      and_split n C h a b k hk hop 1 1 hv
    have hcase : (x = 1 ∧ y = 0 ∧ x2 = 0 ∧ y2 = 1) ∨ (x = 0 ∧ y = 1 ∧ x2 = 1 ∧ y2 = 0) := by
      omega
    rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨k, u1, u2, ⟨hk, hop, Or.inl hin⟩, RA n C h a b u1 hp, RB n C h a b u2 hq,
        OrR_self n C k hk⟩
    · exact ⟨k, u2, u1, ⟨hk, hop, Or.inr hin⟩, RA n C h a b u2 hq, RB n C h a b u1 hp,
        OrR_self n C k hk⟩
  · intro k hk hop ui hin2 hlt hP
    obtain ⟨j, K, F, hg, hK, hF, hr⟩ := hP
    exact ⟨j, K, F, hg, hK, hF, OrR_up n C k hk hop ui hin2 hlt j hr⟩

lemma PD (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) :
    ∀ t, [0, 2] ∈ V C n [a, b] t → DD n C b t := by
  apply climb n C h [a, b] [0, 2] (fun t => DD n C b t)
  · intro t ht hv
    exfalso
    obtain ⟨_, _, e2⟩ := leaf_vec n C a b t ht 0 2 hv
    by_cases c2 : b = t
    · simp [c2] at e2
    · simp [c2] at e2
  · intro k hk hop hv
    obtain ⟨u1, u2, x, y, x2, y2, hin, hp, hq, hxy, hxy2, e1, e2⟩ :=
      and_split n C h a b k hk hop 0 2 hv
    have hcase : x = 0 ∧ y = 1 ∧ x2 = 0 ∧ y2 = 1 := by omega
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
    exact ⟨k, u1, u2, ⟨hk, hop, Or.inl hin⟩, RB n C h a b u1 hp, RB n C h a b u2 hq,
      OrR_self n C k hk⟩
  · intro k hk hop ui hin2 hlt hP
    obtain ⟨j, K, F, hg, hK, hF, hr⟩ := hP
    exact ⟨j, K, F, hg, hK, hF, OrR_up n C k hk hop ui hin2 hlt j hr⟩

lemma P12 (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) (hne : a ≠ b) :
    ∀ t, [1, 2] ∈ V C n [a, b] t → T1 n C a b t ∨ T2 n C a b t := by
  apply climb n C h [a, b] [1, 2] (fun t => T1 n C a b t ∨ T2 n C a b t)
  · intro t ht hv
    exfalso
    obtain ⟨_, _, e2⟩ := leaf_vec n C a b t ht 1 2 hv
    by_cases c2 : b = t
    · simp [c2] at e2
    · simp [c2] at e2
  · intro k hk hop hv
    obtain ⟨u1, u2, x, y, x2, y2, hin, hp, hq, hxy, hxy2, e1, e2⟩ :=
      and_split n C h a b k hk hop 1 2 hv
    have hcase : (x = 1 ∧ y = 0 ∧ x2 = 0 ∧ y2 = 2) ∨ (x = 1 ∧ y = 1 ∧ x2 = 0 ∧ y2 = 1) ∨
        (x = 0 ∧ y = 1 ∧ x2 = 1 ∧ y2 = 1) ∨ (x = 0 ∧ y = 2 ∧ x2 = 1 ∧ y2 = 0) := by
      omega
    rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩
    · right
      obtain ⟨j4, F4, F5, hg, h4, h5, hr⟩ := PD n C h a b u2 hq
      exact ⟨j4, k, F4, F5, u2, u1, hg, h4, h5, hr, ⟨hk, hop, Or.inl hin⟩, RA n C h a b u1 hp,
        OrR_self n C k hk⟩
    · left
      obtain ⟨j2, K, F, hg, hK, hF, hr⟩ := P0 n C h a b hne u1 hp
      exact ⟨j2, k, K, F, u1, u2, hg, hK, hF, hr, ⟨hk, hop, Or.inl hin⟩, RB n C h a b u2 hq,
        OrR_self n C k hk⟩
    · left
      obtain ⟨j2, K, F, hg, hK, hF, hr⟩ := P0 n C h a b hne u2 hq
      exact ⟨j2, k, K, F, u2, u1, hg, hK, hF, hr, ⟨hk, hop, Or.inr hin⟩, RB n C h a b u1 hp,
        OrR_self n C k hk⟩
    · right
      obtain ⟨j4, F4, F5, hg, h4, h5, hr⟩ := PD n C h a b u1 hp
      exact ⟨j4, k, F4, F5, u1, u2, hg, h4, h5, hr, ⟨hk, hop, Or.inr hin⟩, RA n C h a b u2 hq,
        OrR_self n C k hk⟩
  · intro k hk hop ui hin2 hlt hP
    rcases hP with hP | hP
    · left
      obtain ⟨j2, j3, K, F, V1, F3, g1, g2, g3, g4, g5, g6, hr⟩ := hP
      exact ⟨j2, j3, K, F, V1, F3, g1, g2, g3, g4, g5, g6, OrR_up n C k hk hop ui hin2 hlt j3 hr⟩
    · right
      obtain ⟨j4, j5, F4, F5, U1, K, g1, g2, g3, g4, g5, g6, hr⟩ := hP
      exact ⟨j4, j5, F4, F5, U1, K, g1, g2, g3, g4, g5, g6, OrR_up n C k hk hop ui hin2 hlt j5 hr⟩

lemma main (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) (hne : a ≠ b) (t : ℕ)
    (hv : [1, 1] ∈ V C n [a, b] t ∨ [1, 2] ∈ V C n [a, b] t) :
    T0 n C a b t ∨ T1 n C a b t ∨ T2 n C a b t := by
  rcases hv with hv | hv
  · exact Or.inl (P0 n C h a b hne t hv)
  · exact Or.inr (P12 n C h a b hne t hv)

end PEqualNP.Outside.L_meta_2477

theorem PEqualNP.Outside.L_meta_2477 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → (([1, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output []) → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = u ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = w ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = u ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = w ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = w ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = w ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = w ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = u ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5))) ∧ ([2, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] → ((∃ j_6 K_4 F_6, (j_6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [K_4, F_6] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [F_6, K_4])) ∧ (∃ i_9 : Fin n, i_9.val = w ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (K_4)) ∧ (∃ i_10 : Fin n, i_10.val = u ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_6) ∨ (∃ j_7 j_8 K_5 F_7 V_2 F_8, (j_7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [K_5, F_7] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [F_7, K_5])) ∧ (∃ i_11 : Fin n, i_11.val = w ∧ i_11 ∈ PEqualNP.TopForm.orIn n C (K_5)) ∧ (∃ i_12 : Fin n, i_12.val = u ∧ i_12 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_7 ∧ (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [V_2, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [F_8, V_2])) ∧ (∃ i_13 : Fin n, i_13.val = u ∧ i_13 ∈ PEqualNP.TopForm.orIn n C (F_8)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_8) ∨ (∃ j_9 j_10 F_9 F_10 U_2 K_6, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_9, F_10] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_10, F_9])) ∧ (∃ i_14 : Fin n, i_14.val = u ∧ i_14 ∈ PEqualNP.TopForm.orIn n C (F_9)) ∧ (∃ i_15 : Fin n, i_15.val = u ∧ i_15 ∈ PEqualNP.TopForm.orIn n C (F_10)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [K_6, U_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [U_2, K_6])) ∧ (∃ i_16 : Fin n, i_16.val = w ∧ i_16 ∈ PEqualNP.TopForm.orIn n C (K_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10))) := by
  intro n C u w h _ _ hne
  exact ⟨PEqualNP.Outside.L_meta_2477.main n C h u w hne C.output,
    fun h21 => PEqualNP.Outside.L_meta_2477.main n C h w u (Ne.symm hne) C.output
      (Or.inr (PEqualNP.Outside.L_meta_2477.swp1 n C h u w C.output 2 1 h21))⟩
