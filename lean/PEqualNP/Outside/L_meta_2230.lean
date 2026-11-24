import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2230

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

def rcell (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def rf (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    List (List (List ℕ)) :=
  gs.foldl (fun R g => R ++ [rcell S k R g]) R

def ini (S : List ℕ) (n : ℕ) : List (List (List ℕ)) := (List.range n).map (leafVectors S 1)

lemma rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) :
    readVectors C n S 1 = rf S 1 C.gates (ini S n) := rfl

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
  (readVectors C n S 1).getD w []

lemma V_gate (C : Circuit) (n : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    V C n S (n + j) = rcell S 1 (readVectors C n S 1) (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre, hgj⟩ := split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [gateAt_eq C j hj]; exact hgj
  rw [hga] at hrb ⊢
  have hc : readVectors C n S 1
      = rf S 1 post (rf S 1 pre (ini S n) ++ [rcell S 1 (rf S 1 pre (ini S n)) gj]) := by
    rw [rv_eq, hgs]
    simp only [rf, List.foldl_append, List.foldl_cons]
  have hl : (rf S 1 pre (ini S n)).length = n + j := by
    rw [rf_len]; simp [ini, hpre]
  have h1 : V C n S (n + j) = rcell S 1 (rf S 1 pre (ini S n)) gj := by
    unfold V
    rw [hc, rf_keep _ _ _ _ _ (by simp; omega), ← hl]
    simp [List.getD_eq_getElem?_getD]
  rw [h1]
  apply rcell_congr
  intro i hi
  have hlt : i < (rf S 1 pre (ini S n)).length := by rw [hl]; exact hrb i hi
  rw [hc, rf_keep S 1 post _ i (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]

lemma V_leaf (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) (hw : w < n) :
    V C n S w = leafVectors S 1 w := by
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
      capAdd 1 (capAdd 1 (S.map fun _ => 0) p) q = x := by
  rw [V_gate C n S j hj (by rw [hin]; intro i hi; simp at hi; omega)]
  simp only [rcell, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    mem_andStep, List.mem_singleton]
  constructor
  · rintro ⟨p2, ⟨z, rfl, p, hp, rfl⟩, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨_, ⟨_, rfl, p, hp, rfl⟩, q, hq, rfl⟩

lemma cap2 (a b x y x2 y2 : ℕ) :
    capAdd 1 (capAdd 1 (([a, b] : List ℕ).map fun _ => 0) [x, y]) [x2, y2]
      = [min (min x 2 + x2) 2, min (min y 2 + y2) 2] := by
  simp [capAdd]

lemma mem_leaf (a b w : ℕ) (v : List ℕ) :
    v ∈ leafVectors [a, b] 1 w ↔
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

lemma nz (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : Fin n) :
    ∀ w, ∀ v ∈ V C n [a.val, b.val] w, ∃ x y : ℕ, v = [x, y] ∧ 1 ≤ x + y := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    rcases wire_cases n C h w with hw | hw | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · rw [V_leaf C n _ w hw] at hv
      obtain ⟨hm, rfl⟩ := (mem_leaf a.val b.val w v).mp hv
      refine ⟨_, _, rfl, ?_⟩
      rcases hm with rfl | rfl <;> simp
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

lemma reach1 (n : ℕ) (C : Circuit) (h : IsAO2 n C) (S : List ℕ) (c : Fin n) (u : List ℕ)
    (hleaf : ∀ w < n, u ∈ V C n S w → w = c.val)
    (hand : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → u ∉ V C n S (n + k)) :
    ∀ w, u ∈ V C n S w →
      c ∈ orIn n C w ∧ val C.gates w (fun k1 : Fin n => decide (k1 = c)) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    rcases wire_cases n C h w with hw | hw | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · have hwc := hleaf w hw hv
      subst hwc
      refine ⟨?_, ?_⟩
      · simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
        first | exact Or.inl rfl | exact Or.inl trivial
      · rw [val_input C.gates _ _ hw]
        simp
    · rw [V_big C n S w hw] at hv
      simp at hv
    · exact absurd hv (hand k hk hop)
    · have key : ∀ ui, (ui = u1 ∨ ui = u2) → ui < n + k → u ∈ V C n S ui →
          c ∈ orIn n C (n + k) ∧
            val C.gates (n + k) (fun k1 : Fin n => decide (k1 = c)) = true := by
        intro ui hui hlt hmem
        obtain ⟨ho, hval⟩ := ih ui hlt hmem
        refine ⟨?_, val_or2 C _ k hk hop u1 u2 hin ui hui hlt hval⟩
        have hin2 : ui ∈ (gateAt C k).inputs := by rw [hin]; simpa using hui
        simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
        right
        rcases ho with ho | ⟨k2, hk2, hr, hop2, hmem2⟩
        · exact ⟨k, hk, (orReaches_iff n C k k hk).mpr (Or.inl rfl), hop, by rw [ho]; exact hin2⟩
        · have hn : n ≤ ui := (show n ≤ ui ∧ _ from hr).1
          exact ⟨k2, hk2, (orReaches_iff n C k2 k hk).mpr (Or.inr ⟨hop, ui, hin2, hn, hlt, hr⟩),
            hop2, hmem2⟩
      rcases (V_or C n S k hk hop u1 u2 hin h1 h2 u).mp hv with h3 | h3
      · exact key u1 (Or.inl rfl) h1 h3
      · exact key u2 (Or.inr rfl) h2 h3

lemma no_and (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : Fin n) (s t : ℕ) (hst : s + t = 1) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      [s, t] ∉ V C n [a.val, b.val] (n + k) := by
  intro k hk hop hv
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
    omega

lemma reachA (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : Fin n) :
    ∀ w, [1, 0] ∈ V C n [a.val, b.val] w →
      a ∈ orIn n C w ∧ val C.gates w (fun k1 : Fin n => decide (k1 = a)) = true := by
  apply reach1 n C h [a.val, b.val] a [1, 0]
  · intro w hw hv
    rw [V_leaf C n _ w hw] at hv
    obtain ⟨_, he⟩ := (mem_leaf a.val b.val w _).mp hv
    by_contra hne
    have hne2 : ¬ a.val = w := fun e => hne e.symm
    simp [hne2] at he
  · exact no_and n C h a b 1 0 rfl

lemma reachB (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : Fin n) :
    ∀ w, [0, 1] ∈ V C n [a.val, b.val] w →
      b ∈ orIn n C w ∧ val C.gates w (fun k1 : Fin n => decide (k1 = b)) = true := by
  apply reach1 n C h [a.val, b.val] b [0, 1]
  · intro w hw hv
    rw [V_leaf C n _ w hw] at hv
    obtain ⟨_, he⟩ := (mem_leaf a.val b.val w _).mp hv
    by_contra hne
    have hne2 : ¬ b.val = w := fun e => hne e.symm
    simp [hne2] at he
  · exact no_and n C h a b 0 1 rfl

lemma main2 (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : Fin n) (hne : a.val ≠ b.val) :
    ∀ w, [1, 1] ∈ V C n [a.val, b.val] w →
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C w j ∧
        ((a ∈ side (n := n) C j 0 ∧ b ∈ side (n := n) C j 1) ∨
          (b ∈ side (n := n) C j 0 ∧ a ∈ side (n := n) C j 1)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    rcases wire_cases n C h w with hw | hw | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · exfalso
      rw [V_leaf C n _ w hw] at hv
      obtain ⟨_, he⟩ := (mem_leaf a.val b.val w _).mp hv
      by_cases e1 : a.val = w
      · by_cases e2 : b.val = w
        · omega
        · simp [e2] at he
      · simp [e1] at he
    · rw [V_big C n _ w hw] at hv
      simp at hv
    · obtain ⟨p, hp, q, hq, he⟩ := (V_and C n _ k hk hop u1 u2 hin h1 h2 _).mp hv
      obtain ⟨x, y, rfl, hxy⟩ := nz n C h a b u1 p hp
      obtain ⟨x2, y2, rfl, hxy2⟩ := nz n C h a b u2 q hq
      rw [cap2] at he
      injection he with e1 e2
      injection e2 with e2 e3
      have hcase : (x = 1 ∧ y = 0 ∧ x2 = 0 ∧ y2 = 1) ∨ (x = 0 ∧ y = 1 ∧ x2 = 1 ∧ y2 = 0) := by
        omega
      refine ⟨k, hk, hop, (orReaches_iff n C k k hk).mpr (Or.inl rfl), ?_⟩
      have hs0 : side (n := n) C k 0 = orIn n C u1 := by simp [side, opnd, hin]
      have hs1 : side (n := n) C k 1 = orIn n C u2 := by simp [side, opnd, hin]
      rw [hs0, hs1]
      rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inl ⟨(reachA n C h a b u1 hp).1, (reachB n C h a b u2 hq).1⟩
      · exact Or.inr ⟨(reachB n C h a b u1 hp).1, (reachA n C h a b u2 hq).1⟩
    · have key : ∀ ui, (ui = u1 ∨ ui = u2) → ui < n + k → [1, 1] ∈ V C n [a.val, b.val] ui →
          ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C (n + k) j ∧
            ((a ∈ side (n := n) C j 0 ∧ b ∈ side (n := n) C j 1) ∨
              (b ∈ side (n := n) C j 0 ∧ a ∈ side (n := n) C j 1)) := by
        intro ui hui hlt hmem
        obtain ⟨j, hj, hjop, hr, hs⟩ := ih ui hlt hmem
        have hin2 : ui ∈ (gateAt C k).inputs := by rw [hin]; simpa using hui
        have hn : n ≤ ui := (show n ≤ ui ∧ _ from hr).1
        exact ⟨j, hj, hjop,
          (orReaches_iff n C j k hk).mpr (Or.inr ⟨hop, ui, hin2, hn, hlt, hr⟩), hs⟩
      rcases (V_or C n _ k hk hop u1 u2 hin h1 h2 _).mp hv with h3 | h3
      · exact key u1 (Or.inl rfl) h1 h3
      · exact key u2 (Or.inr rfl) h2 h3

end PEqualNP.Outside.L_meta_2230

theorem PEqualNP.Outside.L_meta_2230 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin n), PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → a < b → PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true → ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧ ((a ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ b ∈ PEqualNP.TopForm.side (n := n) C j 1) ∨ (b ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ a ∈ PEqualNP.TopForm.side (n := n) C j 1)) := by
  intro n C a b h hf hab hr
  have hne : a.val ≠ b.val := by
    have := Fin.lt_def.mp hab
    omega
  unfold PEqualNP.ReadK.readsAtMost at hr
  rw [List.any_eq_true] at hr
  obtain ⟨v, hv, hall⟩ := hr
  have hv2 : v ∈ PEqualNP.Outside.L_meta_2230.V C n [a.val, b.val] C.output := hv
  obtain ⟨x, y, rfl, hxy⟩ := PEqualNP.Outside.L_meta_2230.nz n C h a b C.output v hv2
  simp at hall
  have hcase : (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1) := by omega
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exfalso
    have h1 := (PEqualNP.Outside.L_meta_2230.reachA n C h a b C.output hv2).2
    have h2 : PEqualNP.Outside.L_meta_2230.val C.gates C.output
        (fun k1 : Fin n => decide (k1 = a)) = false := hf a
    rw [h1] at h2
    exact Bool.noConfusion h2
  · exfalso
    have h1 := (PEqualNP.Outside.L_meta_2230.reachB n C h a b C.output hv2).2
    have h2 : PEqualNP.Outside.L_meta_2230.val C.gates C.output
        (fun k1 : Fin n => decide (k1 = b)) = false := hf b
    rw [h1] at h2
    exact Bool.noConfusion h2
  · exact PEqualNP.Outside.L_meta_2230.main2 n C h a b hne C.output hv2
