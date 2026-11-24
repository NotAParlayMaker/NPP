import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2239

section Sec2230

namespace P2230


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


end P2230

theorem s2230 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin n), PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → a < b → PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true → ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧ ((a ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ b ∈ PEqualNP.TopForm.side (n := n) C j 1) ∨ (b ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ a ∈ PEqualNP.TopForm.side (n := n) C j 1)) := by
  intro n C a b h hf hab hr
  have hne : a.val ≠ b.val := by
    have := Fin.lt_def.mp hab
    omega
  unfold PEqualNP.ReadK.readsAtMost at hr
  rw [List.any_eq_true] at hr
  obtain ⟨v, hv, hall⟩ := hr
  have hv2 : v ∈ PEqualNP.Outside.L_meta_2239.P2230.V C n [a.val, b.val] C.output := hv
  obtain ⟨x, y, rfl, hxy⟩ := PEqualNP.Outside.L_meta_2239.P2230.nz n C h a b C.output v hv2
  simp at hall
  have hcase : (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1) := by omega
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exfalso
    have h1 := (PEqualNP.Outside.L_meta_2239.P2230.reachA n C h a b C.output hv2).2
    have h2 : PEqualNP.Outside.L_meta_2239.P2230.val C.gates C.output
        (fun k1 : Fin n => decide (k1 = a)) = false := hf a
    rw [h1] at h2
    exact Bool.noConfusion h2
  · exfalso
    have h1 := (PEqualNP.Outside.L_meta_2239.P2230.reachB n C h a b C.output hv2).2
    have h2 : PEqualNP.Outside.L_meta_2239.P2230.val C.gates C.output
        (fun k1 : Fin n => decide (k1 = b)) = false := hf b
    rw [h1] at h2
    exact Bool.noConfusion h2
  · exact PEqualNP.Outside.L_meta_2239.P2230.main2 n C h a b hne C.output hv2

end Sec2230

section Sec2231

namespace P2231


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
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
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

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

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

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

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

lemma opnd_eq {n : ℕ} {C : Circuit} (hA : PEqualNP.TopForm.IsAO2 n C) {a : ℕ}
    (ha : a < C.gates.length) :
    (gateAt C a).inputs = [PEqualNP.TopForm.opnd C a 0, PEqualNP.TopForm.opnd C a 1] := by
  have h2 := hA.2.2 _ (gateAt_mem ha)
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp h2
  simp [PEqualNP.TopForm.opnd, hpq]

lemma nfc (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : PEqualNP.TopForm.NoFourCycle G) :
    ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
  rintro a b c d hac hbd ⟨h1, h2, h3, h4⟩
  have h0 := h a c hac
  have h5 : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj c w).card :=
    Finset.one_lt_card.mpr ⟨b, by simp [h1, h2.symm], d, by simp [h4.symm, h3], hbd⟩
  omega

lemma and_true {n : ℕ} {C : Circuit} (hA : PEqualNP.TopForm.IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool)
    (u v : Fin n) (hu : u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C j 0))
    (hv : v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C j 1))
    (hxu : x u = true) (hxv : x v = true) :
    val C (List.ofFn x) (n + j) = true := by
  have hrb := hA.2.1 j hj
  have h0 : PEqualNP.TopForm.opnd C j 0 < n + j := hrb _ (by rw [opnd_eq hA hj]; simp)
  have h1 : PEqualNP.TopForm.opnd C j 1 < n + j := hrb _ (by rw [opnd_eq hA hj]; simp)
  rw [val_and (n := n) (by simp) hj hop]
  intro i hi
  rw [opnd_eq hA hj] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨h0, reach_var_val x _ u (mem_orIn_reach u hu) hxu⟩
  · exact ⟨h1, reach_var_val x _ v (mem_orIn_reach v hv) hxv⟩

lemma out_true {n : ℕ} {C : Circuit} {j : ℕ} (hr : OrReaches n C C.output j)
    (x : Fin n → Bool) (hv : val C (List.ofFn x) (n + j) = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true := by
  show val C (List.ofFn x) C.output = true
  exact orStep_up (n := n) (by simp) (orReaches_reach j _ hr).1 hv

lemma part1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
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
    have h := out_true hr _
      (and_true hA hj hop (fun k1 => decide (k1 = w)) w w hw0 hw1 (by simp) (by simp))
    rw [h1 w] at h
    cases h
  have hadj : ∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
      ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v := by
    intro u hu v hv
    by_contra hna
    have hne : u ≠ v := by
      rintro rfl
      exact hd u hu hv
    have h := out_true hr _
      (and_true hA hj hop (fun k2 => decide (k2 = u ∨ k2 = v)) u v hu hv (by simp) (by simp))
    rw [h2 u v hne hna] at h
    cases h
  exact ⟨hd, hadj, biclique_star G (nfc n G h4) _ _ hadj⟩

lemma part2 {n : ℕ} (C : Circuit) (E : Finset (Fin n × Fin n))
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


end P2231

theorem s2231 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.OrReaches n C C.output j → (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 → w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧ (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 → ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1)) ∧ (∀ F : Finset ℕ, (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), ∃ i ∈ F, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i ∧ ((e.1 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C i 1) ∨ (e.2 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.1 ∈ PEqualNP.TopForm.side (n := n) C i 1))) → ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)), e3.1 ∈ T ∨ e3.2 ∈ T) := by
  intro n G _ C h4 hA h1 h2
  exact ⟨fun j hj hop hr => PEqualNP.Outside.L_meta_2239.P2231.part1 G C h4 hA h1 h2 j hj hop hr,
    fun F hF => PEqualNP.Outside.L_meta_2239.P2231.part2 C _
      (fun i hi hop hr => (PEqualNP.Outside.L_meta_2239.P2231.part1 G C h4 hA h1 h2 i hi hop hr).2.2)
      F hF⟩

end Sec2231

section Sec2233

namespace P2233


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
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
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
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
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
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
lemma mem_le (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ x, x ∈ (orSets n C).getD k [] → x ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx
    rcases (orSets_mem_iff n C k x hk).mp hx with h | ⟨_, w, _, hn, hlt, hx2⟩
    · omega
    · have := ih (w - n) (by omega) (by omega) x hx2
      omega

open PEqualNP.CleanedNonEdge in
lemma parent (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ x, x ∈ (orSets n C).getD k [] → x ≠ k →
      ∃ p, p ∈ (orSets n C).getD k [] ∧ (gateAt C p).op = GateOp.or ∧
        n + x ∈ (gateAt C p).inputs := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx hne
    rcases (orSets_mem_iff n C k x hk).mp hx with h | ⟨hop, w, hw, hn, hlt, hx2⟩
    · exact absurd h hne
    · by_cases hxw : x = w - n
      · refine ⟨k, (orSets_mem_iff n C k k hk).mpr (Or.inl rfl), hop, ?_⟩
        have : n + x = w := by omega
        rw [this]; exact hw
      · obtain ⟨p, hp, hpop, hpin⟩ := ih (w - n) (by omega) (by omega) x hx2 hxw
        exact ⟨p, (orSets_mem_iff n C k p hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hp⟩), hpop, hpin⟩

open PEqualNP.CleanedNonEdge in
lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp [orSets, orFold_length]

open PEqualNP.CleanedNonEdge in
lemma main (n : ℕ) (C : Circuit) (F : Finset ℕ)
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
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_length]; omega)]
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
      have := mem_le n C r hr i hi
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
    exact (orSets_mem_iff n C r r hr).mpr (Or.inl rfl)
  have hsub : S.erase r ⊆ (O ×ˢ Finset.range 2).image
      (fun p : ℕ × ℕ => (gateAt C p.1).inputs.getD p.2 0 - n) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hxr, hxS⟩ := hx
    rw [hS, List.mem_toFinset] at hxS
    obtain ⟨p, hp, hpop, hpin⟩ := parent n C r hr x hxS hxr
    have hpr := mem_le n C r hr p hp
    have hplen : p < C.gates.length := by omega
    have hlen : (gateAt C p).inputs.length = 2 := by
      rw [gateAt_eq C p hplen]
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


end P2233

theorem s2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hA hF
  exact PEqualNP.Outside.L_meta_2239.P2233.main n C F hA.2.2 hF

end Sec2233

section Sec2234

namespace P2234


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs

def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)

lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega

lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]

lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih

open PEqualNP.CleanedNonEdge in
lemma cnFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma cnStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
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
lemma cnStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma cnFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact cnStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    g ∈ (orSets n C).getD k [] ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ g ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [cnFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, cnFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, cnFold_getD_lt n post _ m (by omega)]
    exact cnStep_getD_lt n _ gk m (by omega)
  have h3 := cnStep_mem_last n (pre.foldl (orStep n) []) gk g
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
lemma orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [cnFold_length]
  simp

open PEqualNP.CleanedNonEdge in
lemma reaches_to (n : ℕ) (C : Circuit) :
    ∀ k g, g ∈ (orSets n C).getD k [] → g < C.gates.length ∧ OrR n C (n + k) (n + g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    have hk : k < C.gates.length := by
      by_contra hk
      have hnone : (orSets n C)[k]? = none :=
        List.getElem?_eq_none (by rw [orSets_len]; omega)
      rw [List.getD_eq_getElem?_getD, hnone] at hg
      simp at hg
    rw [orSets_iff n C g k hk] at hg
    rcases hg with rfl | ⟨hop, w, hw, hn, hlt, h⟩
    · exact ⟨hk, Relation.ReflTransGen.refl⟩
    · obtain ⟨h4, h5⟩ := ih (w - n) (by omega) g h
      have hw' : n + (w - n) = w := by omega
      rw [hw'] at h5
      exact ⟨h4, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hw⟩ h5⟩

open PEqualNP.CleanedNonEdge in
lemma orReaches_iff (n : ℕ) (C : Circuit) (hA : AO n C) (w g : ℕ) :
    OrReaches n C w g ↔ (n ≤ w ∧ g < C.gates.length ∧ OrR n C w (n + g)) := by
  constructor
  · rintro ⟨hn, h⟩
    obtain ⟨h1, h2⟩ := reaches_to n C (w - n) g h
    have hw' : n + (w - n) = w := by omega
    rw [hw'] at h2
    exact ⟨hn, h1, h2⟩
  · rintro ⟨hn, hg, h⟩
    refine ⟨hn, ?_⟩
    clear hn
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have he : n + g - n = g := by omega
      rw [he, orSets_iff n C g g hg]
      exact Or.inl rfl
    | head h1 h2 ih =>
      rename_i u c
      have hle := orR_le n C hA _ _ h2
      have hlt := orStep_lt n C hA _ _ h1
      obtain ⟨k, rfl, hk, hop, hin⟩ := h1
      have he : n + k - n = k := by omega
      rw [he, orSets_iff n C g k hk]
      exact Or.inr ⟨hop, c, hin, by omega, hlt, ih⟩

lemma orIn_iff (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C w ↔ OrR n C w u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hin⟩)
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail ((orReaches_iff n C hA w k).mp hr).2.2 ⟨k, rfl, hk, hop, hin⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, h1, ⟨k, rfl, hk, hop, hin⟩⟩
    · exact Or.inl h1
    · have hle := orR_le n C hA _ _ h1
      exact Or.inr ⟨k, hk, (orReaches_iff n C hA w k).mpr ⟨by omega, hk, h1⟩, hop, hin⟩

lemma ao_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h3 _ hmem)
  refine ⟨h1 _ hmem, a, b, hab, ?_, ?_⟩
  · exact h2 k hk a (by rw [hab]; simp)
  · exact h2 k hk b (by rw [hab]; simp)

theorem cone_count {α : Type*} [DecidableEq α] (n : ℕ) (S : ℕ → Finset α) (Rc : ℕ → ℕ → Prop)
    (h1 : ∀ w < n, (S w).card ≤ 1)
    (h2 : ∀ t, 2 ≤ (S (n + t)).card → ∃ p q, p < n + t ∧ q < n + t ∧ S (n + t) ⊆ S p ∪ S q ∧
      Rc (n + t) t ∧ ∀ g, Rc p g ∨ Rc q g → Rc (n + t) g) :
    ∀ t (W : Finset ℕ), (∀ w ∈ W, w < n + t) → ∀ R : Finset ℕ,
      (∀ g < t, 2 ≤ (S (n + g)).card → (∃ w ∈ W, Rc w g) → g ∈ R) →
      (W.biUnion S).card ≤ R.card + W.card := by
  intro t
  induction t with
  | zero =>
    intro W hW R _
    have e1 : (W.biUnion S).card ≤ ∑ w ∈ W, (S w).card := Finset.card_biUnion_le
    have e2 : ∑ w ∈ W, (S w).card ≤ ∑ w ∈ W, 1 :=
      Finset.sum_le_sum (fun w hw => h1 w (by have := hW w hw; omega))
    have e3 : ∑ w ∈ W, 1 = W.card := by simp
    omega
  | succ t ih =>
    intro W hW R hR
    by_cases hmem : n + t ∈ W
    · have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, hmem⟩
      have e3 := Finset.card_erase_of_mem hmem
      by_cases hc : 2 ≤ (S (n + t)).card
      · obtain ⟨p, q, hp, hq, hsub, hself, hreach⟩ := h2 t hc
        have htR : t ∈ R := hR t (by omega) hc ⟨n + t, hmem, hself⟩
        have hW2 : ∀ w ∈ insert p (insert q (W.erase (n + t))), w < n + t := by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_erase] at hw
          rcases hw with rfl | rfl | ⟨hne, hw⟩
          · exact hp
          · exact hq
          · have := hW w hw
            omega
        have hR2 : ∀ g < t, 2 ≤ (S (n + g)).card →
            (∃ w ∈ insert p (insert q (W.erase (n + t))), Rc w g) → g ∈ R.erase t := by
          intro g hg hcg hex
          obtain ⟨w, hw, hr⟩ := hex
          rw [Finset.mem_erase]
          refine ⟨by omega, hR g (by omega) hcg ?_⟩
          simp only [Finset.mem_insert, Finset.mem_erase] at hw
          rcases hw with rfl | rfl | ⟨hne, hw⟩
          · exact ⟨n + t, hmem, hreach g (Or.inl hr)⟩
          · exact ⟨n + t, hmem, hreach g (Or.inr hr)⟩
          · exact ⟨w, hw, hr⟩
        have key := ih (insert p (insert q (W.erase (n + t)))) hW2 (R.erase t) hR2
        have hU : W.biUnion S ⊆ (insert p (insert q (W.erase (n + t)))).biUnion S := by
          intro x hx
          rw [Finset.mem_biUnion] at hx ⊢
          obtain ⟨w, hw, hxw⟩ := hx
          by_cases hwt : w = n + t
          · subst hwt
            rcases Finset.mem_union.mp (hsub hxw) with h | h
            · exact ⟨p, by simp, h⟩
            · exact ⟨q, by simp, h⟩
          · exact ⟨w, by simp [hwt, hw], hxw⟩
        have e1 := Finset.card_insert_le p (insert q (W.erase (n + t)))
        have e2 := Finset.card_insert_le q (W.erase (n + t))
        have hc2 : (R.erase t).card + 1 = R.card := Finset.card_erase_add_one htR
        have e4 := Finset.card_le_card hU
        omega
      · have hW2 : ∀ w ∈ W.erase (n + t), w < n + t := by
          intro w hw
          have h5 := hW w (Finset.mem_of_mem_erase hw)
          have h6 := Finset.ne_of_mem_erase hw
          omega
        have hR2 : ∀ g < t, 2 ≤ (S (n + g)).card → (∃ w ∈ W.erase (n + t), Rc w g) → g ∈ R := by
          intro g hg hcg hex
          obtain ⟨w, hw, hr⟩ := hex
          exact hR g (by omega) hcg ⟨w, Finset.mem_of_mem_erase hw, hr⟩
        have key := ih (W.erase (n + t)) hW2 R hR2
        have hU : W.biUnion S ⊆ (W.erase (n + t)).biUnion S ∪ S (n + t) := by
          intro x hx
          rw [Finset.mem_biUnion] at hx
          obtain ⟨w, hw, hxw⟩ := hx
          rw [Finset.mem_union, Finset.mem_biUnion]
          by_cases hwt : w = n + t
          · subst hwt
            exact Or.inr hxw
          · exact Or.inl ⟨w, Finset.mem_erase.mpr ⟨hwt, hw⟩, hxw⟩
        have e4 := Finset.card_le_card hU
        have e5 := Finset.card_union_le ((W.erase (n + t)).biUnion S) (S (n + t))
        omega
    · have hW2 : ∀ w ∈ W, w < n + t := by
        intro w hw
        have h5 := hW w hw
        have h6 : w ≠ n + t := fun h => hmem (h ▸ hw)
        omega
      exact ih W hW2 R (fun g hg hcg hex => hR g (by omega) hcg hex)

lemma orIn_small (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h : ∀ u : Fin n, u ∈ PEqualNP.TopForm.orIn n C w → u.val = w := by
    intro u hu
    rcases Relation.ReflTransGen.cases_head ((orIn_iff n C hA w u).mp hu) with h | ⟨c, ⟨k, hk, _⟩, _⟩
    · exact h.symm
    · omega
  exact Fin.ext ((h a ha).trans (h b hb).symm)

lemma orIn_big (n : ℕ) (C : Circuit) (hA : AO n C) (t : ℕ)
    (hc : 2 ≤ (PEqualNP.TopForm.orIn n C (n + t)).card) :
    t < C.gates.length ∧ (gateAt C t).op = GateOp.or ∧ ∃ p q, p < n + t ∧ q < n + t ∧
      PEqualNP.TopForm.orIn n C (n + t) ⊆
        PEqualNP.TopForm.orIn n C p ∪ PEqualNP.TopForm.orIn n C q ∧
      PEqualNP.CleanedNonEdge.OrReaches n C (n + t) t ∧
      ∀ g, PEqualNP.CleanedNonEdge.OrReaches n C p g ∨ PEqualNP.CleanedNonEdge.OrReaches n C q g →
        PEqualNP.CleanedNonEdge.OrReaches n C (n + t) g := by
  obtain ⟨u, hu⟩ : (PEqualNP.TopForm.orIn n C (n + t)).Nonempty := Finset.card_pos.mp (by omega)
  have hstep : ∀ v : Fin n, OrR n C (n + t) v.val →
      ∃ c, OrStep n C (n + t) c ∧ OrR n C c v.val := by
    intro v hv
    rcases Relation.ReflTransGen.cases_head hv with h | h
    · have := v.isLt
      omega
    · exact h
  obtain ⟨c0, ⟨k, hk, hklen, hop, hin0⟩, _⟩ := hstep u ((orIn_iff n C hA _ u).mp hu)
  have hkt : k = t := by omega
  rw [hkt] at hklen hop
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA t hklen
  refine ⟨hklen, hop, a, b, ha, hb, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨c, ⟨k2, hk2, _, _, hin⟩, hr⟩ := hstep v ((orIn_iff n C hA _ v).mp hv)
    have hk2t : k2 = t := by omega
    rw [hk2t, hab] at hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rw [Finset.mem_union]
    rcases hin with rfl | rfl
    · exact Or.inl ((orIn_iff n C hA _ v).mpr hr)
    · exact Or.inr ((orIn_iff n C hA _ v).mpr hr)
  · exact (orReaches_iff n C hA _ _).mpr ⟨by omega, hklen, Relation.ReflTransGen.refl⟩
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨_, hgl, hr⟩ := (orReaches_iff n C hA _ _).mp hg
      exact (orReaches_iff n C hA _ _).mpr ⟨by omega, hgl,
        Relation.ReflTransGen.head ⟨t, rfl, hklen, hop, by rw [hab]; simp⟩ hr⟩
    · obtain ⟨_, hgl, hr⟩ := (orReaches_iff n C hA _ _).mp hg
      exact (orReaches_iff n C hA _ _).mpr ⟨by omega, hgl,
        Relation.ReflTransGen.head ⟨t, rfl, hklen, hop, by rw [hab]; simp⟩ hr⟩

lemma orIn_sub (n : ℕ) (C : Circuit) (hA : AO n C) (w g : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C w g) :
    PEqualNP.TopForm.orIn n C (n + g) ⊆ PEqualNP.TopForm.orIn n C w := by
  intro u hu
  obtain ⟨_, _, hr⟩ := (orReaches_iff n C hA w g).mp h
  exact (orIn_iff n C hA w u).mpr
    (Relation.ReflTransGen.trans hr ((orIn_iff n C hA _ u).mp hu))

lemma out_true (n : ℕ) (C : Circuit) (hA : AO n C) (i : ℕ) (b : Fin n)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C C.output i)
    (hb : b ∈ PEqualNP.TopForm.orIn n C (n + i)) :
    PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = b)) = true := by
  have h1 := orIn_sub n C hA _ _ hr hb
  have h2 := (orIn_iff n C hA _ b).mp h1
  have h3 := orR_mono n C hA (fun k1 => decide (k1 = b)) _ _ h2
    (by rw [W_input n C _ b.val b.isLt]; simp)
  exact h3

theorem part2 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (F : Finset ℕ)
    (ctr : ℕ → Fin n) (lf : ℕ → ℕ) (hN : PEqualNP.TopForm.NoFourCycle G)
    (hI : PEqualNP.TopForm.IsAO2 n C)
    (hlf : ∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b)
    (U : Fin n → Finset (Fin n))
    (hU : ∀ c b, b ∈ U c → ∃ j ∈ F, ctr j = c ∧ b ∈ PEqualNP.TopForm.orIn n C (lf j)) :
    ∑ c : Fin n, (U c).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧
      (gateAt C i2).op = GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧
      ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  classical
  have hA := ao_of n C hI
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
    have hcc := cone_count n (PEqualNP.TopForm.orIn n C) (PEqualNP.CleanedNonEdge.OrReaches n C)
      (fun w hw => orIn_small n C hA w hw)
      (fun t hc => (orIn_big n C hA t hc).2.2) T
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
      have h5 := hlf j hjF b (orIn_sub n C hA _ _ hr hb)
      have h6 := hlf j2 hjF2 b (orIn_sub n C hA _ _ hr2 hb)
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
      obtain ⟨hl, hop, _⟩ := orIn_big n C hA g hcg
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


end P2234

theorem s2234 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  intro n G _ C F ctr lf hN hI h1 hlf
  refine ⟨fun i _ _ hc _ hout => ?_, ?_⟩
  · obtain ⟨b, hb⟩ : (PEqualNP.TopForm.orIn n C (n + i)).Nonempty :=
      Finset.card_pos.mp (by omega)
    exact Bool.false_ne_true ((h1 b).symm.trans
      (PEqualNP.Outside.L_meta_2239.P2234.out_true n C (PEqualNP.Outside.L_meta_2239.P2234.ao_of n C hI) i b hout hb))
  · exact PEqualNP.Outside.L_meta_2239.P2234.part2 n G C F ctr lf hN hI hlf _
      (fun c b hb => (Finset.mem_filter.mp hb).2)

end Sec2234

section SecAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem and_ne_or : GateOp.and ≠ GateOp.or := by
  intro h
  cases h

theorem count3 (len : ℕ) (F : Finset ℕ) (O S : Set ℕ) (hF : ∀ j ∈ F, j < len)
    (hO : ∀ i ∈ O, i < len) (hS : ∀ i ∈ S, i < len) (hFO : ∀ j ∈ F, j ∉ O)
    (hFS : ∀ j ∈ F, j ∉ S) (hOS : ∀ i ∈ O, i ∉ S) : F.card + O.ncard + S.ncard ≤ len := by
  have hOf : O.Finite := (Finset.finite_toSet (Finset.range len)).subset
    (fun i hi => Finset.mem_coe.mpr (Finset.mem_range.mpr (hO i hi)))
  have hSf : S.Finite := (Finset.finite_toSet (Finset.range len)).subset
    (fun i hi => Finset.mem_coe.mpr (Finset.mem_range.mpr (hS i hi)))
  have hFf : (↑F : Set ℕ).Finite := Finset.finite_toSet F
  have d1 : Disjoint (↑F : Set ℕ) O :=
    Set.disjoint_left.mpr (fun a ha => hFO a (Finset.mem_coe.mp ha))
  have d2 : Disjoint ((↑F : Set ℕ) ∪ O) S := by
    refine Set.disjoint_left.mpr ?_
    rintro a (ha | ha)
    · exact hFS a (Finset.mem_coe.mp ha)
    · exact hOS a ha
  have e1 : ((↑F : Set ℕ) ∪ O).ncard = F.card + O.ncard := by
    rw [Set.ncard_union_eq d1 hFf hOf, Set.ncard_coe_finset]
  have e2 : (((↑F : Set ℕ) ∪ O) ∪ S).ncard = F.card + O.ncard + S.ncard := by
    rw [Set.ncard_union_eq d2 (hFf.union hOf) hSf, e1]
  have e3 : (((↑F : Set ℕ) ∪ O) ∪ S).ncard ≤ (↑(Finset.range len) : Set ℕ).ncard := by
    refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
    rintro a ((ha | ha) | ha)
    · exact Finset.mem_coe.mpr (Finset.mem_range.mpr (hF a (Finset.mem_coe.mp ha)))
    · exact Finset.mem_coe.mpr (Finset.mem_range.mpr (hO a ha))
    · exact Finset.mem_coe.mpr (Finset.mem_range.mpr (hS a ha))
  rw [Set.ncard_coe_finset, Finset.card_range] at e3
  omega

theorem arith (e t f o s len : ℕ) (h1 : t ≤ f) (h2 : f ≤ o + 1) (h3 : e ≤ s + f)
    (h4 : f + o + s ≤ len) : e + t ≤ len + 1 := by
  omega

theorem assemble {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (E1 : Finset (Fin n × Fin n))
    (hlt : ∀ e ∈ E1, e.1 < e.2)
    (hw : ∀ e ∈ E1, ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j ∧
      ((e.1 ∈ side (n := n) C j 0 ∧ e.2 ∈ side (n := n) C j 1) ∨
       (e.2 ∈ side (n := n) C j 0 ∧ e.1 ∈ side (n := n) C j 1)))
    (hp1 : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → OrReaches n C C.output j →
      (∀ w : Fin n, w ∈ side (n := n) C j 0 → w ∉ side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 → G.Adj u v) ∧
      ((side (n := n) C j 0).card ≤ 1 ∨ (side (n := n) C j 1).card ≤ 1))
    (hp2 : ∀ F : Finset ℕ, (∀ e ∈ E1, ∃ i ∈ F, i < C.gates.length ∧ (gateAt C i).op = GateOp.and ∧
      OrReaches n C C.output i ∧ ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
       (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1))) →
      ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ E1, e3.1 ∈ T ∨ e3.2 ∈ T)
    (h33 : ∀ F : Finset ℕ, (∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j) →
      F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i} + 1)
    (h34 : ∀ (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ),
      (∀ j ∈ F, ∀ b : Fin n, b ∈ orIn n C (lf j) → G.Adj (ctr j) b) →
      (∀ i < C.gates.length, (gateAt C i).op = GateOp.or → 2 ≤ (orIn n C (n + i)).card →
        (∃ j1 ∈ F, OrReaches n C (lf j1) i) → ¬ OrReaches n C C.output i) ∧
      ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧
          b2 ∈ orIn n C (lf j2))).card ≤
        Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
          2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} + F.card) :
    ∃ T : Finset (Fin n), (∀ e ∈ E1, e.1 ∈ T ∨ e.2 ∈ T) ∧ E1.card + T.card ≤ C.size + 1 := by
  by_cases hE : E1 = ∅
  · subst hE
    exact ⟨∅, fun e he => absurd he (Finset.notMem_empty e), by simp⟩
  obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  haveI : Nonempty (Fin n) := ⟨e0.1⟩
  haveI : Nonempty (Σ _ : Fin n, Fin n) := ⟨⟨e0.1, e0.1⟩⟩
  choose! w hw using hw
  have hFprop : ∀ j ∈ E1.image w, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨(hw e he).1, (hw e he).2.1, (hw e he).2.2.1⟩
  obtain ⟨T, hTF, hTcov⟩ := hp2 (E1.image w) (fun e he =>
    ⟨w e, Finset.mem_image_of_mem w he, (hw e he).1, (hw e he).2.1, (hw e he).2.2.1,
      (hw e he).2.2.2⟩)
  have h3 := h33 (E1.image w) hFprop
  have hdata : ∀ j ∈ E1.image w, ∃ (c : Fin n) (l : ℕ),
      (∀ v : Fin n, v ∈ orIn n C l → G.Adj c v) ∧
      (∀ e ∈ E1, w e = j → (e.1 = c ∧ e.2 ∈ orIn n C l) ∨ (e.2 = c ∧ e.1 ∈ orIn n C l)) := by
    intro j hj
    obtain ⟨e1, he1, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hlen, hand, hor, hcr⟩ := hw e1 he1
    obtain ⟨-, hadj, hsmall⟩ := hp1 (w e1) hlen hand hor
    rcases hsmall with hs | hs
    · have hc : ∃ c : Fin n, c ∈ side (n := n) C (w e1) 0 := by
        rcases hcr with h | h
        · exact ⟨_, h.1⟩
        · exact ⟨_, h.1⟩
      obtain ⟨c, hc⟩ := hc
      have huniq : ∀ x : Fin n, x ∈ side (n := n) C (w e1) 0 → x = c :=
        fun x hx => Finset.card_le_one.mp hs x hx c hc
      refine ⟨c, opnd C (w e1) 1, fun v hv => hadj c hc v hv, ?_⟩
      intro e he hwe
      rcases (hw e he).2.2.2 with h | h
      · rw [hwe] at h
        exact Or.inl ⟨huniq _ h.1, h.2⟩
      · rw [hwe] at h
        exact Or.inr ⟨huniq _ h.1, h.2⟩
    · have hc : ∃ c : Fin n, c ∈ side (n := n) C (w e1) 1 := by
        rcases hcr with h | h
        · exact ⟨_, h.2⟩
        · exact ⟨_, h.2⟩
      obtain ⟨c, hc⟩ := hc
      have huniq : ∀ x : Fin n, x ∈ side (n := n) C (w e1) 1 → x = c :=
        fun x hx => Finset.card_le_one.mp hs x hx c hc
      refine ⟨c, opnd C (w e1) 0, fun v hv => (hadj v hv c hc).symm, ?_⟩
      intro e he hwe
      rcases (hw e he).2.2.2 with h | h
      · rw [hwe] at h
        exact Or.inr ⟨huniq _ h.2, h.1⟩
      · rw [hwe] at h
        exact Or.inl ⟨huniq _ h.2, h.1⟩
  choose! ctr lf hctr hcross using hdata
  obtain ⟨hA4, hB4⟩ := h34 (E1.image w) ctr lf hctr
  have hd : ∀ e ∈ E1, ∃ p : (Σ _ : Fin n, Fin n),
      p ∈ (Finset.univ : Finset (Fin n)).sigma (fun c => Finset.univ.filter (fun b2 : Fin n =>
        ∃ j2 ∈ E1.image w, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))) ∧
      ((p.1 = e.1 ∧ p.2 = e.2) ∨ (p.1 = e.2 ∧ p.2 = e.1)) := by
    intro e he
    have hj := Finset.mem_image_of_mem w he
    rcases hcross (w e) hj e he rfl with h | h
    · refine ⟨⟨e.1, e.2⟩, ?_, Or.inl ⟨rfl, rfl⟩⟩
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, w e, hj, h.1.symm, h.2⟩⟩
    · refine ⟨⟨e.2, e.1⟩, ?_, Or.inr ⟨rfl, rfl⟩⟩
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, w e, hj, h.1.symm, h.2⟩⟩
  choose! d hd1 hd2 using hd
  have hinj : Set.InjOn d (↑E1 : Set (Fin n × Fin n)) := by
    intro e he f hf hee
    have hl := hlt e (Finset.mem_coe.mp he)
    have hm := hlt f (Finset.mem_coe.mp hf)
    have q1 : (d e).1 = (d f).1 := by rw [hee]
    have q2 : (d e).2 = (d f).2 := by rw [hee]
    rcases hd2 e (Finset.mem_coe.mp he) with h | h <;>
      rcases hd2 f (Finset.mem_coe.mp hf) with k | k
    · exact Prod.ext (h.1.symm.trans (q1.trans k.1)) (h.2.symm.trans (q2.trans k.2))
    · exfalso
      have a1 : e.1 = f.2 := h.1.symm.trans (q1.trans k.1)
      have a2 : e.2 = f.1 := h.2.symm.trans (q2.trans k.2)
      rw [a1, a2] at hl
      exact lt_asymm hl hm
    · exfalso
      have a1 : e.2 = f.1 := h.1.symm.trans (q1.trans k.1)
      have a2 : e.1 = f.2 := h.2.symm.trans (q2.trans k.2)
      rw [a1, a2] at hl
      exact lt_asymm hl hm
    · exact Prod.ext (h.2.symm.trans (q2.trans k.2)) (h.1.symm.trans (q1.trans k.1))
  have hcardE : E1.card ≤ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n =>
      ∃ j2 ∈ E1.image w, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))).card := by
    rw [← Finset.card_sigma]
    exact Finset.card_le_card_of_injOn d (fun a ha => hd1 a (Finset.mem_coe.mp ha)) hinj
  have hsz : (E1.image w).card +
      Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i} +
      Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
          2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ E1.image w, OrReaches n C (lf j3) i2}
      ≤ C.gates.length := by
    refine count3 _ _ _ _ (fun j hj => (hFprop j hj).1) (fun i hi => hi.1) (fun i hi => hi.1)
      ?_ ?_ ?_
    · intro j hj hjo
      exact and_ne_or ((hFprop j hj).2.1.symm.trans hjo.2.1)
    · intro j hj hjs
      exact and_ne_or ((hFprop j hj).2.1.symm.trans hjs.2.1)
    · intro i hio his
      exact hA4 i his.1 his.2.1 his.2.2.1 his.2.2.2 hio.2.2
  exact ⟨T, hTcov, arith _ _ _ _ _ _ hTF h3 (hcardE.trans hB4) hsz⟩

end SecAsm

theorem core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → ∃ T : Finset (Fin n), (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), e.1 ∈ T ∨ e.2 ∈ T) ∧ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 hA h1 h2
  exact assemble G C _ (fun e he => (Finset.mem_filter.mp he).2.1)
    (fun e he => s2230 n C e.1 e.2 hA h1 (Finset.mem_filter.mp he).2.1
      (Finset.mem_filter.mp he).2.2.2)
    (s2231 n G C h4 hA h1 h2).1 (s2231 n G C h4 hA h1 h2).2
    (fun F hF => s2233 n C F hA hF)
    (fun F ctr lf h => s2234 n G C F ctr lf h4 hA h1 h)

theorem setList_pair {n : ℕ} (a b : Fin n) (h : a < b) :
    PEqualNP.ReadK.setList ({a, b} : Finset (Fin n)) = [a.val, b.val] := by
  unfold PEqualNP.ReadK.setList
  have h1 : (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) = [a, b] := by
    apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
    · exact ((List.sortedLT_finRange n).pairwise).filter _
    · simp [h]
    · intro x
      simp
  rw [h1]; rfl

theorem prime_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hf : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x
      = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    (a b : Fin n) (hab : G.Adj a b) :
    PEqualNP.ReadK.IsPrimeImplicant n C ({a, b} : Finset (Fin n)) := by
  constructor
  · rw [hf]
    simp only [decide_eq_true_eq]
    exact ⟨a, b, hab, by simp [PEqualNP.ReadK.setInput], by simp [PEqualNP.ReadK.setInput]⟩
  · intro T hT
    rw [hf]
    simp only [decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    have hu' : u ∈ T := by simpa [PEqualNP.ReadK.setInput] using hu
    have hv' : v ∈ T := by simpa [PEqualNP.ReadK.setInput] using hv
    rw [Finset.mem_ssubsets] at hT
    have hu2 := hT.1 hu'
    have hv2 := hT.1 hv'
    have hne : u ≠ v := G.ne_of_adj huv
    apply hT.2
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu2 hv2 hz
    rcases hu2 with hu2 | hu2 <;> rcases hv2 with hv2 | hv2 <;> rcases hz with hz | hz
    all_goals first
      | exact absurd (hu2.trans hv2.symm) hne
      | (rw [hz, ← hu2]; exact hu')
      | (rw [hz, ← hv2]; exact hv')

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → PEqualNP.ReadK.IsReadK n C 1 → ∃ T : Finset (Fin n), (∀ u2 v2 : Fin n, G.Adj u2 v2 → u2 ∈ T ∨ v2 ∈ T) ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 hao hf hr
  have h1 : ∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false := by
    intro a1
    rw [hf]
    simp only [decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [decide_eq_true_eq] at hu hv
    exact G.ne_of_adj huv (hu.trans hv.symm)
  have h2 : ∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 →
      PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false := by
    intro a2 b2 _ hnab
    rw [hf]
    simp only [decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [decide_eq_true_eq] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact G.ne_of_adj huv (hu.trans hv.symm)
    · rw [hu, hv] at huv
      exact hnab huv
    · rw [hu, hv] at huv
      exact hnab (huv.symm)
    · exact G.ne_of_adj huv (hu.trans hv.symm)
  obtain ⟨T, hT, hcard⟩ := core n G C h4 hao h1 h2
  have hall : ∀ u v : Fin n, u < v → G.Adj u v →
      PEqualNP.ReadK.readsAtMost C n [u.val, v.val] 1 = true := by
    intro u v huv hadj
    have h3 := hr _ (prime_pair G C hf u v hadj)
    rwa [setList_pair u v huv] at h3
  refine ⟨T, ?_, ?_⟩
  · intro u v hadj
    rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with h | h
    · exact hT (u, v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hadj, hall u v h hadj⟩)
    · exact (hT (v, u) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, h, hadj.symm, hall v u h (hadj.symm)⟩)).symm
  · have hsub : G.edgeFinset ⊆ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).image (fun e : Fin n × Fin n => s(e.1, e.2)) := by
      intro e
      refine Sym2.ind (fun u v he => ?_) e
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rw [Finset.mem_image]
      rcases lt_or_gt_of_ne (G.ne_of_adj he) with h | h
      · exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, he, hall u v h he⟩, rfl⟩
      · exact ⟨(v, u), Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, h, he.symm, hall v u h (he.symm)⟩, Sym2.eq_swap⟩
    have hle := (Finset.card_le_card hsub).trans Finset.card_image_le
    exact (Nat.add_le_add_right hle _).trans hcard

namespace Own

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

theorem ofFn_getD {α : Type} {n : ℕ} (x : Fin n → α) (dflt : α) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i dflt = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

def F {α : Type} (step : Gate → List α → α) (gs : List Gate) (d : List α) : List α :=
  gs.foldl (fun d g => d ++ [step g d]) d

theorem F_append {α : Type} (step : Gate → List α → α) (a b : List Gate) (d : List α) :
    F step (a ++ b) d = F step b (F step a d) := by
  simp [F, List.foldl_append]

def chain : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | acc, w, i :: is => ⟨GateOp.or, [acc, i]⟩ :: chain w (w + 1) is

def cfin : ℕ → ℕ → List ℕ → ℕ
  | acc, _, [] => acc
  | _, w, _ :: is => cfin w (w + 1) is

theorem chain_len : ∀ (ins : List ℕ) (acc w : ℕ), (chain acc w ins).length = ins.length
  | [], _, _ => rfl
  | _ :: is, _, w => by simp [chain, chain_len is]

theorem chain_or : ∀ (ins : List ℕ) (acc w : ℕ), ∀ g ∈ chain acc w ins,
    g.op = GateOp.or ∧ g.inputs.length = 2
  | [], _, _ => by simp [chain]
  | i :: is, acc, w => by
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, rfl⟩
    · exact chain_or is w (w + 1) g hg

theorem chain_spec {α : Type} (step : Gate → List α → α) (dflt : α) (op : α → α → α)
    (hstep : ∀ (a b : ℕ) (d : List α),
      step ⟨GateOp.or, [a, b]⟩ d = op (d.getD a dflt) (d.getD b dflt))
    (ins : List ℕ) : ∀ (acc w : ℕ) (d : List α), d.length = w → acc < w → (∀ i ∈ ins, i < w) →
      (F step (chain acc w ins) d).length = w + ins.length ∧
      (∀ i < w, (F step (chain acc w ins) d).getD i dflt = d.getD i dflt) ∧
      (F step (chain acc w ins) d).getD (cfin acc w ins) dflt =
        ins.foldl (fun v i => op v (d.getD i dflt)) (d.getD acc dflt) ∧
      cfin acc w ins < w + ins.length := by
  induction ins with
  | nil =>
    intro acc w d hw hacc _
    refine ⟨by simp [chain, F, hw], fun i _ => by simp [chain, F], by simp [chain, F, cfin],
      by simpa [cfin] using hacc⟩
  | cons i is ih =>
    intro acc w d hw hacc hins
    have hi : i < w := hins i (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := ih w (w + 1) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d])
      (by simp [hw]) (by omega) (fun k hk => by have := hins k (by simp [hk]); omega)
    have hF : F step (chain acc w (i :: is)) d =
        F step (chain w (w + 1) is) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]) := by
      simp [F, chain]
    have hpre : ∀ k < w, (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD k dflt = d.getD k dflt :=
      fun k hk => List.getD_append _ _ _ _ (by omega)
    have hd : (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD w dflt =
        op (d.getD acc dflt) (d.getD i dflt) := by
      rw [List.getD_append_right _ _ _ _ (by omega), hstep]
      simp [hw]
    have hc : cfin acc w (i :: is) = cfin w (w + 1) is := by simp [cfin]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hF, h1]; simp only [List.length_cons]; omega
    · intro k hk; rw [hF, h2 k (by omega), hpre k hk]
    · rw [hF, hc, h3, hd, List.foldl_cons]
      exact List.foldl_ext _ _ _ (fun v k hk => by rw [hpre k (hins k (by simp [hk]))])
    · rw [hc]; simp only [List.length_cons]; omega

def wstep (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wstep_or (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.or, [a, b]⟩ d = (d.getD a false || d.getD b false) := by
  simp [wstep, GateOp.eval]

theorem wstep_and (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.and, [a, b]⟩ d = (d.getD a false && d.getD b false) := by
  simp [wstep, GateOp.eval]

theorem foldl_or (f : ℕ → Bool) : ∀ (l : List ℕ) (a : Bool),
    l.foldl (fun v i => v || f i) a = (a || l.any f)
  | [], a => by simp
  | i :: is, a => by simp [foldl_or f is, Bool.or_assoc]

theorem F_one {α : Type} (step : Gate → List α → α) (g : Gate) (d : List α) :
    F step [g] d = d ++ [step g d] := rfl

theorem F_len {α : Type} (step : Gate → List α → α) : ∀ (gs : List Gate) (d : List α),
    (F step gs d).length = d.length + gs.length
  | [], d => by simp [F]
  | g :: gs, d => by
    have h := F_len step gs (d ++ [step g d])
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem F_pre {α : Type} (step : Gate → List α → α) (dflt : α) :
    ∀ (gs : List Gate) (d : List α) (i : ℕ), i < d.length →
      (F step gs d).getD i dflt = d.getD i dflt
  | [], _, _, _ => rfl
  | g :: gs, d, i, hi => by
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, F_pre step dflt gs (d ++ [step g d]) i (by rw [List.length_append]; omega)]
    exact List.getD_append _ _ _ _ hi

def blk (c h : ℕ) (t : List ℕ) (w : ℕ) : List Gate :=
  chain h w t ++ [⟨GateOp.and, [cfin h w t, c]⟩]

theorem blk_len (c h : ℕ) (t : List ℕ) (w : ℕ) : (blk c h t w).length = t.length + 1 := by
  simp [blk, chain_len]

theorem blk_shape (c h : ℕ) (t : List ℕ) (w : ℕ) :
    ∀ g ∈ blk c h t w, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  unfold blk at hg
  rw [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · obtain ⟨a, b⟩ := chain_or _ _ _ g hg
    exact ⟨Or.inr a, b⟩
  · exact ⟨Or.inl rfl, rfl⟩

theorem blk_val (c h : ℕ) (t : List ℕ) (w : ℕ) (d : List Bool)
    (hw : d.length = w) (h1 : h < w) (h2 : ∀ i ∈ t, i < w) (h3 : c < w) :
    (F wstep (blk c h t w) d).getD (w + t.length) false =
      ((d.getD h false || t.any fun i => d.getD i false) && d.getD c false) := by
  obtain ⟨c1, c2, c3, c4⟩ :=
    chain_spec wstep false (fun u v => u || v) wstep_or t h w d hw h1 h2
  unfold blk
  rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq c1), c1, Nat.sub_self,
    List.getD_cons_zero, wstep_and, c3, c2 _ h3, foldl_or (fun i => d.getD i false)]

theorem blk_iff (n c h : ℕ) (t : List ℕ) (w : ℕ) (d x : List Bool)
    (hw : d.length = w) (hpre : ∀ i < n, d.getD i false = x.getD i false)
    (h1 : h < n) (h2 : ∀ i ∈ t, i < n) (hl : c < n) (hNw : n ≤ w) :
    (F wstep (blk c h t w) d).getD (w + t.length) false = true ↔
      (x.getD c false = true ∧ ∃ i ∈ h :: t, x.getD i false = true) := by
  rw [blk_val c h t w d hw (by omega) (fun i hi => by have := h2 i hi; omega) (by omega),
    Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, hpre h (by omega),
    hpre c (by omega)]
  constructor
  · rintro ⟨hh | ⟨i, hi, hh⟩, hy⟩
    · exact ⟨hy, h, by simp, hh⟩
    · exact ⟨hy, i, by simp [hi], by rw [← hpre i (h2 i hi)]; exact hh⟩
  · rintro ⟨hy, i, hi, hh⟩
    refine ⟨?_, hy⟩
    rcases List.mem_cons.mp hi with e | hi2
    · rw [e] at hh; exact Or.inl hh
    · exact Or.inr ⟨i, hi2, by rw [hpre i (h2 i hi2)]; exact hh⟩

def G (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : List (ℕ × ℕ × List ℕ) → List Gate
  | [] => blk s0.1 s0.2.1 s0.2.2 n
  | s :: r => G n s0 r ++ blk s.1 s.2.1 s.2.2 (n + (G n s0 r).length) ++
      [⟨GateOp.or, [n + (G n s0 r).length - 1, n + (G n s0 r).length + s.2.2.length]⟩]

theorem G_pos (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r, 0 < (G n s0 r).length
  | [] => by simp [G, blk_len]
  | s :: r => by simp [G]

theorem G_len (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r : List (ℕ × ℕ × List ℕ),
    (G n s0 r).length + 1 = (s0.2.2.length + 2) + (r.map fun s => s.2.2.length + 2).sum
  | [] => by simp [G, blk_len]
  | s :: r => by
    have ih := G_len n s0 r
    simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil,
      List.map_cons, List.sum_cons]
    omega

theorem G_shape (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r : List (ℕ × ℕ × List ℕ),
    ∀ g ∈ G n s0 r, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  | [] => by
    intro g hg
    simp only [G] at hg
    exact blk_shape _ _ _ _ g hg
  | s :: r => by
    intro g hg
    simp only [G, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact G_shape n s0 r g hg
    · exact blk_shape _ _ _ _ g hg
    · exact ⟨Or.inr rfl, rfl⟩

theorem G_val (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (x : List Bool) (hx : x.length = n)
    (h0 : s0.1 < n ∧ ∀ i ∈ s0.2.1 :: s0.2.2, i < n) :
    ∀ r : List (ℕ × ℕ × List ℕ), (∀ s ∈ r, s.1 < n ∧ ∀ i ∈ s.2.1 :: s.2.2, i < n) →
      ((F wstep (G n s0 r) x).getD (n + (G n s0 r).length - 1) false = true ↔
        ∃ s ∈ s0 :: r, x.getD s.1 false = true ∧ ∃ i ∈ s.2.1 :: s.2.2, x.getD i false = true)
  | [], _ => by
    have e : n + (G n s0 []).length - 1 = n + s0.2.2.length := by
      simp only [G, blk_len]
      omega
    rw [e]
    simp only [G]
    rw [blk_iff n s0.1 s0.2.1 s0.2.2 n x x hx (fun i _ => rfl) (h0.2 _ (by simp))
      (fun i hi => h0.2 i (by simp [hi])) h0.1 (le_refl _)]
    constructor
    · intro a
      exact ⟨s0, by simp, a⟩
    · rintro ⟨s, hs, a⟩
      rw [List.mem_singleton.mp hs] at a
      exact a
  | s :: r, hr => by
    have ih := G_val n s0 x hx h0 r (fun s' hs' => hr s' (by simp [hs']))
    have hs := hr s (by simp)
    have hL : (F wstep (G n s0 r) x).length = n + (G n s0 r).length := by
      rw [F_len, hx]
    have hpre : ∀ i < n, (F wstep (G n s0 r) x).getD i false = x.getD i false :=
      fun i hi => F_pre wstep false _ _ i (by omega)
    have hb := blk_iff n s.1 s.2.1 s.2.2 (n + (G n s0 r).length)
      (F wstep (G n s0 r) x) x hL hpre (hs.2 _ (by simp)) (fun i hi => hs.2 i (by simp [hi]))
      hs.1 (by omega)
    have hL2 : (F wstep (G n s0 r ++ blk s.1 s.2.1 s.2.2 (n + (G n s0 r).length))
        x).length = n + (G n s0 r).length + s.2.2.length + 1 := by
      rw [F_len, List.length_append, blk_len, hx]
      omega
    have hpos := G_pos n s0 r
    have e : n + (G n s0 (s :: r)).length - 1 =
        n + (G n s0 r).length + s.2.2.length + 1 := by
      simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil]
      omega
    rw [e]
    simp only [G]
    rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq hL2), hL2, Nat.sub_self,
      List.getD_cons_zero, wstep_or, Bool.or_eq_true]
    rw [F_append, F_pre wstep false _ _ (n + (G n s0 r).length - 1)
      (by rw [hL]; omega), ih, hb]
    constructor
    · rintro (⟨s', hs', a⟩ | a)
      · refine ⟨s', ?_, a⟩
        simp only [List.mem_cons] at hs' ⊢
        tauto
      · exact ⟨s, by simp, a⟩
    · rintro ⟨s', hs', a⟩
      simp only [List.mem_cons] at hs'
      rcases hs' with h | h | h
      · exact Or.inl ⟨s', by simp [h], a⟩
      · rw [h] at a
        exact Or.inr a
      · exact Or.inl ⟨s', by simp [h], a⟩

def RB (w : ℕ) (b : List Gate) : Prop :=
  ∀ j < b.length, ∀ i ∈ (b.getD j ⟨GateOp.or, []⟩).inputs, i < w + j

theorem RB_app (w : ℕ) (a b : List Gate) (ha : RB w a) (hb : RB (w + a.length) b) :
    RB w (a ++ b) := by
  intro j hj i hi
  rcases Nat.lt_or_ge j a.length with h | h
  · rw [List.getD_append _ _ _ _ h] at hi
    exact ha j h i hi
  · rw [List.getD_append_right _ _ _ _ h] at hi
    have hj2 : j - a.length < b.length := by
      rw [List.length_append] at hj; omega
    have := hb (j - a.length) hj2 i hi
    omega

theorem RB_two (w : ℕ) (op : GateOp) (a b : ℕ) (ha : a < w) (hb : b < w) :
    RB w [⟨op, [a, b]⟩] := by
  intro j hj i hi
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  have hi' : i ∈ [a, b] := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with hi' | hi' <;> omega

theorem cfin_lt : ∀ (ins : List ℕ) (acc w : ℕ), acc < w → cfin acc w ins < w + ins.length
  | [], acc, w, h => by simpa [cfin] using h
  | i :: is, acc, w, h => by
    have := cfin_lt is w (w + 1) (by omega)
    simp only [cfin, List.length_cons]
    omega

theorem RB_chain : ∀ (ins : List ℕ) (acc w : ℕ), acc < w → (∀ i ∈ ins, i < w) →
    RB w (chain acc w ins)
  | [], _, _, _, _ => by
    intro j hj
    simp [chain] at hj
  | i :: is, acc, w, hacc, hins => by
    have e : chain acc w (i :: is) = [⟨GateOp.or, [acc, i]⟩] ++ chain w (w + 1) is := rfl
    rw [e]
    apply RB_app
    · exact RB_two w GateOp.or acc i hacc (hins i (by simp))
    · exact RB_chain is w (w + 1) (by omega)
        (fun k hk => by have := hins k (by simp [hk]); omega)

theorem RB_blk (c h : ℕ) (t : List ℕ) (w : ℕ) (h1 : h < w) (h2 : ∀ i ∈ t, i < w)
    (h3 : c < w) : RB w (blk c h t w) := by
  unfold blk
  apply RB_app _ _ _ (RB_chain t h w h1 h2)
  rw [chain_len]
  exact RB_two _ GateOp.and _ _ (cfin_lt t h w h1) (by omega)

theorem RB_G (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (h0 : s0.1 < n ∧ ∀ i ∈ s0.2.1 :: s0.2.2, i < n) :
    ∀ r : List (ℕ × ℕ × List ℕ), (∀ s ∈ r, s.1 < n ∧ ∀ i ∈ s.2.1 :: s.2.2, i < n) →
      RB n (G n s0 r)
  | [], _ => by
    simp only [G]
    exact RB_blk _ _ _ _ (h0.2 _ (by simp)) (fun i hi => h0.2 i (by simp [hi])) h0.1
  | s :: r, hr => by
    have ih := RB_G n s0 h0 r (fun s' hs' => hr s' (by simp [hs']))
    have hs := hr s (by simp)
    have hpos := G_pos n s0 r
    simp only [G]
    apply RB_app
    · apply RB_app _ _ _ ih
      exact RB_blk _ _ _ _ (by have := hs.2 s.2.1 (by simp); omega)
        (fun i hi => by have := hs.2 i (by simp [hi]); omega) (by have := hs.1; omega)
    · rw [List.length_append, blk_len]
      exact RB_two _ GateOp.or _ _ (by omega) (by omega)

def rstep (S : List ℕ) (k : ℕ) (g : Gate) (R : List (List (List ℕ))) : List (List ℕ) :=
  match g.op with
  | GateOp.or =>
    (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

theorem rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = F (rstep S k) C.gates ((List.range n).map (leafVectors S k)) := rfl

theorem mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h1 | h1)
      · exact h1
      · rw [h1]; exact h
  · simp

theorem mem_foldl_insertNew (x : List ℕ) : ∀ (B A : List (List ℕ)),
    x ∈ B.foldl insertNew A ↔ x ∈ A ∨ x ∈ B
  | [], A => by simp
  | b :: B, A => by
    rw [List.foldl_cons, mem_foldl_insertNew x B, mem_insertNew, List.mem_cons]
    tauto

def orv (A B : List (List ℕ)) : List (List ℕ) := B.foldl insertNew (A.foldl insertNew [])

theorem mem_orv (x : List ℕ) (A B : List (List ℕ)) : x ∈ orv A B ↔ x ∈ A ∨ x ∈ B := by
  unfold orv
  rw [mem_foldl_insertNew, mem_foldl_insertNew]
  simp

theorem rstep_or (S : List ℕ) (k a b : ℕ) (R : List (List (List ℕ))) :
    rstep S k ⟨GateOp.or, [a, b]⟩ R = orv (R.getD a []) (R.getD b []) := rfl

theorem mem_andStep (k : ℕ) (x : List ℕ) (A B : List (List ℕ)) :
    x ∈ andStep k A B ↔ ∃ u ∈ A, ∃ v ∈ B, capAdd k u v = x := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp [List.mem_flatMap]

theorem rstep_and (S : List ℕ) (k a b : ℕ) (R : List (List (List ℕ))) :
    rstep S k ⟨GateOp.and, [a, b]⟩ R =
      andStep k (andStep k [S.map fun _ => 0] (R.getD a [])) (R.getD b []) := rfl

theorem foldl_orv (x : List ℕ) (g : ℕ → List (List ℕ)) : ∀ (l : List ℕ) (a : List (List ℕ)),
    (x ∈ a ∨ ∃ i ∈ l, x ∈ g i) → x ∈ l.foldl (fun v i => orv v (g i)) a
  | [], a, h => by
    rcases h with h | ⟨i, hi, _⟩
    · exact h
    · simp at hi
  | i :: is, a, h => by
    rw [List.foldl_cons]
    apply foldl_orv x g is
    rcases h with h | ⟨j, hj, hx⟩
    · exact Or.inl ((mem_orv _ _ _).mpr (Or.inl h))
    · rcases List.mem_cons.mp hj with e | hj2
      · rw [e] at hx
        exact Or.inl ((mem_orv _ _ _).mpr (Or.inr hx))
      · exact Or.inr ⟨j, hj2, hx⟩

theorem blk_rv (S : List ℕ) (k : ℕ) (c h : ℕ) (t : List ℕ) (w : ℕ)
    (d : List (List (List ℕ))) (hw : d.length = w) (h1 : h < w) (h2 : ∀ i ∈ t, i < w)
    (h3 : c < w) (i : ℕ) (hi : i ∈ h :: t) (u y : List ℕ) (hu : u ∈ d.getD i [])
    (hy : y ∈ d.getD c []) :
    capAdd k (capAdd k (S.map fun _ => 0) u) y ∈
      (F (rstep S k) (blk c h t w) d).getD (w + t.length) [] := by
  obtain ⟨c1, c2, c3, c4⟩ :=
    chain_spec (rstep S k) [] orv (rstep_or S k) t h w d hw h1 h2
  unfold blk
  rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq c1), c1, Nat.sub_self,
    List.getD_cons_zero, rstep_and, c3, c2 _ h3, mem_andStep]
  refine ⟨_, ?_, y, hy, rfl⟩
  rw [mem_andStep]
  refine ⟨_, by simp, u, ?_, rfl⟩
  apply foldl_orv u (fun i => d.getD i [])
  rcases List.mem_cons.mp hi with e | hi2
  · rw [e] at hu
    exact Or.inl hu
  · exact Or.inr ⟨i, hi2, hu⟩

theorem G_rv (S : List ℕ) (k : ℕ) (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (x : List (List (List ℕ)))
    (hx : x.length = n) (h0 : s0.1 < n ∧ ∀ i ∈ s0.2.1 :: s0.2.2, i < n) :
    ∀ r : List (ℕ × ℕ × List ℕ), (∀ s ∈ r, s.1 < n ∧ ∀ i ∈ s.2.1 :: s.2.2, i < n) →
      ∀ s ∈ s0 :: r, ∀ i ∈ s.2.1 :: s.2.2, ∀ u ∈ x.getD i [], ∀ y ∈ x.getD s.1 [],
        capAdd k (capAdd k (S.map fun _ => 0) u) y ∈
          (F (rstep S k) (G n s0 r) x).getD (n + (G n s0 r).length - 1) []
  | [], _ => by
    intro s hs i hi u hu y hy
    have hs2 := List.mem_singleton.mp hs
    rw [hs2] at hi hy
    have e : n + (G n s0 []).length - 1 = n + s0.2.2.length := by
      simp only [G, blk_len]
      omega
    rw [e]
    simp only [G]
    exact blk_rv S k s0.1 s0.2.1 s0.2.2 n x hx (h0.2 _ (by simp))
      (fun i hi => h0.2 i (by simp [hi])) h0.1 i hi u y hu hy
  | s :: r, hr => by
    intro s' hs' i hi u hu y hy
    have ih := G_rv S k n s0 x hx h0 r (fun s' hs' => hr s' (by simp [hs']))
    have hs := hr s (by simp)
    have hL : (F (rstep S k) (G n s0 r) x).length = n + (G n s0 r).length := by
      rw [F_len, hx]
    have hpre : ∀ i < n, (F (rstep S k) (G n s0 r) x).getD i [] = x.getD i [] :=
      fun i hi => F_pre (rstep S k) [] _ _ i (by omega)
    have hL2 : (F (rstep S k) (G n s0 r ++ blk s.1 s.2.1 s.2.2 (n + (G n s0 r).length))
        x).length = n + (G n s0 r).length + s.2.2.length + 1 := by
      rw [F_len, List.length_append, blk_len, hx]
      omega
    have hpos := G_pos n s0 r
    have e : n + (G n s0 (s :: r)).length - 1 =
        n + (G n s0 r).length + s.2.2.length + 1 := by
      simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil]
      omega
    rw [e]
    simp only [G]
    rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq hL2), hL2, Nat.sub_self,
      List.getD_cons_zero, rstep_or, mem_orv]
    rw [F_append, F_pre (rstep S k) [] _ _ (n + (G n s0 r).length - 1)
      (by rw [hL]; omega)]
    simp only [List.mem_cons] at hs'
    rcases hs' with h | h | h
    · exact Or.inl (ih s' (by simp [h]) i hi u hu y hy)
    · rw [h] at hi hy
      refine Or.inr (blk_rv S k s.1 s.2.1 s.2.2 (n + (G n s0 r).length) _ hL
        (by have := hs.2 s.2.1 (by simp); omega)
        (fun i hi => by have := hs.2 i (by simp [hi]); omega) (by have := hs.1; omega)
        i hi u y ?_ ?_)
      · rw [hpre i (hs.2 i hi)]
        exact hu
      · rw [hpre _ hs.1]
        exact hy
    · exact Or.inl (ih s' (by simp [h]) i hi u hu y hy)

theorem capAdd_map (k : ℕ) (f g : ℕ → ℕ) : ∀ S : List ℕ,
    capAdd k (S.map f) (S.map g) = S.map fun j => min (f j + g j) (k + 1)
  | [] => rfl
  | a :: S => by
    have ih := capAdd_map k f g S
    unfold capAdd at ih ⊢
    simp only [List.map_cons, List.zipWith_cons_cons, ih]

theorem read_ok (S : List ℕ) (k a b : ℕ) (hk : 1 ≤ k) (hab : a ≠ b) :
    ((capAdd k (capAdd k (S.map fun _ => 0)
        (S.map fun j => if j = a then min 1 (k + 1) else 0))
      (S.map fun j => if j = b then min 1 (k + 1) else 0)).all
        fun x => decide (x ≤ k)) = true := by
  rw [capAdd_map, capAdd_map, List.all_eq_true]
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  rw [decide_eq_true_eq]
  split_ifs with h1 h2 <;> omega

theorem leaf_getD (S : List ℕ) (k n i : ℕ) (hi : i < n) (hS : i ∈ S) :
    (S.map fun j => if j = i then min 1 (k + 1) else 0) ∈
      ((List.range n).map (leafVectors S k)).getD i [] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [leafVectors, hS]

def pts {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : List ℕ :=
  ((List.finRange N).filter fun p => decide (I p l)).map Fin.val

def star {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : ℕ × ℕ × List ℕ :=
  (N + l.val, (pts I l).headD 0, (pts I l).tail)

theorem mem_pts {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) (i : ℕ) :
    i ∈ pts I l ↔ ∃ p : Fin N, I p l ∧ p.val = i := by
  simp [pts]

theorem pts_len {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) :
    (pts I l).length = (Finset.univ.filter (fun p => I p l)).card := by
  have e : (Finset.univ.filter (fun p => I p l)) =
      ((List.finRange N).filter fun p => decide (I p l)).toFinset := by
    ext p
    simp
  rw [e, List.toFinset_card_of_nodup ((List.nodup_finRange N).filter _)]
  simp [pts]

theorem hd_tl {α : Type} (d : α) : ∀ l : List α, l ≠ [] → l.headD d :: l.tail = l
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem upper (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hN : 0 < N)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z2 : Fin (N + N) → Bool, circuitFun (N + N) D z2 =
        decide (∃ p4 l4 : Fin N, I p4 l4 ∧ z2 (Fin.castAdd N p4) = true ∧
          z2 (Fin.natAdd N l4) = true)) ∧
      IsReadK (N + N) D 1 ∧ D.size + 1 = N * (q + 2) := by
  have hall0 : (List.finRange N).map (star I) ≠ [] := by
    intro h
    have h2 := congrArg List.length h
    simp at h2
    omega
  have hall := hd_tl (0, 0, []) _ hall0
  generalize ((List.finRange N).map (star I)).headD (0, 0, []) = s0 at hall
  generalize ((List.finRange N).map (star I)).tail = r at hall
  have hmem : ∀ s ∈ s0 :: r, ∃ l : Fin N, s = star I l := by
    intro s hs
    rw [hall] at hs
    obtain ⟨l, _, hl⟩ := List.mem_map.mp hs
    exact ⟨l, hl.symm⟩
  have hlen : ∀ l : Fin N, (pts I l).length = q + 1 := fun l => by rw [pts_len, hc]
  have hcons : ∀ l : Fin N, (star I l).2.1 :: (star I l).2.2 = pts I l := by
    intro l
    apply hd_tl
    intro h
    have := hlen l
    rw [h] at this
    simp at this
  have hbd : ∀ s ∈ s0 :: r, s.1 < N + N ∧ ∀ i ∈ s.2.1 :: s.2.2, i < N + N := by
    intro s hs
    obtain ⟨l, rfl⟩ := hmem s hs
    refine ⟨?_, ?_⟩
    · show N + l.val < N + N
      have := l.isLt
      omega
    · intro i hi
      rw [hcons l] at hi
      obtain ⟨p, _, rfl⟩ := (mem_pts I l i).mp hi
      have := p.isLt
      omega
  have hb0 := hbd s0 (by simp)
  have hbr : ∀ s ∈ r, s.1 < N + N ∧ ∀ i ∈ s.2.1 :: s.2.2, i < N + N :=
    fun s hs => hbd s (by simp [hs])
  have hzl : ∀ (z : Fin (N + N) → Bool) (l : Fin N),
      (List.ofFn z).getD (N + l.val) false = z (Fin.natAdd N l) :=
    fun z l => ofFn_getD z false (N + l.val) (by have := l.isLt; omega)
  have hzp : ∀ (z : Fin (N + N) → Bool) (p : Fin N),
      (List.ofFn z).getD p.val false = z (Fin.castAdd N p) :=
    fun z p => ofFn_getD z false p.val (by have := p.isLt; omega)
  have hval : ∀ z2 : Fin (N + N) → Bool,
      circuitFun (N + N) ⟨G (N + N) s0 r, N + N + (G (N + N) s0 r).length - 1⟩ z2 =
        decide (∃ p4 l4 : Fin N, I p4 l4 ∧ z2 (Fin.castAdd N p4) = true ∧
          z2 (Fin.natAdd N l4) = true) := by
    intro z
    have hv := G_val (N + N) s0 (List.ofFn z) (by simp) hb0 r hbr
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    refine Iff.trans hv ?_
    constructor
    · rintro ⟨s, hs, h1, i, hi, h2⟩
      obtain ⟨l, rfl⟩ := hmem s hs
      rw [hcons l] at hi
      obtain ⟨p, hp, rfl⟩ := (mem_pts I l i).mp hi
      refine ⟨p, l, hp, ?_, ?_⟩
      · rw [← hzp z p]
        exact h2
      · rw [← hzl z l]
        exact h1
    · rintro ⟨p, l, hp, h1, h2⟩
      refine ⟨star I l, ?_, ?_, p.val, ?_, ?_⟩
      · rw [hall]
        exact List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩
      · show (List.ofFn z).getD (N + l.val) false = true
        rw [hzl z l]
        exact h2
      · rw [hcons l]
        exact (mem_pts I l _).mpr ⟨p, hp, rfl⟩
      · rw [hzp z p]
        exact h1
  refine ⟨⟨G (N + N) s0 r, N + N + (G (N + N) s0 r).length - 1⟩, ?_, hval, ?_, ?_⟩
  · refine And.intro ?_ (And.intro ?_ ?_)
    · intro g hg
      exact (G_shape _ _ _ g hg).1
    · exact RB_G (N + N) s0 hb0 r hbr
    · intro g hg
      exact (G_shape _ _ _ g hg).2
  · intro S hS
    have ht := hS.1
    rw [hval, decide_eq_true_iff] at ht
    obtain ⟨p, l, hpl, h1, h2⟩ := ht
    have h1' : Fin.castAdd N p ∈ S := of_decide_eq_true h1
    have h2' : Fin.natAdd N l ∈ S := of_decide_eq_true h2
    have hpL : p.val ∈ setList S :=
      List.mem_map.mpr ⟨Fin.castAdd N p,
        List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using h1'⟩, rfl⟩
    have hlL : N + l.val ∈ setList S :=
      List.mem_map.mpr ⟨Fin.natAdd N l,
        List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using h2'⟩, rfl⟩
    have hpn : p.val < N + N := by have := p.isLt; omega
    have hln : N + l.val < N + N := by have := l.isLt; omega
    have hmemv := G_rv (setList S) 1 (N + N) s0
      ((List.range (N + N)).map (leafVectors (setList S) 1)) (by simp) hb0 r hbr
      (star I l) (by rw [hall]; exact List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩)
      p.val (by rw [hcons l]; exact (mem_pts I l _).mpr ⟨p, hpl, rfl⟩)
      _ (leaf_getD (setList S) 1 (N + N) p.val hpn hpL)
      _ (leaf_getD (setList S) 1 (N + N) (N + l.val) hln hlL)
    show ((readVectors ⟨G (N + N) s0 r, N + N + (G (N + N) s0 r).length - 1⟩ (N + N)
      (setList S) 1).getD (N + N + (G (N + N) s0 r).length - 1) []).any
        (fun v => v.all fun a => decide (a ≤ 1)) = true
    rw [rv_eq, List.any_eq_true]
    exact ⟨_, hmemv, read_ok (setList S) 1 p.val (N + l.val) (le_refl 1)
      (by have := p.isLt; omega)⟩
  · show (G (N + N) s0 r).length + 1 = N * (q + 2)
    rw [G_len]
    have hq2 : ∀ s ∈ s0 :: r, s.2.2.length + 2 = q + 2 := by
      intro s hs
      obtain ⟨l, rfl⟩ := hmem s hs
      have := hlen l
      show (pts I l).tail.length + 2 = q + 2
      rw [List.length_tail]
      omega
    have e : (s0.2.2.length + 2) + (r.map fun s => s.2.2.length + 2).sum =
        ((s0 :: r).map fun s => s.2.2.length + 2).sum := by
      simp only [List.map_cons, List.sum_cons]
    have e2 : ((s0 :: r).map fun s => s.2.2.length + 2) = List.replicate N (q + 2) := by
      apply List.eq_replicate_iff.mpr
      refine ⟨?_, ?_⟩
      · rw [List.length_map, hall]
        simp
      · intro b hb
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
        exact hq2 s hs
    rw [e, e2, List.sum_replicate, smul_eq_mul]

theorem lines_through {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (p0 : Fin N) : (Finset.univ.filter (fun l => I p0 l)).card = q + 1 := by
  have h1 : ∀ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
      ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card = 1 := by
    intro p hp
    have hne : p0 ≠ p := (Finset.ne_of_mem_erase hp).symm
    obtain ⟨l, hl, hu⟩ := huniq p0 p hne
    rw [Finset.card_eq_one]
    refine ⟨l, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx
      exact hu x hx
    · intro hx
      rw [hx]
      exact hl
  have h2 : ∀ l ∈ Finset.univ.filter (fun l => I p0 l),
      (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card = q := by
    intro l hl
    have hl' := (Finset.mem_filter.mp hl).2
    have e : ((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)
        = (Finset.univ.filter (fun p => I p l)).erase p0 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    have hmem : p0 ∈ Finset.univ.filter (fun p => I p l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩
    rw [e, Finset.card_erase_of_mem hmem, hline l]
    rfl
  have h3 : ∑ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
        ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card
      = ∑ l ∈ Finset.univ.filter (fun l => I p0 l),
        (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2] at h3
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ p0),
    Finset.card_univ, Fintype.card_fin] at h3
  have e : N - 1 = (q + 1) * q := by
    have : (q + 1) * q = q ^ 2 + q := by ring
    omega
  rw [e] at h3
  exact (Nat.eq_of_mul_eq_mul_right hq h3).symm

theorem cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
  have := p.isLt
  omega

theorem cast_inj {N : ℕ} {p p' : Fin N} (h : Fin.castAdd N p = Fin.castAdd N p') : p = p' := by
  have h2 := congrArg Fin.val h
  simp only [Fin.val_castAdd] at h2
  exact Fin.ext h2

theorem nat_inj {N : ℕ} {l l' : Fin N} (h : Fin.natAdd N l = Fin.natAdd N l') : l = l' := by
  have h2 := congrArg Fin.val h
  simp only [Fin.val_natAdd] at h2
  exact Fin.ext (by omega)

theorem fin_split {N : ℕ} (u : Fin (N + N)) :
    (∃ p : Fin N, u = Fin.castAdd N p) ∨ (∃ l : Fin N, u = Fin.natAdd N l) := by
  rcases Nat.lt_or_ge u.val N with h | h
  · exact Or.inl ⟨⟨u.val, h⟩, Fin.ext rfl⟩
  · have := u.isLt
    exact Or.inr ⟨⟨u.val - N, by omega⟩, Fin.ext (by simp only [Fin.val_natAdd]; omega)⟩

def PG {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N + N)) where
  Adj u v := ∃ p l : Fin N, I p l ∧
    ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))
  symm := ⟨by
    rintro u v ⟨p, l, h, h2⟩
    exact ⟨p, l, h, h2.symm.imp And.symm And.symm⟩⟩
  loopless := ⟨by
    rintro u ⟨p, l, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact cast_ne_nat p l (h1.symm.trans h2)
    · exact cast_ne_nat p l (h2.symm.trans h1)⟩

theorem adj_cast {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) (v : Fin (N + N)) :
    (PG I).Adj (Fin.castAdd N p) v ↔ ∃ l : Fin N, I p l ∧ v = Fin.natAdd N l := by
  constructor
  · rintro ⟨p', l, h, ⟨h1, h2⟩ | ⟨h1, _⟩⟩
    · have := cast_inj h1
      subst this
      exact ⟨l, h, h2⟩
    · exact absurd h1 (cast_ne_nat p l)
  · rintro ⟨l, h, rfl⟩
    exact ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩

theorem adj_nat {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) (v : Fin (N + N)) :
    (PG I).Adj (Fin.natAdd N l) v ↔ ∃ p : Fin N, I p l ∧ v = Fin.castAdd N p := by
  constructor
  · rintro ⟨p, l', h, ⟨h1, _⟩ | ⟨h1, h2⟩⟩
    · exact absurd h1.symm (cast_ne_nat p l)
    · have := nat_inj h1
      subst this
      exact ⟨p, h, h2⟩
  · rintro ⟨p, h, rfl⟩
    exact ⟨p, l, h, Or.inr ⟨rfl, rfl⟩⟩

theorem pg_nfc {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel (PG I).Adj]
    (hU : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) :
    PEqualNP.TopForm.NoFourCycle (PG I) := by
  intro a b hab
  rw [Finset.card_le_one]
  intro w1 h1 w2 h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  rcases fin_split a with ⟨pa, rfl⟩ | ⟨la, rfl⟩
  · obtain ⟨l1, i1, rfl⟩ := (adj_cast I pa w1).mp h1.1
    obtain ⟨l2, i2, rfl⟩ := (adj_cast I pa w2).mp h2.1
    obtain ⟨pb, j1, rfl⟩ := (adj_nat I l1 b).mp h1.2.symm
    obtain ⟨l3, j2, e⟩ := (adj_cast I pb _).mp h2.2
    have := nat_inj e
    subst this
    have hne : pa ≠ pb := fun h => hab (by rw [h])
    rw [(hU pa pb hne).unique ⟨i1, j1⟩ ⟨i2, j2⟩]
  · obtain ⟨p1, i1, rfl⟩ := (adj_nat I la w1).mp h1.1
    obtain ⟨p2, i2, rfl⟩ := (adj_nat I la w2).mp h2.1
    obtain ⟨lb, j1, rfl⟩ := (adj_cast I p1 b).mp h1.2.symm
    obtain ⟨p3, j2, e⟩ := (adj_nat I lb _).mp h2.2
    have := cast_inj e
    subst this
    by_contra hne
    have hp : p1 ≠ p2 := fun h => hne (by rw [h])
    exact hab (by rw [(hU p1 p2 hp).unique ⟨i1, i2⟩ ⟨j1, j2⟩])

def Inc {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    Finset (Fin N × Fin N) := (A ×ˢ B).filter (fun pl => I pl.1 pl.2)

theorem Inc_right {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    (Inc I A B).card = ∑ l ∈ B, (A.filter (fun p => I p l)).card := by
  unfold Inc
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.card_filter]

theorem Inc_left {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    (Inc I A B).card = ∑ p ∈ A, (B.filter (fun l => I p l)).card := by
  unfold Inc
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

theorem pg_edges {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    [DecidableRel (PG I).Adj]
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    N * (q + 1) ≤ (PG I).edgeFinset.card := by
  have h0 : (Inc I Finset.univ Finset.univ).card = N * (q + 1) := by
    rw [Inc_right, Finset.sum_congr rfl (fun l _ => hc l)]
    simp
  rw [← h0]
  refine Finset.card_le_card_of_injOn
    (fun pl => s(Fin.castAdd N pl.1, Fin.natAdd N pl.2)) ?_ ?_
  · intro pl hpl
    have hpl' : pl ∈ Inc I Finset.univ Finset.univ := hpl
    have hI : I pl.1 pl.2 := (Finset.mem_filter.mp hpl').2
    have hadj : (PG I).Adj (Fin.castAdd N pl.1) (Fin.natAdd N pl.2) :=
      (adj_cast I pl.1 _).mpr ⟨pl.2, hI, rfl⟩
    exact SimpleGraph.mem_edgeFinset.mpr hadj
  · intro a _ b _ hab
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    have hab' : s(Fin.castAdd N a1, Fin.natAdd N a2) = s(Fin.castAdd N b1, Fin.natAdd N b2) :=
      hab
    rcases Sym2.eq_iff.mp hab' with ⟨e1, e2⟩ | ⟨e1, _⟩
    · rw [cast_inj e1, nat_inj e2]
    · exact absurd e1 (cast_ne_nat a1 b2)

theorem cover_ge {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hd : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (T : Finset (Fin (N + N)))
    (hT : ∀ p l : Fin N, I p l → Fin.castAdd N p ∈ T ∨ Fin.natAdd N l ∈ T) :
    N ≤ T.card := by
  have h0 : (Inc I Finset.univ Finset.univ).card = N * (q + 1) := by
    rw [Inc_right, Finset.sum_congr rfl (fun l _ => hc l)]
    simp
  have h1 : (Inc I (Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T))
      Finset.univ).card =
      (Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T)).card * (q + 1) := by
    rw [Inc_left, Finset.sum_congr rfl (fun p _ => hd p)]
    simp
  have h2 : (Inc I Finset.univ
      (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T))).card =
      (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T)).card * (q + 1) := by
    rw [Inc_right, Finset.sum_congr rfl (fun l _ => hc l)]
    simp
  have hsub : Inc I Finset.univ Finset.univ ⊆
      Inc I (Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T)) Finset.univ ∪
        Inc I Finset.univ (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T)) := by
    intro pl hpl
    have hI : I pl.1 pl.2 := (Finset.mem_filter.mp hpl).2
    rw [Finset.mem_union]
    rcases hT pl.1 pl.2 hI with h | h
    · left
      unfold Inc
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true]
      exact ⟨h, hI⟩
    · right
      unfold Inc
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact ⟨h, hI⟩
  have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [h0, h1, h2] at hle
  have e1 : T.card = ∑ i : Fin (N + N), (if i ∈ T then 1 else 0) := by
    rw [← Finset.card_filter]
    congr 1
    ext i
    simp
  have hTT : (Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T)).card +
      (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T)).card = T.card := by
    rw [e1, Fin.sum_univ_add, Finset.card_filter, Finset.card_filter]
  rw [← hTT]
  rw [← Nat.add_mul] at hle
  exact Nat.le_of_mul_le_mul_right hle (Nat.succ_pos q)

theorem lower (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1)
    (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧
        z (Fin.natAdd N l3) = true))
    (hread : IsReadK (N + N) C 1) : N * (q + 2) ≤ C.size + 1 := by
  classical
  have hd := lines_through q I (by omega) hN hc hU
  obtain ⟨T, hT, hle⟩ := PEqualNP.Outside.L_meta_2239.main (N + N) (PG I) C (pg_nfc I hU) hAO (fun x => by
    rw [hfun x]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨p, l, h, h1, h2⟩
      exact ⟨Fin.castAdd N p, Fin.natAdd N l, (adj_cast I p _).mpr ⟨l, h, rfl⟩, h1, h2⟩
    · rintro ⟨u, v, ⟨p, l, h, hh⟩, hu, hv⟩
      rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨p, l, h, hu, hv⟩
      · exact ⟨p, l, h, hv, hu⟩) hread
  have hE := pg_edges q I hc
  have hTN := cover_ge q I hc hd T
    (fun p l h => hT _ _ ((adj_cast I p _).mpr ⟨l, h, rfl⟩))
  have e : N * (q + 2) = N * (q + 1) + N := by ring
  omega

end Own

end PEqualNP.Outside.L_meta_2239

theorem PEqualNP.Outside.L_meta_2239 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 1 → N * (q + 2) ≤ C.size + 1) ∧ (∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ z2 : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z2 = decide (∃ p4 l4 : Fin N, I p4 l4 ∧ z2 (Fin.castAdd N p4) = true ∧ z2 (Fin.natAdd N l4) = true)) ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 ∧ D.size + 1 = N * (q + 2)) := by
  intro q N I _ hq hN hc hU
  exact ⟨fun C hAO hfun hread => PEqualNP.Outside.L_meta_2239.Own.lower q N I hq hN hc hU C hAO hfun hread,
    PEqualNP.Outside.L_meta_2239.Own.upper q N I (by omega) hc⟩
