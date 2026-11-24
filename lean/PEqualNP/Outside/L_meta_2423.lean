import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2423

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadK

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

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

lemma val_and2 (C : Circuit) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (u1 u2 : ℕ) (hin : (gateAt C k).inputs = [u1, u2])
    (h1 : u1 < n + k) (h2 : u2 < n + k) (hv1 : val C.gates u1 x = true)
    (hv2 : val C.gates u2 x = true) : val C.gates (n + k) x = true := by
  rw [gateAt_eq C k hk] at hop hin
  refine (val_and C.gates x k hk hop).mpr ?_
  intro i hi
  rw [hin] at hi
  have hi2 : i = u1 ∨ i = u2 := by simpa using hi
  rcases hi2 with e | e
  · rw [e]; exact ⟨h1, hv1⟩
  · rw [e]; exact ⟨h2, hv2⟩

def Rr (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs)

def Tt (n : ℕ) (C : Circuit) : ℕ → List (ℕ × ℕ) → Prop :=
  fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop,
    (∀ (qv qt : ℕ), qv < n → Rr n C qv qt → Q qt [(qt, qv)]) →
    (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
      (gateAt C qj).op = GateOp.and → Rr n C (n + qj) qt →
      Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 →
      Q qt (qL1 ++ qL2)) → Q tt tL

lemma Tt_leaf (n : ℕ) (C : Circuit) (qv qt : ℕ) (h1 : qv < n) (h2 : Rr n C qv qt) :
    Tt n C qt [(qt, qv)] := fun _ hl _ => hl qv qt h1 h2

lemma Tt_node (n : ℕ) (C : Circuit) (qj qt : ℕ) (L1 L2 : List (ℕ × ℕ))
    (h1 : qj < C.gates.length) (h2 : (gateAt C qj).op = GateOp.and) (h3 : Rr n C (n + qj) qt)
    (t1 : Tt n C ((gateAt C qj).inputs.getD 0 0) L1)
    (t2 : Tt n C ((gateAt C qj).inputs.getD 1 0) L2) : Tt n C qt (L1 ++ L2) :=
  fun Q hl hn => hn qj qt L1 L2 h1 h2 h3 (t1 Q hl hn) (t2 Q hl hn)

lemma Rr_refl (n : ℕ) (C : Circuit) (t : ℕ) : Rr n C t t := Relation.ReflTransGen.refl

lemma Rr_trans (n : ℕ) (C : Circuit) (a b c : ℕ) (h1 : Rr n C a b) (h2 : Rr n C b c) :
    Rr n C a c := Relation.ReflTransGen.trans h1 h2

lemma Rr_step (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (ui : ℕ) (hin : ui ∈ (gateAt C k).inputs)
    (hlt : ui < n + k) : Rr n C ui (n + k) :=
  Relation.ReflTransGen.single ⟨hlt, k, rfl, hk, hop, hin⟩

lemma capfix (a b : ℕ) : min (min (min a 3) 3 + min b 3) 3 = min (a + b) 3 := by omega

lemma tree_of (n : ℕ) (C : Circuit) (u w : ℕ) (hne : u ≠ w) (t : ℕ) (v : List ℕ)
    (hinv : (∃ c, (c = u ∨ c = w) ∧ c < n ∧ Rr n C c t ∧
        v = [if u = c then 1 else 0, if w = c then 1 else 0]) ∨
      (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧
        (gateAt C j0).op = GateOp.and ∧ Rr n C (n + j0) t ∧
        Tt n C ((gateAt C j0).inputs.getD 0 0) L1 ∧ Tt n C ((gateAt C j0).inputs.getD 1 0) L2 ∧
        (∀ gv ∈ L1 ++ L2, gv.2 = u ∨ gv.2 = w) ∧
        v = [min ((L1 ++ L2).filter (fun e => decide (e.2 = u))).length 3,
             min ((L1 ++ L2).filter (fun e => decide (e.2 = w))).length 3])) :
    ∃ L : List (ℕ × ℕ), Tt n C t L ∧ (∀ gv ∈ L, gv.2 = u ∨ gv.2 = w) ∧
      v = [min (L.filter (fun e => decide (e.2 = u))).length 3,
           min (L.filter (fun e => decide (e.2 = w))).length 3] := by
  rcases hinv with ⟨c, hc, hcn, hR, he⟩ | ⟨j0, L1, L2, hj, hop, hR, hT1, hT2, hg, he⟩
  · refine ⟨[(t, c)], Tt_leaf n C c t hcn hR, ?_, ?_⟩
    · intro gv hgv
      have e : gv = (t, c) := by simpa using hgv
      rw [e]
      exact hc
    · rw [he]
      have hne2 : ¬ w = u := fun e => hne e.symm
      rcases hc with hc | hc
      · rw [hc]; simp [hne, hne2]
      · rw [hc]; simp [hne, hne2]
  · exact ⟨L1 ++ L2, Tt_node n C j0 t L1 L2 hj hop hR hT1 hT2, hg, he⟩

lemma inv (n : ℕ) (C : Circuit) (h : IsAO2 n C) (u w : ℕ) (hne : u ≠ w) :
    ∀ t, ∀ v ∈ V C n [u, w] t,
      (∃ c, (c = u ∨ c = w) ∧ c < n ∧ Rr n C c t ∧
        v = [if u = c then 1 else 0, if w = c then 1 else 0]) ∨
      (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧
        (gateAt C j0).op = GateOp.and ∧ Rr n C (n + j0) t ∧
        Tt n C ((gateAt C j0).inputs.getD 0 0) L1 ∧ Tt n C ((gateAt C j0).inputs.getD 1 0) L2 ∧
        (∀ gv ∈ L1 ++ L2, gv.2 = u ∨ gv.2 = w) ∧
        v = [min ((L1 ++ L2).filter (fun e => decide (e.2 = u))).length 3,
             min ((L1 ++ L2).filter (fun e => decide (e.2 = w))).length 3]) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v hv
    rcases wire_cases n C h t with ht | ht | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · rw [V_leaf C n _ t ht] at hv
      obtain ⟨hm, rfl⟩ := (mem_leaf u w t v).mp hv
      exact Or.inl ⟨t, hm, ht, Rr_refl n C t, rfl⟩
    · rw [V_big C n _ t ht] at hv
      simp at hv
    · obtain ⟨p, hp, q, hq, he⟩ := (V_and C n _ k hk hop u1 u2 hin h1 h2 v).mp hv
      obtain ⟨L1, hT1, hg1, rfl⟩ := tree_of n C u w hne u1 p (ih u1 (by omega) p hp)
      obtain ⟨L2, hT2, hg2, rfl⟩ := tree_of n C u w hne u2 q (ih u2 (by omega) q hq)
      rw [cap2, capfix, capfix] at he
      have e0 : (gateAt C k).inputs.getD 0 0 = u1 := by rw [hin]; rfl
      have e1 : (gateAt C k).inputs.getD 1 0 = u2 := by rw [hin]; rfl
      refine Or.inr ⟨k, L1, L2, hk, hop, Rr_refl n C (n + k), by rw [e0]; exact hT1,
        by rw [e1]; exact hT2, ?_, ?_⟩
      · intro gv hgv
        rcases List.mem_append.mp hgv with hgv | hgv
        · exact hg1 gv hgv
        · exact hg2 gv hgv
      · rw [← he]
        simp only [List.filter_append, List.length_append]
    · have key : ∀ ui, (ui = u1 ∨ ui = u2) → ui < n + k → v ∈ V C n [u, w] ui →
          (∃ c, (c = u ∨ c = w) ∧ c < n ∧ Rr n C c (n + k) ∧
            v = [if u = c then 1 else 0, if w = c then 1 else 0]) ∨
          (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧
            (gateAt C j0).op = GateOp.and ∧ Rr n C (n + j0) (n + k) ∧
            Tt n C ((gateAt C j0).inputs.getD 0 0) L1 ∧
            Tt n C ((gateAt C j0).inputs.getD 1 0) L2 ∧
            (∀ gv ∈ L1 ++ L2, gv.2 = u ∨ gv.2 = w) ∧
            v = [min ((L1 ++ L2).filter (fun e => decide (e.2 = u))).length 3,
                 min ((L1 ++ L2).filter (fun e => decide (e.2 = w))).length 3]) := by
        intro ui hui hlt hmem
        have hin2 : ui ∈ (gateAt C k).inputs := by rw [hin]; simpa using hui
        have hst := Rr_step n C k hk hop ui hin2 hlt
        rcases ih ui hlt v hmem with ⟨c, hc, hcn, hR, he⟩ |
          ⟨j0, L1, L2, hj, hop2, hR, hT1, hT2, hg, he⟩
        · exact Or.inl ⟨c, hc, hcn, Rr_trans n C _ _ _ hR hst, he⟩
        · exact Or.inr ⟨j0, L1, L2, hj, hop2, Rr_trans n C _ _ _ hR hst, hT1, hT2, hg, he⟩
      rcases (V_or C n _ k hk hop u1 u2 hin h1 h2 v).mp hv with h3 | h3
      · exact key u1 (Or.inl rfl) h1 h3
      · exact key u2 (Or.inr rfl) h2 h3

lemma zval (n : ℕ) (C : Circuit) (h : IsAO2 n C) (u w : ℕ) :
    ∀ t, ∀ v ∈ V C n [u, w] t, ∃ x y : ℕ, v = [x, y] ∧
      (y = 0 → val C.gates t (fun k1 : Fin n => decide (k1.val = u)) = true) ∧
      (x = 0 → val C.gates t (fun k2 : Fin n => decide (k2.val = w)) = true) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v hv
    rcases wire_cases n C h t with ht | ht | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · rw [V_leaf C n _ t ht] at hv
      obtain ⟨hm, rfl⟩ := (mem_leaf u w t v).mp hv
      refine ⟨_, _, rfl, ?_, ?_⟩
      · intro hy
        rw [val_input C.gates _ t ht]
        by_cases e : w = t
        · rw [if_pos e] at hy
          exact absurd hy (by norm_num)
        · have e2 : t = u := by
            rcases hm with hm | hm
            · exact hm
            · exact absurd hm.symm e
          simpa using e2
      · intro hx
        rw [val_input C.gates _ t ht]
        by_cases e : u = t
        · rw [if_pos e] at hx
          exact absurd hx (by norm_num)
        · have e2 : t = w := by
            rcases hm with hm | hm
            · exact absurd hm.symm e
            · exact hm
          simpa using e2
    · rw [V_big C n _ t ht] at hv
      simp at hv
    · obtain ⟨p, hp, q, hq, rfl⟩ := (V_and C n _ k hk hop u1 u2 hin h1 h2 v).mp hv
      obtain ⟨x, y, rfl, hy, hx⟩ := ih u1 (by omega) p hp
      obtain ⟨x2, y2, rfl, hy2, hx2⟩ := ih u2 (by omega) q hq
      rw [cap2]
      refine ⟨_, _, rfl, ?_, ?_⟩
      · intro e
        exact val_and2 C _ k hk hop u1 u2 hin h1 h2 (hy (by omega)) (hy2 (by omega))
      · intro e
        exact val_and2 C _ k hk hop u1 u2 hin h1 h2 (hx (by omega)) (hx2 (by omega))
    · rcases (V_or C n _ k hk hop u1 u2 hin h1 h2 v).mp hv with h3 | h3
      · obtain ⟨x, y, rfl, hy, hx⟩ := ih u1 h1 v h3
        exact ⟨x, y, rfl,
          fun e => val_or2 C _ k hk hop u1 u2 hin u1 (Or.inl rfl) h1 (hy e),
          fun e => val_or2 C _ k hk hop u1 u2 hin u1 (Or.inl rfl) h1 (hx e)⟩
      · obtain ⟨x, y, rfl, hy, hx⟩ := ih u2 h2 v h3
        exact ⟨x, y, rfl,
          fun e => val_or2 C _ k hk hop u1 u2 hin u2 (Or.inr rfl) h2 (hy e),
          fun e => val_or2 C _ k hk hop u1 u2 hin u2 (Or.inr rfl) h2 (hx e)⟩

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

lemma sym1 (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ)
    (hr : readsAtMost C n [a, b] 2 = true) : readsAtMost C n [b, a] 2 = true := by
  unfold readsAtMost at hr ⊢
  rw [List.any_eq_true] at hr ⊢
  obtain ⟨v, hv, hall⟩ := hr
  have hv2 : v ∈ V C n [a, b] C.output := hv
  obtain ⟨x, y, rfl, hs⟩ := swp n C h a b C.output v hv2
  refine ⟨[y, x], hs, ?_⟩
  simp at hall ⊢
  omega

lemma sym2 (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) :
    readsAtMost C n [a, b] 2 = readsAtMost C n [b, a] 2 := by
  rw [Bool.eq_iff_iff]
  exact ⟨sym1 n C h a b, sym1 n C h b a⟩

lemma part2 (n : ℕ) (C : Circuit) (u w : ℕ) (h : IsAO2 n C) (hne : u ≠ w)
    (hfu : circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = false)
    (hfw : circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = false)
    (hr : readsAtMost C n [u, w] 2 = true) :
    ∃ L : List (ℕ × ℕ), (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧
      (gateAt C j0).op = GateOp.and ∧ Rr n C (n + j0) C.output ∧
      Tt n C ((gateAt C j0).inputs.getD 0 0) L1 ∧ Tt n C ((gateAt C j0).inputs.getD 1 0) L2 ∧
      L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = u ∨ gv.2 = w) ∧
      (L.filter (fun e1 => decide (e1.2 = u))).length ∈ ({1, 2} : Finset ℕ) ∧
      (L.filter (fun e2 => decide (e2.2 = w))).length ∈ ({1, 2} : Finset ℕ) := by
  have gu : val C.gates C.output (fun k1 : Fin n => decide (k1.val = u)) = false := hfu
  have gw : val C.gates C.output (fun k2 : Fin n => decide (k2.val = w)) = false := hfw
  unfold readsAtMost at hr
  rw [List.any_eq_true] at hr
  obtain ⟨v, hv, hall⟩ := hr
  have hv2 : v ∈ V C n [u, w] C.output := hv
  obtain ⟨x, y, rfl, hy0, hx0⟩ := zval n C h u w C.output v hv2
  have hall2 : x ≤ 2 ∧ y ≤ 2 := by simpa using hall
  have hx1 : x ≠ 0 := by
    intro e
    have h3 := hx0 e
    rw [h3] at gw
    exact Bool.noConfusion gw
  have hy1 : y ≠ 0 := by
    intro e
    have h3 := hy0 e
    rw [h3] at gu
    exact Bool.noConfusion gu
  rcases inv n C h u w hne C.output [x, y] hv2 with ⟨c, hc, hcn, hR, he⟩ |
    ⟨j0, L1, L2, hj, hop, hR, hT1, hT2, hg, he⟩
  · exfalso
    injection he with e1 e2
    injection e2 with e2 e3
    have hne2 : ¬ w = u := fun e => hne e.symm
    rcases hc with hc | hc
    · rw [hc, if_neg hne2] at e2
      exact hy1 e2
    · rw [hc, if_neg hne] at e1
      exact hx1 e1
  · injection he with e1 e2
    injection e2 with e2 e3
    refine ⟨L1 ++ L2, ⟨j0, L1, L2, hj, hop, hR, hT1, hT2, rfl⟩, hg, ?_, ?_⟩
    · rw [Finset.mem_insert, Finset.mem_singleton]
      omega
    · rw [Finset.mem_insert, Finset.mem_singleton]
      omega

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

lemma half1 (N M : ℕ) (I : Fin N → Fin M → Prop) [DecidableRel I] (C : Circuit)
    (hf : ∀ z : Fin (N + M) → Bool, circuitFun (N + M) C z = decide (∃ (p : Fin N) (l : Fin M),
      I p l ∧ z (Fin.castAdd M p) = true ∧ z (Fin.natAdd N l) = true))
    (P : Finset (Fin N)) (Y : Finset (Fin M)) (hno : ∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) :
    circuitFun (N + M) C (fun k3 : Fin (N + M) => decide (k3.val ∈
      P.image (fun pv : Fin N => pv.val) ∪ Y.image (fun lv : Fin M => N + lv.val))) = false := by
  rw [hf, decide_eq_false_iff_not]
  rintro ⟨p, l, hI, hp, hl⟩
  have hp1 : (Fin.castAdd M p).val ∈
      P.image (fun pv : Fin N => pv.val) ∪ Y.image (fun lv : Fin M => N + lv.val) :=
    of_decide_eq_true hp
  have hl1 : (Fin.natAdd N l).val ∈
      P.image (fun pv : Fin N => pv.val) ∪ Y.image (fun lv : Fin M => N + lv.val) :=
    of_decide_eq_true hl
  have hp2 : p ∈ P := by
    rcases Finset.mem_union.mp hp1 with h2 | h2
    · obtain ⟨a, ha, e⟩ := Finset.mem_image.mp h2
      have e2 : a.val = p.val := e
      have e3 : a = p := Fin.ext e2
      rw [← e3]; exact ha
    · obtain ⟨a, ha, e⟩ := Finset.mem_image.mp h2
      exfalso
      have e2 : N + a.val = p.val := e
      have := p.isLt
      omega
  have hl2 : l ∈ Y := by
    rcases Finset.mem_union.mp hl1 with h2 | h2
    · obtain ⟨a, ha, e⟩ := Finset.mem_image.mp h2
      exfalso
      have e2 : a.val = N + l.val := e
      have := a.isLt
      omega
    · obtain ⟨a, ha, e⟩ := Finset.mem_image.mp h2
      have e2 : N + a.val = N + l.val := e
      have e3 : a = l := Fin.ext (by omega)
      rw [← e3]; exact ha
  exact hno p hp2 l hl2 hI

lemma prime (N M : ℕ) (I : Fin N → Fin M → Prop) [DecidableRel I] (C : Circuit)
    (hf : ∀ z : Fin (N + M) → Bool, circuitFun (N + M) C z = decide (∃ (p : Fin N) (l : Fin M),
      I p l ∧ z (Fin.castAdd M p) = true ∧ z (Fin.natAdd N l) = true))
    (p : Fin N) (l : Fin M) (hI : I p l) :
    IsPrimeImplicant (N + M) C ({Fin.castAdd M p, Fin.natAdd N l} : Finset (Fin (N + M))) := by
  constructor
  · rw [hf]
    exact decide_eq_true ⟨p, l, hI, by simp [setInput], by simp [setInput]⟩
  · intro T hT
    rw [hf, decide_eq_false_iff_not]
    rintro ⟨p2, l2, hI2, hp, hl⟩
    have hp2 : Fin.castAdd M p2 ∈ T := of_decide_eq_true hp
    have hl2 : Fin.natAdd N l2 ∈ T := of_decide_eq_true hl
    rw [Finset.mem_ssubsets] at hT
    have h1 := hT.1 hp2
    have h2 := hT.1 hl2
    rw [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have e1 : Fin.castAdd M p2 = Fin.castAdd M p := by
      rcases h1 with h | h
      · exact h
      · exfalso
        have h3 : p2.val = N + l.val := congrArg Fin.val h
        have := p2.isLt
        omega
    have e2 : Fin.natAdd N l2 = Fin.natAdd N l := by
      rcases h2 with h | h
      · exfalso
        have h3 : N + l2.val = p.val := congrArg Fin.val h
        have := p.isLt
        omega
      · exact h
    apply hT.2
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · rw [hx, ← e1]; exact hp2
    · rw [hx, ← e2]; exact hl2

lemma half2 (N M : ℕ) (I : Fin N → Fin M → Prop) [DecidableRel I] (C : Circuit)
    (h : IsAO2 (N + M) C)
    (hf : ∀ z : Fin (N + M) → Bool, circuitFun (N + M) C z = decide (∃ (p : Fin N) (l : Fin M),
      I p l ∧ z (Fin.castAdd M p) = true ∧ z (Fin.natAdd N l) = true))
    (hrk : IsReadK (N + M) C 2) (p : Fin N) (l : Fin M) (hI : I p l) :
    ∃ L : List (ℕ × ℕ), (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧
      (gateAt C j0).op = GateOp.and ∧ Rr (N + M) C (N + M + j0) C.output ∧
      Tt (N + M) C ((gateAt C j0).inputs.getD 0 0) L1 ∧
      Tt (N + M) C ((gateAt C j0).inputs.getD 1 0) L2 ∧
      L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = p.val ∨ gv.2 = N + l.val) ∧
      (L.filter (fun e1 => decide (e1.2 = p.val))).length ∈ ({1, 2} : Finset ℕ) ∧
      (L.filter (fun e2 => decide (e2.2 = N + l.val))).length ∈ ({1, 2} : Finset ℕ) := by
  have hlt : Fin.castAdd M p < Fin.natAdd N l := by
    rw [Fin.lt_def]
    show p.val < N + l.val
    have := p.isLt
    omega
  have hr := hrk _ (prime N M I C hf p l hI)
  rw [setList_pair _ _ hlt] at hr
  have hr2 : readsAtMost C (N + M) [p.val, N + l.val] 2 = true := hr
  refine part2 (N + M) C p.val (N + l.val) h (by have := p.isLt; omega) ?_ ?_ hr2
  · rw [hf, decide_eq_false_iff_not]
    rintro ⟨p2, l2, hI2, hp, hl⟩
    have h1 : (Fin.natAdd N l2).val = p.val := of_decide_eq_true hl
    have h2 : N + l2.val = p.val := h1
    have := p.isLt
    omega
  · rw [hf, decide_eq_false_iff_not]
    rintro ⟨p2, l2, hI2, hp, hl⟩
    have h1 : (Fin.castAdd M p2).val = N + l.val := of_decide_eq_true hp
    have h2 : p2.val = N + l.val := h1
    have := p2.isLt
    omega

end PEqualNP.Outside.L_meta_2423

theorem PEqualNP.Outside.L_meta_2423 : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (N + M) C → (∀ z : Fin (N + M) → Bool, PEqualNP.MetaComplexity.circuitFun (N + M) C z = decide (∃ (p : Fin N) (l : Fin M), I p l ∧ z (Fin.castAdd M p) = true ∧ z (Fin.natAdd N l) = true)) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = (N + M) + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < (N + M) → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (N + M + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ((∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun (N + M) C (fun k3 : Fin (N + M) => decide (k3.val ∈ P.image (fun pv : Fin N => pv.val) ∪ Y.image (fun lv : Fin M => N + lv.val))) = false)) ∧ (PEqualNP.ReadK.IsReadK (N + M) C 2 → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (N + M + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = p6.val ∨ g6.2 = (N + l6.val)) ∧ (L6.filter (fun e6 => decide (e6.2 = p6.val))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = (N + l6.val)))).length ∈ ({1, 2} : Finset ℕ))) := by
  intro N M I _ C h hf R hR T hT
  subst hR
  subst hT
  exact ⟨fun P Y _ _ hno => PEqualNP.Outside.L_meta_2423.half1 N M I C hf P Y hno,
    fun hrk p6 l6 hI => PEqualNP.Outside.L_meta_2423.half2 N M I C h hf hrk p6 l6 hI⟩
