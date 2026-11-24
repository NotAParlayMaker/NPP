import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3545

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

-- The fold lemmas follow L_meta_1490.
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

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def shift (n d i : ℕ) : ℕ :=
  if i < n then i else i + d

def rewriteCircuit (n : ℕ) (C : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ) : Circuit :=
  ⟨G0 ++ C.gates.mapIdx (fun r g => ⟨g.op, g.inputs.map (rho r)⟩), shift n G0.length C.output⟩

def shiftedRead (n d : ℕ) (D : Circuit) (rho : ℕ → ℕ → ℕ) (r i : ℕ) (x : Fin n → Bool) :
    Bool :=
  if rho r i < n + d + r then wireVal n D (rho r i) x else false

lemma shift_gate (n d r : ℕ) : shift n d (n + r) = n + d + r := by
  simp only [shift, if_neg (show ¬ n + r < n by omega)]
  omega

lemma wireRaw {n : ℕ} (D : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n D i.val x = x i :=
  val_ofFn D x i

lemma wirePast {n : ℕ} (D : Circuit) (i : ℕ) (h : n + D.gates.length ≤ i) (x : Fin n → Bool) :
    wireVal n D i x = false :=
  val_ge (n := n) (by simp) h

lemma wireReadBack {n : ℕ} {C : Circuit} (h : ReadsBack n C) (r : ℕ)
    (hr : r < C.gates.length) (x : Fin n → Bool) :
    wireVal n C (n + r) x = (gateAt C r).op.eval
      ((gateAt C r).inputs.map (fun i => wireVal n C i x)) := by
  change val C _ _ = _
  rw [val_gate (by simp) hr]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (h r hr i hi)]
  rfl

lemma rewrittenLength (n : ℕ) (C : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ) :
    (rewriteCircuit n C G0 rho).gates.length = G0.length + C.gates.length := by
  simp [rewriteCircuit]

lemma rewrittenGate {n : ℕ} {C : Circuit} (G0 : List Gate) (rho : ℕ → ℕ → ℕ) (r : ℕ)
    (hr : r < C.gates.length) (x : Fin n → Bool) :
    wireVal n (rewriteCircuit n C G0 rho) (shift n G0.length (n + r)) x =
      (gateAt C r).op.eval ((gateAt C r).inputs.map
        (fun i => shiftedRead n G0.length (rewriteCircuit n C G0 rho) rho r i x)) := by
  let D := rewriteCircuit n C G0 rho
  have hd : G0.length + r < D.gates.length := by
    change G0.length + r < (rewriteCircuit n C G0 rho).gates.length
    rw [rewrittenLength]
    omega
  have hg : gateAt D (G0.length + r) =
      ⟨(gateAt C r).op, (gateAt C r).inputs.map (rho r)⟩ := by
    rw [gateAt_eq hr]
    change (G0 ++ C.gates.mapIdx (fun k g => (⟨g.op, g.inputs.map (rho k)⟩ : Gate))).getD
      (G0.length + r) ⟨GateOp.or, []⟩ = _
    rw [List.getD_append_right _ _ _ _ (by omega), show G0.length + r - G0.length = r by omega]
    rw [List.getD_eq_getElem _ _ (by simpa using hr)]
    simp
  rw [shift_gate]
  change val D (List.ofFn x) (n + G0.length + r) = _
  rw [show n + G0.length + r = n + (G0.length + r) by omega, val_gate (by simp) hd, hg]
  simp only [List.map_map, shiftedRead, val, wireVal, Nat.add_assoc]
  rfl

lemma prefixWire {n : ℕ} (C : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ) (i : ℕ)
    (hi : i < n + G0.length) (x : Fin n → Bool) :
    wireVal n (rewriteCircuit n C G0 rho) i x = wireVal n ⟨G0, 0⟩ i x := by
  unfold wireVal
  rw [wires_eq_foldl, wires_eq_foldl]
  simp only [rewriteCircuit, List.foldl_append]
  apply foldl_getD_lt
  rw [foldl_length]
  simpa using hi

lemma shifted_normal {n d r i : ℕ} (D : Circuit) (rho : ℕ → ℕ → ℕ)
    (hi : i < n + r) (h : rho r i = shift n d i) (x : Fin n → Bool) :
    shiftedRead n d D rho r i x = wireVal n D (shift n d i) x := by
  unfold shiftedRead
  rw [h, if_pos]
  unfold shift
  split <;> omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- The cone recurrence is adapted from the checked proof of L-meta-1490.
private lemma narrowConesLength (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

private lemma narrowConesCharacterization (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [narrowConesLength]; simp
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

private lemma narrowConeIff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := narrowConesCharacterization n C.gates i j
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

lemma coneRead (n : ℕ) (C : Circuit) (j r : ℕ) (hr : r < C.gates.length)
    (hbefore : n + j < n + r) (hread : n + j ∈ (gateAt C r).inputs) :
    InCone n C j r ∧ ∀ p, InCone n C p j → InCone n C p r := by
  have hjr : j < r := by omega
  refine ⟨(narrowConeIff n C j r).2 ⟨hr, j, hjr, hread, Or.inl rfl⟩, ?_⟩
  intro p hp
  exact (narrowConeIff n C p r).2 ⟨hr, j, hjr, hread, Or.inr hp⟩

lemma coneEarlier (n : ℕ) (C : Circuit) (j r : ℕ) (h : InCone n C j r) : j < r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    obtain ⟨_, k, hk, _, hj | hj⟩ := (narrowConeIff n C j r).1 h
    · exact hj ▸ hk
    · exact (ih k hk hj).trans hk

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

lemma stable {n m : ℕ} {C : Circuit} {u : ℕ → ℕ} {NR : ℕ → ℕ → Prop}
    (old new : ℕ → (Fin n → Bool) → Bool)
    (rd : ℕ → ℕ → (Fin n → Bool) → Bool)
    (hOld : ∀ r, r < C.gates.length → ∀ x,
      old (n + r) x = (gateAt C r).op.eval ((gateAt C r).inputs.map (fun i => old i x)))
    (hNew : ∀ r, r < C.gates.length → ∀ x,
      new (n + r) x = (gateAt C r).op.eval ((gateAt C r).inputs.map (fun i => rd r i x)))
    (hRaw : ∀ (i : Fin n) x, new i.val x = old i.val x)
    (hNormal : ∀ r, r < C.gates.length → ∀ i ∈ (gateAt C r).inputs,
      (∀ k < m, ¬ (NR k r ∧ i = n + u k)) → ∀ x, rd r i x = new i x)
    (hBack : ReadsBack n C)
    (hCone : ∀ j r : ℕ, r < C.gates.length → n + j < n + r → n + j ∈ (gateAt C r).inputs →
      InCone n C j r ∧ ∀ p, InCone n C p j → InCone n C p r) :
    ∀ j, j < C.gates.length → (∀ k < m, ∀ r, NR k r → r ≠ j ∧ ¬ InCone n C r j) →
      ∀ x, new (n + j) x = old (n + j) x := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hUnchanged x
    rw [hNew j hj x, hOld j hj x]
    apply congrArg (gateAt C j).op.eval
    apply List.map_congr_left
    intro i hi
    rw [hNormal j hj i hi (fun k hk h => (hUnchanged k hk j h.1).1 rfl) x]
    by_cases hRawInput : i < n
    · exact hRaw ⟨i, hRawInput⟩ x
    · have hBefore := hBack j hj i hi
      let l := i - n
      have hiEq : i = n + l := by omega
      have hlLt : l < j := by omega
      rcases hCone l j hj (by omega) (hiEq ▸ hi) with ⟨hlCone, hThrough⟩
      have hlUnchanged : ∀ k < m, ∀ r, NR k r → r ≠ l ∧ ¬ InCone n C r l := by
        intro k hk r hr
        have hNo := (hUnchanged k hk r hr).2
        exact ⟨fun heq => hNo (heq ▸ hlCone), fun hc => hNo (hThrough r hc)⟩
      rw [hiEq]
      exact ih l hlLt (by omega) hlUnchanged x

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma rewrittenRead {n m : ℕ} {C : Circuit} {u : ℕ → ℕ} {NR : ℕ → ℕ → Prop}
    {P : ℕ → (Fin n → Bool) → Bool} (G0 : List Gate) (rho : ℕ → ℕ → ℕ)
    (hBack : ReadsBack n C)
    (hNormal : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs,
      (∀ k < m, ¬ (NR k r ∧ i = n + u k)) → rho r i = shift n G0.length i)
    (hReplaced : ∀ r : ℕ, ∀ k < m, NR k r →
      (rho r (n + u k) < n + G0.length ∧
        ∀ x : Fin n → Bool, wireVal n ⟨G0, 0⟩ (rho r (n + u k)) x = P k x) ∨
      (∃ g < r, rho r (n + u k) = n + G0.length + g ∧
        (∀ x : Fin n → Bool, wireVal n C (n + g) x = P k x) ∧
        ∀ k' < m, ∀ r' : ℕ, NR k' r' → r' ≠ g ∧ ¬ InCone n C r' g) ∨
      ((∀ x : Fin n → Bool, P k x = false) ∧ n + G0.length + r ≤ rho r (n + u k)))
    (hStable : ∀ g, g < C.gates.length →
      (∀ k' < m, ∀ r' : ℕ, NR k' r' → r' ≠ g ∧ ¬ InCone n C r' g) →
      ∀ x : Fin n → Bool,
        wireVal n (rewriteCircuit n C G0 rho) (shift n G0.length (n + g)) x =
          wireVal n C (n + g) x) :
    ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, ∀ x : Fin n → Bool,
      (∃ k < m, NR k r ∧ i = n + u k ∧
        shiftedRead n G0.length (rewriteCircuit n C G0 rho) rho r i x = P k x) ∨
      shiftedRead n G0.length (rewriteCircuit n C G0 rho) rho r i x =
        wireVal n (rewriteCircuit n C G0 rho) (shift n G0.length i) x := by
  classical
  intro r hr i hi x
  by_cases hNarrowed : ∃ k < m, NR k r ∧ i = n + u k
  · obtain ⟨k, hk, hNR, rfl⟩ := hNarrowed
    left
    refine ⟨k, hk, hNR, rfl, ?_⟩
    rcases hReplaced r k hk hNR with ⟨hPrefix, hVal⟩ | ⟨g, hg, hAt, hVal, hSafe⟩ | ⟨hVal, hLate⟩
    · unfold shiftedRead
      rw [ite_eq_left (by omega), prefixWire C G0 rho _ hPrefix]
      exact hVal x
    · unfold shiftedRead
      rw [hAt, ite_eq_left (by omega), ← shift_gate n G0.length g]
      exact (hStable g (by omega) hSafe x).trans (hVal x)
    · unfold shiftedRead
      rw [ite_eq_right (Nat.not_lt_of_ge hLate), hVal x]
  · right
    refine shifted_normal _ _ (hBack r hr i hi) (hNormal r hr i hi ?_) x
    exact fun k hk h => hNarrowed ⟨k, hk, h⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

private def upperPair {n : ℕ} (w : Fin n) (z : ℕ) (v : Fin n) : Bool :=
  decide (v = w ∨ v.val = z)

private def upperRegion (n : ℕ) (C : Circuit) (u W : ℕ → ℕ) (k r : ℕ) : Prop :=
  OrReaches n C (W k) r ∧ (gateAt C r).op = GateOp.or ∧ InCone n C (u k) r

private lemma upper_or_true {l : List ℕ} {f : ℕ → Bool} :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]

private lemma upper_and_true {l : List ℕ} {f : ℕ → Bool} :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]

private lemma upper_op_forward {op : GateOp} {l : List ℕ} {f g : ℕ → Bool}
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · intro hf
    exact upper_and_true.mpr (fun i hi => h i hi (upper_and_true.mp hf i hi))
  · rintro hf
    obtain ⟨i, hi, hv⟩ := upper_or_true.mp hf
    exact upper_or_true.mpr ⟨i, hi, h i hi hv⟩

theorem upper {n m : ℕ} (H : SimpleGraph (Fin n)) (q : (Fin n → Bool) → Bool)
    (C : Circuit) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop)
    (P : ℕ → (Fin n → Bool) → Bool) (old new : ℕ → (Fin n → Bool) → Bool)
    (rd : ℕ → ℕ → (Fin n → Bool) → Bool)
    (hQ : ∀ x, q x = true ↔ ∃ a b : Fin n, H.Adj a b ∧ x a = true ∧ x b = true)
    (hFun : ∀ x, old C.output x = q x)
    (hOp : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨
      (gateAt C r).op = GateOp.or)
    (hBack : ReadsBack n C)
    (hOld : ∀ r < C.gates.length, ∀ x, old (n+r) x =
      (gateAt C r).op.eval ((gateAt C r).inputs.map (fun i => old i x)))
    (hNew : ∀ r < C.gates.length, ∀ x, new (n+r) x =
      (gateAt C r).op.eval ((gateAt C r).inputs.map (fun i => rd r i x)))
    (hRead : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, ∀ x,
      (∃ k < m, NR k r ∧ i = n+u k ∧ rd r i x = P k x) ∨ rd r i x = new i x)
    (hOldInput : ∀ i (hi : i < n) x, old i x = x ⟨i, hi⟩)
    (hNewInput : ∀ i (hi : i < n) x, new i x = x ⟨i, hi⟩)
    (hNewMissing : ∀ i, n + C.gates.length ≤ i → ∀ x, new i x = false)
    (hNR : ∀ k r, NR k r → r = T k ∨
      (OrReaches n C (W k) r ∧ (gateAt C r).op = GateOp.or))
    (hP : ∀ k x, P k x = true → ∃ w : Fin n,
      x w = true ∧ old (n+u k) (upperPair w (z k)) = true)
    (hTop : ∀ k < m, (gateAt C (T k)).op = GateOp.and ∧ z k < n ∧
      ((gateAt C (T k)).inputs = [W k,z k] ∨ (gateAt C (T k)).inputs = [z k,W k]) ∧
      ∀ x, old (n+T k) x = true → q x = true)
    (hIsol : ∀ k < m, ∀ g < C.gates.length, OrReaches n C (W k) g →
      (gateAt C g).op = GateOp.or → InCone n C (u k) g → C.output ≠ n+g ∧
      ∀ r < C.gates.length, n+g ∈ (gateAt C r).inputs → r = T k ∨
        (OrReaches n C (W k) r ∧ (gateAt C r).op = GateOp.or))
    (hCone : ∀ {a j r : ℕ}, r < C.gates.length → j < r →
      n+j ∈ (gateAt C r).inputs → a = j ∨ InCone n C a j → InCone n C a r) :
    ∀ y, new C.output y = true → q y = true := by
  classical
  intro y hout
  by_contra hy
  have hwitness (w : Fin n) (i : ℕ) (hi : i<n)
      (hw : y w = true) (hiy : y ⟨i, hi⟩ = true) :
      q (upperPair w i) = true → False := by
    intro hq
    obtain ⟨a, b, hab, ha, hb⟩ := (hQ _).mp hq
    apply hy
    apply (hQ _).mpr
    have belongs (a : Fin n) (ha : upperPair w i a = true) : y a = true := by
      change decide (a = w ∨ a.val = i) = true at ha
      rcases of_decide_eq_true ha with ha | ha
      · simpa [ha] using hw
      · have hv : a = (⟨i,hi⟩ : Fin n) := Fin.ext ha
        simpa [hv] using hiy
    exact ⟨a,b,hab,belongs a ha,belongs b hb⟩
  have gain : ∀ r < C.gates.length, new (n+r) y = true → old (n+r) y ≠ true →
      ∃ k < m, ∃ w : Fin n, y w = true ∧
        old (n+r) (upperPair w (z k)) = true ∧ upperRegion n C u W k r := by
    intro r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      intro hr hn ho
      have hnOp := (hNew r hr y) ▸ hn
      have hreadGain : ∃ i ∈ (gateAt C r).inputs, rd r i y = true ∧ old i y ≠ true := by
        by_contra! hNo
        apply ho
        rw [hOld r hr y]
        exact upper_op_forward (hOp r hr) hNo hnOp
      obtain ⟨i, hi, hrd, hoi⟩ := hreadGain
      have fromRead : ∃ k < m, ∃ w : Fin n, y w = true ∧ n ≤ i ∧
          old i (upperPair w (z k)) = true ∧
          (r = T k ∨ upperRegion n C u W k r) := by
        rcases hRead r hr i hi y with ⟨k,hkm,hNRr,heq,hval⟩ | hval
        · have hp : P k y = true := hval ▸ hrd
          obtain ⟨w, hyw, hop⟩ := hP k y hp
          refine ⟨k,hkm,w,hyw,by omega,by simpa [heq] using hop,?_⟩
          rcases hNR k r hNRr with he | ⟨hor,hopr⟩
          · exact Or.inl he
          · have hlt : u k < r := by have := hBack r hr i hi; omega
            exact Or.inr ⟨hor,hopr,hCone hr hlt (by simpa [heq] using hi) (Or.inl rfl)⟩
        · have hnt : new i y = true := hval ▸ hrd
          by_cases hin : i<n
          · exfalso
            apply hoi
            rw [hOldInput i hin y]
            simpa [hNewInput i hin y] using hnt
          · let j := i-n
            have heq : i=n+j := by dsimp [j]; omega
            have hj : j<r := by have := hBack r hr i hi; omega
            have hmem : n+j ∈ (gateAt C r).inputs := by simpa [heq] using hi
            obtain ⟨k,hkm,w,hyw,hop,hreg⟩ :=
              ih j hj (by omega) (by rwa [←heq]) (by rwa [←heq])
            obtain ⟨hor,hoj,hcone⟩ := hreg
            refine ⟨k,hkm,w,hyw,by omega,by simpa [heq] using hop,?_⟩
            rcases (hIsol k hkm j (by omega) hor hoj hcone).2 r hr hmem with he | ⟨hor',hopr⟩
            · exact Or.inl he
            · exact Or.inr ⟨hor',hopr,hCone hr hj hmem (Or.inr hcone)⟩
      obtain ⟨k,hkm,w,hyw,hige,hipair,htop | hreg⟩ := fromRead
      · exfalso
        obtain ⟨hopT,hz,hinput,hbelow⟩ := hTop k hkm
        have hopr : (gateAt C r).op = GateOp.and := by simpa [htop] using hopT
        have hinput' : (gateAt C r).inputs = [W k,z k] ∨
            (gateAt C r).inputs = [z k,W k] := by simpa [htop] using hinput
        have hzm : z k ∈ (gateAt C r).inputs := by
          rcases hinput' with h | h <;> simp [h]
        have hnewZ : rd r (z k) y = true := by
          rw [hopr] at hnOp
          exact upper_and_true.mp hnOp (z k) hzm
        have hyz : y ⟨z k,hz⟩ = true := by
          rcases hRead r hr (z k) hzm y with ⟨k',_,_,hzbad,_⟩ | hen
          · omega
          · rwa [hen,hNewInput (z k) hz y] at hnewZ
        have hzi : i ≠ z k := by omega
        have hiW : i = W k := by
          rcases hinput' with hh | hh
          · have h := hi
            simp [hh] at h
            exact h.resolve_right hzi
          · have h := hi
            simp [hh] at h
            exact h.resolve_left hzi
        have hpairZ : old (z k) (upperPair w (z k)) = true := by
          rw [hOldInput (z k) hz]
          simp [upperPair]
        have hpairR : old (n+r) (upperPair w (z k)) = true := by
          rw [hOld r hr _,hopr]
          apply upper_and_true.mpr
          intro b hb
          have hb' : b=W k ∨ b=z k := by
            rcases hinput' with hh | hh
            · simpa [hh] using hb
            · simpa [hh,or_comm] using hb
          rcases hb' with rfl | rfl
          · simpa [hiW] using hipair
          · exact hpairZ
        apply hwitness w (z k) hz hyw hyz
        apply hbelow
        simpa [htop] using hpairR
      · refine ⟨k,hkm,w,hyw,?_,hreg⟩
        rw [hOld r hr _,hreg.2.1]
        exact upper_or_true.mpr ⟨i,hi,hipair⟩
  have hOutOld : old C.output y ≠ true := by simpa [hFun] using hy
  by_cases hraw : C.output<n
  · apply hOutOld
    rw [hOldInput C.output hraw y]
    simpa [hNewInput C.output hraw y] using hout
  · let r := C.output-n
    have hrEq : C.output=n+r := by dsimp [r]; omega
    by_cases hr : r<C.gates.length
    · obtain ⟨k,hkm,w,_,_,hor,hop,hcone⟩ :=
        gain r hr (by rwa [←hrEq]) (by rwa [←hrEq])
      exact (hIsol k hkm r hr hor hop hcone).1 hrEq
    · rw [hNewMissing C.output (by omega) y] at hout
      cases hout

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

private lemma lower_op (op : GateOp) (hs : op = .and ∨ op = .or)
    (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hs with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro ht i hi
    exact h i hi (ht i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, ht⟩
    exact ⟨i, hi, h i hi ht⟩

lemma lower {n : ℕ} {H : SimpleGraph (Fin n)} {qH : (Fin n → Bool) → Bool}
    {C : Circuit} {m : ℕ} {u T W z : ℕ → ℕ} {NR : ℕ → ℕ → Prop}
    {P : ℕ → (Fin n → Bool) → Bool}
    {old new : ℕ → (Fin n → Bool) → Bool}
    {rd : ℕ → ℕ → (Fin n → Bool) → Bool}
    (hEdge : ∀ y, qH y = true ↔ ∃ a b : Fin n, H.Adj a b ∧ y a = true ∧ y b = true)
    (hOps : ∀ r < C.gates.length, (gateAt C r).op = .and ∨ (gateAt C r).op = .or)
    (hBack : ReadsBack n C)
    (hCone : ∀ r < C.gates.length, ∀ i < r, n + i ∈ (gateAt C r).inputs →
      ∀ j, j = i ∨ InCone n C j i → InCone n C j r)
    (hOld : ∀ r < C.gates.length, ∀ x, old (n + r) x =
      (gateAt C r).op.eval ((gateAt C r).inputs.map (fun i => old i x)))
    (hNew : ∀ r < C.gates.length, ∀ x, new (n + r) x =
      (gateAt C r).op.eval ((gateAt C r).inputs.map (fun i => rd r i x)))
    (hRead : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, ∀ x,
      (∃ k < m, NR k r ∧ i = n + u k ∧ rd r i x = P k x) ∨ rd r i x = new i x)
    (hOldRaw : ∀ (i : Fin n) x, old i.val x = x i)
    (hNewRaw : ∀ (i : Fin n) x, new i.val x = x i)
    (hOldMissing : ∀ i, n + C.gates.length ≤ i → ∀ x, old i x = false)
    (hOldOut : ∀ x, old C.output x = qH x)
    (hNR : ∀ k r, NR k r → r = T k ∨ (OrReaches n C (W k) r ∧ (gateAt C r).op = .or))
    (hP : ∀ k x, P k x = decide
      (∃ w : Fin n, x w = true ∧ old (n + u k) (fun j : Fin n => decide (j = w ∨ j.val = z k)) = true))
    (hT : ∀ k < m, (gateAt C (T k)).op = .and ∧ z k < n ∧
      ((gateAt C (T k)).inputs = [W k, z k] ∨ (gateAt C (T k)).inputs = [z k, W k]))
    (hGuard : ∀ k < m, ∀ g < C.gates.length, OrReaches n C (W k) g →
      (gateAt C g).op = .or → InCone n C (u k) g → C.output ≠ n + g ∧
      ∀ r < C.gates.length, n + g ∈ (gateAt C r).inputs →
        r = T k ∨ (OrReaches n C (W k) r ∧ (gateAt C r).op = .or)) :
    ∀ y, qH y = true → new C.output y = true := by
  intro y hq
  obtain ⟨a, b, hab, ha, hb⟩ := (hEdge y).mp hq
  let x : Fin n → Bool := fun i => decide (i = a ∨ i = b)
  have hIncl : ∀ i, x i = true → y i = true := by
    intro i hi
    rcases of_decide_eq_true hi with rfl | rfl
    · exact ha
    · exact hb
  have hTop (r k : ℕ) (hr : r < C.gates.length) (hk : k < m)
      (hrEq : r = T k) (hf : old (z k) x = false) (ht : old (n + r) x = true) : False := by
    obtain ⟨hAnd, _, hIns⟩ := hT k hk
    have hMem : z k ∈ (gateAt C r).inputs := by
      rw [hrEq]
      rcases hIns with hin | hin <;> simp [hin]
    have hEval := hOld r hr x
    rw [ht, show (gateAt C r).op = GateOp.and from hrEq ▸ hAnd] at hEval
    have hAll : ∀ i ∈ (gateAt C r).inputs, old i x = true := by
      simpa only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
        using hEval.symm
    exact Bool.noConfusion ((hAll (z k) hMem).symm.trans hf)
  have hLoss : ∀ r < C.gates.length, old (n + r) x = true → new (n + r) y = false →
      ∃ k < m, old (z k) x = false ∧ OrReaches n C (W k) r ∧
        (gateAt C r).op = .or ∧ InCone n C (u k) r := by
    intro r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      intro hr hPrev hNow
      have hDiff : ∃ i ∈ (gateAt C r).inputs, old i x = true ∧ rd r i y = false := by
        by_contra hn
        have hMono : ∀ i ∈ (gateAt C r).inputs, old i x = true → rd r i y = true := by
          intro i hi ho
          cases hrd : rd r i y
          · exact (hn ⟨i, hi, ho, hrd⟩).elim
          · rfl
        have heq := lower_op _ (hOps r hr) _ _ _ hMono (by rwa [← hOld r hr x])
        rw [← hNew r hr y, hNow] at heq
        cases heq
      obtain ⟨i, hi, hiOld, hiNew⟩ := hDiff
      have hiLt := hBack r hr i hi
      rcases hRead r hr i hi y with ⟨k, hk, hkNR, hki, hrP⟩ | hrEq
      · have hzlt := (hT k hk).2.1
        have hOldZ : old (z k) x = false := by
          cases hzV : x ⟨z k, hzlt⟩ with
          | false => exact (hOldRaw ⟨z k, hzlt⟩ x).trans hzV
          | true =>
            have hActive : (⟨z k, hzlt⟩ : Fin n) = a ∨ (⟨z k, hzlt⟩ : Fin n) = b :=
              of_decide_eq_true hzV
            have hPair : ∃ w : Fin n, y w = true ∧
                x = fun j : Fin n => decide (j = w ∨ j.val = z k) := by
              rcases hActive with hza | hzb
              · have hz : z k = a.val := congrArg Fin.val hza
                refine ⟨b, hb, ?_⟩
                funext j
                simp [x, hz, Fin.val_inj, or_comm]
              · have hz : z k = b.val := congrArg Fin.val hzb
                refine ⟨a, ha, ?_⟩
                funext j
                simp [x, hz, Fin.val_inj]
            obtain ⟨w, hwy, hw⟩ := hPair
            have hPt : P k y = true := by
              rw [hP k y]
              exact decide_eq_true ⟨w, hwy, by rw [← hw, ← hki]; exact hiOld⟩
            rw [hrP, hPt] at hiNew
            cases hiNew
        rcases hNR k r hkNR with hrT | ⟨hOr, hOp⟩
        · exact (hTop r k hr hk hrT hOldZ hPrev).elim
        · have huLt : u k < r := by omega
          have huMem : n + u k ∈ (gateAt C r).inputs := by rwa [← hki]
          exact ⟨k, hk, hOldZ, hOr, hOp, hCone r hr (u k) huLt huMem (u k) (Or.inl rfl)⟩
      · rw [hrEq] at hiNew
        by_cases hiInput : i < n
        · have hrawOld := hOldRaw ⟨i, hiInput⟩ x
          have hrawNew := hNewRaw ⟨i, hiInput⟩ y
          have hy : y ⟨i, hiInput⟩ = true := hIncl _ (hrawOld.symm.trans hiOld)
          exact Bool.noConfusion (hy.symm.trans (hrawNew.symm.trans hiNew))
        · let j := i - n
          have heq : n + j = i := by dsimp [j]; omega
          have hj : j < r := by omega
          have hjMem : n + j ∈ (gateAt C r).inputs := by rwa [heq]
          obtain ⟨k, hk, hOldZ, hOr, hOp, hjCone⟩ :=
            ih j hj (by omega) (by rwa [heq]) (by rwa [heq])
          rcases (hGuard k hk j (by omega) hOr hOp hjCone).2 r hr hjMem with hrT | ⟨hrOr, hrOp⟩
          · exact (hTop r k hr hk hrT hOldZ hPrev).elim
          · exact ⟨k, hk, hOldZ, hrOr, hrOp, hCone r hr j hj hjMem (u k) (Or.inr hjCone)⟩
  have hx : qH x = true := (hEdge x).mpr ⟨a, b, hab, by simp [x], by simp [x]⟩
  have hOldOutT : old C.output x = true := (hOldOut x).trans hx
  cases hVal : new C.output y with
  | true => rfl
  | false =>
    by_cases hInput : C.output < n
    · have hrawOld := hOldRaw ⟨C.output, hInput⟩ x
      have hrawNew := hNewRaw ⟨C.output, hInput⟩ y
      have hy : y ⟨C.output, hInput⟩ = true := hIncl _ (hrawOld.symm.trans hOldOutT)
      exact Bool.noConfusion (hy.symm.trans (hrawNew.symm.trans hVal))
    · let r := C.output - n
      have hOut : n + r = C.output := by dsimp [r]; omega
      by_cases hr : r < C.gates.length
      · obtain ⟨k, hk, _, hOr, hOp, hCn⟩ := hLoss r hr (by rwa [hOut]) (by rwa [hOut])
        exact ((hGuard k hk r hr hOr hOp hCn).1 hOut.symm).elim
      · exact Bool.noConfusion (hOldOutT.symm.trans (hOldMissing C.output (by omega) x))

end PEqualNP.Outside.L_meta_3545

open PEqualNP.Outside.L_meta_3545
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.L_meta_3545 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 := by
  intro n H qH C m u T W z NR P G0 rho D hGraph hAO hEval hNR hP hT hGuard hIndependent _ hD hRho hAlt
  have hD' : D = rewriteCircuit n C G0 rho := hD
  subst D
  let D := rewriteCircuit n C G0 rho
  let old := wireVal n C
  let new := fun i => wireVal n D (shift n G0.length i)
  let rd := shiftedRead n G0.length D rho
  have hOld := wireReadBack hAO.2.1
  have hNew := rewrittenGate (n := n) (C := C) G0 rho
  have hOldInput (i : Fin n) (x : Fin n → Bool) : old i.val x = x i := wireRaw C i x
  have hNewInput (i : Fin n) (x : Fin n → Bool) : new i.val x = x i := by
    simpa only [new, shift, ite_eq_left i.isLt] using wireRaw D i x
  have hOldMissing (i : ℕ) (hi : n + C.gates.length ≤ i) (x : Fin n → Bool) : old i x = false :=
    wirePast C i hi x
  have hNewMissing (i : ℕ) (hi : n + C.gates.length ≤ i) (x : Fin n → Bool) : new i x = false := by
    change wireVal n D (shift n G0.length i) x = false
    apply wirePast
    change n + (rewriteCircuit n C G0 rho).gates.length ≤ _
    rw [rewrittenLength]
    simp only [shift, ite_eq_right (show ¬ i < n by omega)]
    omega
  have hNormal (r : ℕ) (hr : r < C.gates.length) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
      (h : ∀ k < m, ¬ (NR k r ∧ i = n + u k)) (x : Fin n → Bool) : rd r i x = new i x :=
    shifted_normal D rho (hAO.2.1 r hr i hi) (hRho r hr i hi h) x
  have hStable := stable old new rd hOld hNew (fun i x => (hNewInput i x).trans (hOldInput i x).symm)
    hNormal hAO.2.1 (coneRead n C)
  have hRead := rewrittenRead
    (n := n) (m := m) (C := C) (G0 := G0) (rho := rho) (u := u) (NR := NR) (P := P)
    hAO.2.1 hRho hAlt hStable
  have hOps (r : ℕ) (hr : r < C.gates.length) : (gateAt C r).op = .and ∨ (gateAt C r).op = .or :=
    hAO.1 (gateAt C r) (gateAt_mem hr)
  have hCone (r : ℕ) (hr : r < C.gates.length) (i : ℕ) (hi : i < r)
      (hm : n + i ∈ (gateAt C r).inputs) (j : ℕ) (hj : j = i ∨ InCone n C j i) :
      InCone n C j r := by
    obtain ⟨hDir, hTrans⟩ := coneRead n C i r hr (by omega) hm
    rcases hj with rfl | hj
    · exact hDir
    · exact hTrans j hj
  have hNR' (k r : ℕ) (h : NR k r) :=
    ((hNR k r).mp h).2.2
  have hu := upper (m := m) H qH C u T W z NR P old new rd
    hGraph hEval hOps hAO.2.1 hOld hNew hRead
    (fun i hi => hOldInput ⟨i, hi⟩) (fun i hi => hNewInput ⟨i, hi⟩) hNewMissing hNR'
    (fun k x h => of_decide_eq_true ((hP k x).symm.trans h))
    (fun k hk => by
      obtain ⟨_, _, hop, hz, hins, hbelow, _⟩ := hT k hk
      exact ⟨hop, hz, hins, hbelow⟩)
    hGuard (fun hr hi hm hj => hCone _ hr _ hi hm _ hj)
  have hl := lower (m := m) (u := u) (T := T) (W := W) (z := z) (NR := NR) (P := P)
    hGraph hOps hAO.2.1 hCone hOld hNew hRead hOldInput hNewInput hOldMissing hEval hNR' hP
    (fun k hk => by
      obtain ⟨_, _, hop, hz, hins, _⟩ := hT k hk
      exact ⟨hop, hz, hins⟩)
    hGuard
  intro x
  change new C.output x = qH x
  exact Bool.eq_iff_iff.2 ⟨hu x, hl x⟩
