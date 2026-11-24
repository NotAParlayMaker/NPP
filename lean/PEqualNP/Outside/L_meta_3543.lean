import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3543

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

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

open PEqualNP.EdgeOwnership

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

/-! The generic relation lemma: two runs of the gate list of `C`, each with its narrowed reads
replaced by a value of its own. -/

lemma gen (n u : ℕ) (C : Circuit) (S : ℕ → Prop) (R : Bool → Bool → Prop) (hR : OpMono R)
    (hRf : R false false)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (v1 v2 a1 a2 : ℕ → Bool) (f1 f2 : ℕ → ℕ → Bool)
    (h1 : ∀ r < C.gates.length, v1 (n + r) = (gateAt C r).op.eval ((gateAt C r).inputs.map (f1 r)))
    (h2 : ∀ r < C.gates.length, v2 (n + r) = (gateAt C r).op.eval ((gateAt C r).inputs.map (f2 r)))
    (hf1 : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, (S r ∧ i = n + u → f1 r i = a1 r) ∧
      (¬ (S r ∧ i = n + u) → f1 r i = if i < n + r then v1 i else false))
    (hf2 : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, (S r ∧ i = n + u → f2 r i = a2 r) ∧
      (¬ (S r ∧ i = n + u) → f2 r i = if i < n + r then v2 i else false))
    (hin : ∀ i < n, R (v1 i) (v2 i))
    (ha : ∀ r < C.gates.length, S r → (∀ h < r, R (v1 (n + h)) (v2 (n + h))) → R (a1 r) (a2 r)) :
    ∀ r < C.gates.length, R (v1 (n + r)) (v2 (n + r)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro hr
  rw [h1 r hr, h2 r hr]
  refine hR _ (hops r hr) _ _ _ (fun i hi => ?_)
  by_cases hs : S r ∧ i = n + u
  · rw [(hf1 r hr i hi).1 hs, (hf2 r hr i hi).1 hs]
    exact ha r hr hs.1 (fun h hh => ih h hh (by omega))
  · rw [(hf1 r hr i hi).2 hs, (hf2 r hr i hi).2 hs]
    by_cases hlt : i < n + r
    · rw [if_pos hlt, if_pos hlt]
      by_cases hn : i < n
      · exact hin i hn
      · obtain ⟨h, rfl⟩ : ∃ h, i = n + h := ⟨i - n, by omega⟩
        exact ih h (by omega) (by omega)
    · rw [if_neg hlt, if_neg hlt]; exact hRf

lemma all_wires (n len : ℕ) (R : Bool → Bool → Prop) (hRf : R false false) (v1 v2 : ℕ → Bool)
    (hin : ∀ i < n, R (v1 i) (v2 i)) (hg : ∀ r < len, R (v1 (n + r)) (v2 (n + r)))
    (hb1 : ∀ i, n + len ≤ i → v1 i = false) (hb2 : ∀ i, n + len ≤ i → v2 i = false) :
    ∀ i, R (v1 i) (v2 i) := by
  intro i
  by_cases h1 : i < n
  · exact hin i h1
  by_cases h2 : i < n + len
  · obtain ⟨r, rfl⟩ : ∃ r, i = n + r := ⟨i - n, by omega⟩
    exact hg r (by omega)
  · rw [hb1 i (by omega), hb2 i (by omega)]; exact hRf

lemma gen_all (n u : ℕ) (C : Circuit) (S : ℕ → Prop)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (v1 v2 a1 a2 : ℕ → Bool) (f1 f2 : ℕ → ℕ → Bool)
    (h1 : ∀ r < C.gates.length, v1 (n + r) = (gateAt C r).op.eval ((gateAt C r).inputs.map (f1 r)))
    (h2 : ∀ r < C.gates.length, v2 (n + r) = (gateAt C r).op.eval ((gateAt C r).inputs.map (f2 r)))
    (hf1 : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, (S r ∧ i = n + u → f1 r i = a1 r) ∧
      (¬ (S r ∧ i = n + u) → f1 r i = if i < n + r then v1 i else false))
    (hf2 : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, (S r ∧ i = n + u → f2 r i = a2 r) ∧
      (¬ (S r ∧ i = n + u) → f2 r i = if i < n + r then v2 i else false))
    (hin : ∀ i < n, v1 i = true → v2 i = true)
    (ha : ∀ r < C.gates.length, S r → (∀ h < r, v1 (n + h) = true → v2 (n + h) = true) →
      a1 r = true → a2 r = true)
    (hb1 : ∀ i, n + C.gates.length ≤ i → v1 i = false)
    (hb2 : ∀ i, n + C.gates.length ≤ i → v2 i = false) :
    ∀ i, v1 i = true → v2 i = true :=
  all_wires n C.gates.length (fun a b => a = true → b = true) (fun h => h) v1 v2 hin
    (gen n u C S _ opMono_imp (fun h => h) hops v1 v2 a1 a2 f1 f2 h1 h2 hf1 hf2 hin ha) hb1 hb2

def shf (n L i : ℕ) : ℕ := if i < n then i else i + L

def cv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool := val C (List.ofFn x) i

def ev (n L : ℕ) (D : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool := val D (List.ofFn x) (shf n L i)

def fc (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r i : ℕ) : Bool :=
  if i < n + r then cv n C x i else false

def fd (n L : ℕ) (D : Circuit) (rho : ℕ → ℕ → ℕ) (x : Fin n → Bool) (r i : ℕ) : Bool :=
  if rho r i < n + L + r then val D (List.ofFn x) (rho r i) else false

lemma c_run (n u : ℕ) (C : Circuit) (hRB : ReadsBack n C) (S : ℕ → Prop) (x : Fin n → Bool) :
    (∀ r < C.gates.length, cv n C x (n + r) =
      (gateAt C r).op.eval ((gateAt C r).inputs.map (fc n C x r))) ∧
    (∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs,
      (S r ∧ i = n + u → fc n C x r i = cv n C x (n + u)) ∧
      (¬ (S r ∧ i = n + u) → fc n C x r i = if i < n + r then cv n C x i else false)) := by
  refine ⟨fun r hr => ?_, fun r hr i hi => ⟨fun h => ?_, fun _ => rfl⟩⟩
  · exact val_gate (n := n) (by simp) hr
  · rw [← h.2]; unfold fc; rw [if_pos (hRB r hr i hi)]

lemma d_run (n u : ℕ) (C D : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ)
    (hDg : D.gates = G0 ++ C.gates.mapIdx (fun r7 g7 =>
      ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : Gate)))
    (S : ℕ → Prop)
    (hrho : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, ¬ (S r ∧ i = n + u) →
      rho r i = if i < n then i else i + G0.length) (x : Fin n → Bool) :
    (∀ r < C.gates.length, ev n G0.length D x (n + r) =
      (gateAt C r).op.eval ((gateAt C r).inputs.map (fd n G0.length D rho x r))) ∧
    (∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs,
      (S r ∧ i = n + u → fd n G0.length D rho x r i = fd n G0.length D rho x r (n + u)) ∧
      (¬ (S r ∧ i = n + u) → fd n G0.length D rho x r i =
        if i < n + r then ev n G0.length D x i else false)) := by
  refine ⟨fun r hr => ?_, fun r hr i hi => ⟨fun h => by rw [h.2], fun h => ?_⟩⟩
  · have hj : G0.length + r < D.gates.length := by rw [hDg]; simp; omega
    have hg : gateAt D (G0.length + r) =
        ⟨(gateAt C r).op, (gateAt C r).inputs.map (fun i7 => rho r i7)⟩ := by
      rw [gateAt_eq hj, gateAt_eq hr]
      simp only [hDg]
      rw [List.getElem_append_right (by omega)]
      simp
    have := val_gate (C := D) (n := n) (x := List.ofFn x) (by simp) hj
    rw [hg] at this
    unfold ev shf
    rw [if_neg (by omega)]
    have e : n + r + G0.length = n + (G0.length + r) := by omega
    rw [e, this, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, fd]
    rw [show n + (G0.length + r) = n + G0.length + r by omega]
  · unfold fd ev shf
    rw [hrho r hr i hi h]
    by_cases hn : i < n
    · rw [if_pos hn, if_pos (by omega), if_pos (by omega)]
    · rw [if_neg hn]
      by_cases hlt : i < n + r
      · rw [if_pos (by omega), if_pos hlt]
      · rw [if_neg (by omega), if_neg hlt]

lemma d_pre (n : ℕ) (C D : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ)
    (hDg : D.gates = G0 ++ C.gates.mapIdx (fun r7 g7 =>
      ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : Gate)))
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + G0.length) :
    val D (List.ofFn x) w = val (⟨G0, 0⟩ : Circuit) (List.ofFn x) w := by
  unfold val
  rw [wires_eq_foldl, wires_eq_foldl, hDg, List.foldl_append]
  apply foldl_getD_lt
  rw [foldl_length]
  simp
  omega

lemma and_eval_false (l : List ℕ) (f : ℕ → Bool) (z : ℕ) (hz : z ∈ l) (hf : f z = false) :
    GateOp.and.eval (l.map f) = false := by
  simp only [GateOp.eval]
  rw [Bool.eq_false_iff]
  intro h
  rw [List.all_eq_true] at h
  have := h (f z) (List.mem_map_of_mem hz)
  simp [hf] at this

open PEqualNP.CleanedNonEdge in
theorem core (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C D : Circuit)
    (u T W z : ℕ) (S : ℕ → Prop) (P : (Fin n → Bool) → Bool) (G0 : List Gate)
    (rho : ℕ → ℕ → ℕ)
    (hq : ∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hRB : ReadsBack n C)
    (hC : ∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1)
    (hS : ∀ r, S r → r < C.gates.length ∧ n + u ∈ (gateAt C r).inputs ∧
      (r = T ∨ (OrReaches n C W r ∧ (gateAt C r).op = GateOp.or)))
    (hP : ∀ y2 : Fin n → Bool, P y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧
      val C (List.ofFn (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z))) (n + u) = true))
    (hu : u < C.gates.length) (hT : T < C.gates.length) (hTop : (gateAt C T).op = GateOp.and)
    (hz : z < n) (hTin : z ∈ (gateAt C T).inputs)
    (h3 : ∀ g < C.gates.length, OrReaches n C W g → (gateAt C g).op = GateOp.or →
      InCone n C u g → C.output ≠ n + g ∧ ∀ r < C.gates.length, n + g ∈ (gateAt C r).inputs →
        r = T ∨ (OrReaches n C W r ∧ (gateAt C r).op = GateOp.or))
    (hDg : D.gates = G0 ++ C.gates.mapIdx (fun r7 g7 =>
      ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : Gate)))
    (hDo : D.output = if C.output < n then C.output else C.output + G0.length)
    (hrho : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, ¬ (S r ∧ i = n + u) →
      rho r i = if i < n then i else i + G0.length)
    (h9 : ∀ r, S r →
      (rho r (n + u) < n + G0.length ∧
        ∀ y9 : Fin n → Bool, val (⟨G0, 0⟩ : Circuit) (List.ofFn y9) (rho r (n + u)) = P y9) ∨
      (∃ g9 < r, rho r (n + u) = n + G0.length + g9 ∧
        ∀ y10 : Fin n → Bool, val C (List.ofFn y10) (n + g9) = P y10) ∨
      ((∀ y11 : Fin n → Bool, P y11 = false) ∧ n + G0.length + r ≤ rho r (n + u))) :
    ∀ y : Fin n → Bool, D.eval (List.ofFn y) = qH y := by
  intro y
  have hDlen : D.gates.length = G0.length + C.gates.length := by rw [hDg]; simp
  have hCr := fun x => c_run n u C hRB S x
  have hDr := fun x => d_run n u C D G0 rho hDg S hrho x
  have inC : ∀ (x : Fin n → Bool) (i : ℕ) (hi : i < n), cv n C x i = x ⟨i, hi⟩ := by
    intro x i hi
    unfold cv
    rw [val_input (n := n) (by simp) hi]
    simp [List.getD_eq_getElem?_getD, hi]
  have inD : ∀ (x : Fin n → Bool) (i : ℕ) (hi : i < n), ev n G0.length D x i = x ⟨i, hi⟩ := by
    intro x i hi
    unfold ev shf
    rw [if_pos hi, val_input (n := n) (by simp) hi]
    simp [List.getD_eq_getElem?_getD, hi]
  have beC : ∀ (x : Fin n → Bool) (i : ℕ), n + C.gates.length ≤ i → cv n C x i = false := by
    intro x i hi
    exact val_ge (n := n) (by simp) hi
  have beD : ∀ (x : Fin n → Bool) (i : ℕ), n + C.gates.length ≤ i →
      ev n G0.length D x i = false := by
    intro x i hi
    unfold ev shf
    rw [if_neg (by omega)]
    apply val_ge (n := n) (by simp)
    rw [hDlen]
    omega
  have oD : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = ev n G0.length D x C.output := by
    intro x
    show val D (List.ofFn x) D.output = _
    rw [hDo]
    rfl
  have hα : ∀ r, S r →
      (∀ x, fd n G0.length D rho x r (n + u) = P x) ∨
      (∃ g < r, (∀ x, fd n G0.length D rho x r (n + u) = ev n G0.length D x (n + g)) ∧
        ∀ x, cv n C x (n + g) = P x) ∨
      ((∀ x, P x = false) ∧ ∀ x, fd n G0.length D rho x r (n + u) = false) := by
    intro r hs
    rcases h9 r hs with ⟨h1, h2⟩ | ⟨g, hg, h1, h2⟩ | ⟨h1, h2⟩
    · left
      intro x
      unfold fd
      rw [if_pos (by omega), d_pre n C D G0 rho hDg x _ h1, h2]
    · right; left
      refine ⟨g, hg, fun x => ?_, fun x => h2 x⟩
      unfold fd ev shf
      rw [h1, if_pos (by omega), if_neg (by omega)]
      rw [show n + G0.length + g = n + g + G0.length by omega]
    · right; right
      refine ⟨h1, fun x => ?_⟩
      unfold fd
      rw [if_neg (by omega)]
  have Cmono : ∀ x1 x2 : Fin n → Bool, (∀ j, x1 j = true → x2 j = true) →
      ∀ i, cv n C x1 i = true → cv n C x2 i = true := by
    intro x1 x2 hle
    have A1 := c_run n u C hRB (fun _ => False) x1
    have A2 := c_run n u C hRB (fun _ => False) x2
    refine gen_all n u C (fun _ => False) hops (cv n C x1) (cv n C x2)
      (fun _ => cv n C x1 (n + u)) (fun _ => cv n C x2 (n + u)) (fc n C x1) (fc n C x2)
      A1.1 A2.1 A1.2 A2.2 ?_ ?_ (beC x1) (beC x2)
    · intro i hi h
      rw [inC x2 i hi]; rw [inC x1 i hi] at h; exact hle _ h
    · intro r _ hs; exact hs.elim
  have Pmono : ∀ x1 x2 : Fin n → Bool, (∀ j, x1 j = true → x2 j = true) →
      P x1 = true → P x2 = true := by
    intro x1 x2 hle h
    rw [hP] at h ⊢
    simp only [decide_eq_true_eq] at h ⊢
    obtain ⟨w, hw, hv⟩ := h
    exact ⟨w, hle w hw, hv⟩
  have PleU : ∀ x : Fin n → Bool, x ⟨z, hz⟩ = true → P x = true → cv n C x (n + u) = true := by
    intro x hzx h
    rw [hP] at h
    simp only [decide_eq_true_eq] at h
    obtain ⟨w, hw, hv⟩ := h
    refine Cmono _ x ?_ (n + u) hv
    intro j hj
    simp only [decide_eq_true_eq] at hj
    rcases hj with rfl | hj
    · exact hw
    · have : j = ⟨z, hz⟩ := Fin.ext hj
      rw [this]; exact hzx
  have EQ0 : ∀ x : Fin n → Bool, x ⟨z, hz⟩ = false →
      ev n G0.length D x C.output = cv n C x C.output := by
    intro x hx0
    have key : ∀ r < C.gates.length,
        ¬ (OrReaches n C W r ∧ (gateAt C r).op = GateOp.or ∧ InCone n C u r) →
        ev n G0.length D x (n + r) = cv n C x (n + r) := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
      intro hr hO
      rw [(hDr x).1 r hr, (hCr x).1 r hr]
      by_cases hrT : r = T
      · have hz' : z ∈ (gateAt C r).inputs := hrT ▸ hTin
        have hop : (gateAt C r).op = GateOp.and := hrT ▸ hTop
        have hns : ¬ (S r ∧ z = n + u) := fun h => by omega
        have hfz : fd n G0.length D rho x r z = false := by
          rw [((hDr x).2 r hr z hz').2 hns, if_pos (by omega), inD x z hz]; exact hx0
        have hcz : fc n C x r z = false := by
          unfold fc; rw [if_pos (by omega), inC x z hz]; exact hx0
        rw [hop, and_eval_false _ _ z hz' hfz, and_eval_false _ _ z hz' hcz]
      · congr 1
        apply List.map_congr_left
        intro i hi
        have hns : ¬ (S r ∧ i = n + u) := by
          rintro ⟨hs, rfl⟩
          obtain ⟨_, _, hor⟩ := hS r hs
          rcases hor with h | ⟨h1, h2⟩
          · exact hrT h
          · have hlt := hRB r hr _ hi
            exact hO ⟨h1, h2, (inCone_iff n C u r).2 ⟨hr, u, by omega, hi, Or.inl rfl⟩⟩
        rw [((hDr x).2 r hr i hi).2 hns]
        unfold fc
        by_cases hlt : i < n + r
        · rw [if_pos hlt, if_pos hlt]
          by_cases hn : i < n
          · rw [inD x i hn, inC x i hn]
          · obtain ⟨h, rfl⟩ : ∃ h, i = n + h := ⟨i - n, by omega⟩
            apply ih h (by omega) (by omega)
            rintro ⟨h1, h2, h4⟩
            rcases (h3 h (by omega) h1 h2 h4).2 r hr hi with h5 | ⟨h5, h6⟩
            · exact hrT h5
            · exact hO ⟨h5, h6, (inCone_iff n C u r).2 ⟨hr, h, by omega, hi, Or.inr h4⟩⟩
        · rw [if_neg hlt, if_neg hlt]
    by_cases ho : C.output < n
    · rw [inD x _ ho, inC x _ ho]
    by_cases ho2 : C.output < n + C.gates.length
    · obtain ⟨g, hg⟩ : ∃ g, C.output = n + g := ⟨C.output - n, by omega⟩
      rw [hg]
      apply key g (by omega)
      intro hO
      exact (h3 g (by omega) hO.1 hO.2.1 hO.2.2).1 hg
    · rw [beD x _ (by omega), beC x _ (by omega)]
  rw [oD, ← hC y]
  show ev n G0.length D y C.output = cv n C y C.output
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hd
    by_cases hzy : y ⟨z, hz⟩ = true
    · refine gen_all n u C S hops (ev n G0.length D y) (cv n C y)
        (fun r => fd n G0.length D rho y r (n + u)) (fun _ => cv n C y (n + u))
        (fd n G0.length D rho y) (fc n C y) (hDr y).1 (hCr y).1 (hDr y).2 (hCr y).2 ?_ ?_
        (beD y) (beC y) _ hd
      · intro i hi h
        rw [inC y i hi]; rw [inD y i hi] at h; exact h
      · intro r _ hs ih
        rcases hα r hs with h | ⟨g, hg, h1, h2⟩ | ⟨h1, h2⟩
        · rw [h y]; exact PleU y hzy
        · rw [h1 y]
          intro hh
          have := ih g hg hh
          rw [h2 y] at this
          exact PleU y hzy this
        · rw [h2 y]; intro hh; cases hh
    · have hz0 : y ⟨z, hz⟩ = false := by simpa using hzy
      rw [EQ0 y hz0] at hd
      exact hd
  · intro hc
    have hq0 : qH y = true := by rw [← hC y]; exact hc
    obtain ⟨a, b, hab, ha, hb⟩ := (hq y).1 hq0
    let x1 : Fin n → Bool := fun j => decide (j = a ∨ j = b)
    have hq1 : cv n C x1 C.output = true := by
      show C.eval (List.ofFn x1) = true
      rw [hC x1]
      exact (hq x1).2 ⟨a, b, hab, by simp [x1], by simp [x1]⟩
    have hle : ∀ j, x1 j = true → y j = true := by
      intro j hj
      simp only [x1, decide_eq_true_eq] at hj
      rcases hj with rfl | rfl
      · exact ha
      · exact hb
    by_cases hzab : (a : ℕ) = z ∨ (b : ℕ) = z
    · have PeqU : cv n C x1 (n + u) = true → P x1 = true := by
        intro hh
        rw [hP]
        simp only [decide_eq_true_eq]
        rcases hzab with hza | hzb
        · refine ⟨b, by simp [x1], ?_⟩
          have : (fun j : Fin n => decide (j = b ∨ (j : ℕ) = z)) = x1 := by
            funext j
            have e : ((j : ℕ) = z) ↔ j = a := by rw [Fin.ext_iff, hza]
            apply Bool.eq_iff_iff.mpr
            simp only [x1, decide_eq_true_eq]
            rw [e]
            tauto
          rw [this]; exact hh
        · refine ⟨a, by simp [x1], ?_⟩
          have : (fun j : Fin n => decide (j = a ∨ (j : ℕ) = z)) = x1 := by
            funext j
            have e : ((j : ℕ) = z) ↔ j = b := by rw [Fin.ext_iff, hzb]
            apply Bool.eq_iff_iff.mpr
            simp only [x1, decide_eq_true_eq]
            rw [e]
          rw [this]; exact hh
      refine gen_all n u C S hops (cv n C x1) (ev n G0.length D y)
        (fun _ => cv n C x1 (n + u)) (fun r => fd n G0.length D rho y r (n + u))
        (fc n C x1) (fd n G0.length D rho y) (hCr x1).1 (hDr y).1 (hCr x1).2 (hDr y).2 ?_ ?_
        (beC x1) (beD y) _ hq1
      · intro i hi h
        rw [inD y i hi]; rw [inC x1 i hi] at h; exact hle _ h
      · intro r _ hs ih
        rcases hα r hs with h | ⟨g, hg, h1, h2⟩ | ⟨h1, h2⟩
        · rw [h y]; intro hh; exact Pmono x1 y hle (PeqU hh)
        · rw [h1 y]
          intro hh
          apply ih g hg
          rw [h2 x1]
          exact PeqU hh
        · rw [h2 y]
          intro hh
          have := PeqU hh
          rw [h1 x1] at this
          cases this
    · have hz1 : x1 ⟨z, hz⟩ = false := by
        simp only [x1, decide_eq_false_iff_not, not_or]
        exact ⟨fun h => hzab (Or.inl (by rw [← h])), fun h => hzab (Or.inr (by rw [← h]))⟩
      have hd1 : ev n G0.length D x1 C.output = true := by rw [EQ0 x1 hz1]; exact hq1
      refine gen_all n u C S hops (ev n G0.length D x1) (ev n G0.length D y)
        (fun r => fd n G0.length D rho x1 r (n + u)) (fun r => fd n G0.length D rho y r (n + u))
        (fd n G0.length D rho x1) (fd n G0.length D rho y) (hDr x1).1 (hDr y).1 (hDr x1).2
        (hDr y).2 ?_ ?_ (beD x1) (beD y) _ hd1
      · intro i hi h
        rw [inD y i hi]; rw [inD x1 i hi] at h; exact hle _ h
      · intro r _ hs ih
        rcases hα r hs with h | ⟨g, hg, h1, h2⟩ | ⟨h1, h2⟩
        · rw [h x1, h y]; exact Pmono x1 y hle
        · rw [h1 x1, h1 y]; exact ih g hg
        · rw [h2 x1]; intro hh; cases hh

end PEqualNP.Outside.L_meta_3543

open PEqualNP.Outside.L_meta_3543 in
theorem PEqualNP.Outside.L_meta_3543 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → m = 1 → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 := by
  intro n H qH C m u T W z NR P G0 rho D hq hAO hC hNR hP hk2 hk3 _ _ hD h8 h9 hm
  subst hm
  have hAO' := hAO
  unfold PEqualNP.TopForm.IsAO2 at hAO'
  obtain ⟨hu, hT, hTop, hz, hTin, _, _⟩ := hk2 0 (by omega)
  have hops : ∀ r < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C r).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C r).op = PEqualNP.CircuitLowerBounds.GateOp.or :=
    fun r hr => hAO'.1 _ (gateAt_mem hr)
  have hzT : z 0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T 0)).inputs := by
    rcases hTin with h | h <;> rw [h] <;> simp
  refine core n H qH C D (u 0) (T 0) (W 0) (z 0) (NR 0) (P 0) G0 rho hq hops hAO'.2.1 hC
    (fun r h => (hNR 0 r).1 h) (fun y => hP 0 y) hu hT hTop hz hzT
    (fun g hg h1 h2 h4 => hk3 0 (by omega) g hg h1 h2 h4) (by subst hD; rfl) (by subst hD; rfl)
    (fun r hr i hi hns => h8 r hr i hi (fun k hk => by obtain rfl : k = 0 := (by omega); exact hns))
    ?_
  intro r hs
  rcases h9 r 0 (by omega) hs with ⟨h1, h2⟩ | ⟨g, hg, h1, h2, _⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, fun y => h2 y⟩
  · exact Or.inr (Or.inl ⟨g, hg, h1, fun y => h2 y⟩)
  · exact Or.inr (Or.inr ⟨h1, h2⟩)
