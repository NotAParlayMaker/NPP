import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3545

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- The wire evaluation and cone recursion lemmas below follow L_meta_1878.
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
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
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


open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

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

def shift (n d w : ℕ) := if w < n then w else w + d

def changed (C : Circuit) (n : ℕ) (G : List Gate) (rho : ℕ → ℕ → ℕ) : Circuit :=
  ⟨G ++ C.gates.mapIdx (fun r g => ⟨g.op,g.inputs.map (rho r)⟩), shift n G.length C.output⟩

def v (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) := wireVal n C w x

lemma raw {n C x i} (hi : i < n) : v n C x i = x ⟨i,hi⟩ := by
  change val C (List.ofFn x) i = _
  rw [val_input (n := n) (by simp) hi]
  simp [List.getD_eq_getElem?_getD,hi]

lemma oldGate {n C x} (ao : IsAO2 n C) {r} (hr : r < C.gates.length) :
    v n C x (n+r) = (gateAt C r).op.eval ((gateAt C r).inputs.map (v n C x)) := by
  rw [show v n C x (n+r) = val C (List.ofFn x) (n+r) from rfl,val_gate (by simp) hr]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left (ao.2.1 r hr i hi)]
  rfl

def newPort (n : ℕ) (C : Circuit) (G : List Gate) (rho : ℕ → ℕ → ℕ) (x : Fin n → Bool) (r i : ℕ) :=
  if rho r i < n + G.length + r then v n (changed C n G rho) x (rho r i) else false

lemma newGate {n C G rho x r} (hr : r < C.gates.length) :
    v n (changed C n G rho) x (n+G.length+r) =
    (gateAt C r).op.eval ((gateAt C r).inputs.map (newPort n C G rho x r)) := by
  have hg : G.length+r < (changed C n G rho).gates.length := by simp [changed]; omega
  have eq : gateAt (changed C n G rho) (G.length+r) =
      ⟨(gateAt C r).op,(gateAt C r).inputs.map (rho r)⟩ := by
    rw [gateAt_eq hg,gateAt_eq hr]
    simp [changed,List.getElem_append_right]
  change val _ (List.ofFn x) _ = _
  rw [Nat.add_assoc,val_gate (by simp) hg,eq]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply,newPort,Nat.add_assoc]
  rfl

lemma base_mono {n C} (ao : IsAO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    v n C x w = true → v n C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · rw [raw hw,raw hw]; exact hxy _
    by_cases hr : w-n < C.gates.length
    · obtain ⟨r,rfl⟩ : ∃ r, w = n+r := ⟨w-n,by omega⟩
      have hr' : r < C.gates.length := by omega
      rw [oldGate ao hr',oldGate ao hr']
      apply opMono_imp _ (ao.1 _ (gateAt_mem hr'))
      intro i hi
      exact ih i (ao.2.1 _ hr' _ hi)
    · have e : val C (List.ofFn x) w = false := val_ge (n := n) (by simp) (by omega)
      exact fun h => Bool.noConfusion (e.symm.trans h)

def Bad (a b : Bool) := a = true ∧ b = false

lemma badPort (op : GateOp) (hop : op = .and ∨ op = .or) (inputs : List ℕ) (a b : ℕ → Bool)
    (h : Bad (op.eval (inputs.map a)) (op.eval (inputs.map b))) :
    ∃ i ∈ inputs, Bad (a i) (b i) := by
  by_contra! contra
  have good : ∀ i ∈ inputs, a i = true → b i = true := by
    intro i hi hai
    cases hb : b i
    · exact (contra i hi ⟨hai,hb⟩).elim
    · rfl
  exact Bool.noConfusion (h.2.symm.trans (opMono_imp op hop _ a b good h.1))

-- A difference must stay in the OR region of a pair whose center is inactive.
theorem confine {n m : ℕ} {C : Circuit} {u T : ℕ → ℕ} {zone : ℕ → ℕ → Prop}
    (ao : IsAO2 n C) (active : ℕ → Prop) (bad : ℕ → Prop)
    (top : ∀ k < m, bad (T k) → active k)
    (closed : ∀ k < m, ∀ j < C.gates.length, zone k j → InCone n C (u k) j →
      C.output ≠ n+j ∧ ∀ r < C.gates.length, n+j ∈ (gateAt C r).inputs → r = T k ∨ zone k r)
    (cause : ∀ r < C.gates.length, bad r →
      (∃ k < m, ¬ active k ∧ n+u k ∈ (gateAt C r).inputs ∧ (r = T k ∨ zone k r)) ∨
      (∃ j < r, n+j ∈ (gateAt C r).inputs ∧ bad j)) :
    ∀ r < C.gates.length, bad r →
      ∃ k < m, ¬active k ∧ zone k r ∧ InCone n C (u k) r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr hb
    rcases cause r hr hb with ⟨k,hk,off,port,loc⟩ | ⟨j,hj,port,bj⟩
    · have bound := ao.2.1 r hr _ port
      refine ⟨k,hk,off,loc.resolve_left (fun eq => off (top k hk (eq ▸ hb))),?_⟩
      exact (inCone_iff n C _ _).mpr ⟨hr,u k,by omega,port,Or.inl rfl⟩
    · obtain ⟨k,hk,off,loc,cone⟩ := ih j hj (by omega) bj
      have next := (closed k hk j (by omega) loc cone).2 r hr port
      exact ⟨k,hk,off,next.resolve_left (fun eq => off (top k hk (eq ▸ hb))),
        (inCone_iff n C _ _).mpr ⟨hr,j,hj,port,Or.inr cone⟩⟩

def mapped (n : ℕ) (C : Circuit) (G : List Gate) (rho : ℕ → ℕ → ℕ) (x : Fin n → Bool) (i : ℕ) :=
  v n (changed C n G rho) x (shift n G.length i)

lemma map_raw {n C G rho x i} (hi : i < n) : mapped n C G rho x i = x ⟨i,hi⟩ := by
  simpa [mapped,shift,hi] using (raw (C := changed C n G rho) (x := x) hi)

lemma map_gate {n C G rho x r} (hr : r < C.gates.length) :
    mapped n C G rho x (n+r) =
      (gateAt C r).op.eval ((gateAt C r).inputs.map (newPort n C G rho x r)) := by
  have eq : shift n G.length (n+r) = n+G.length+r := by simp [shift]; omega
  simpa only [mapped,eq] using (newGate (n := n) (G := G) (rho := rho) (x := x) hr)

lemma standardPort {n C G rho x r i} (back : i < n+r)
    (he : rho r i = shift n G.length i) :
    newPort n C G rho x r i = mapped n C G rho x i := by
  have bound : rho r i < n+G.length+r := by
    rw [he]
    unfold shift
    split <;> omega
  rw [newPort,ite_eq_left bound,he]
  rfl

lemma prefix_val {n C G rho x i} (hi : i < n+G.length) :
    v n (changed C n G rho) x i = v n (⟨G,0⟩ : Circuit) x i := by
  change val _ (List.ofFn x) i = val _ (List.ofFn x) i
  unfold val
  rw [wires_eq_foldl,wires_eq_foldl]
  change ((G ++ _).foldl stepWire (List.ofFn x)).getD i false =
    (G.foldl stepWire (List.ofFn x)).getD i false
  rw [List.foldl_append]
  apply foldl_getD_lt
  simpa [foldl_length] using hi

def safe (n m : ℕ) (C : Circuit) (NR : ℕ → ℕ → Prop) (g : ℕ) :=
  ∀ k < m, ∀ r, NR k r → r ≠ g ∧ ¬ InCone n C r g

lemma safe_eval {n m C G rho x} {NR : ℕ → ℕ → Prop} {u : ℕ → ℕ} (ao : IsAO2 n C)
    (standard : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs,
      (∀ k < m, ¬(NR k r ∧ i = n+u k)) → rho r i = shift n G.length i) :
    ∀ g < C.gates.length, safe n m C NR g →
      mapped n C G rho x (n+g) = v n C x (n+g) := by
  intro g
  induction g using Nat.strong_induction_on with
  | ind g ih =>
    intro hg hs
    rw [map_gate hg,oldGate ao hg]
    congr 1
    apply List.map_congr_left
    intro i hi
    have back := ao.2.1 g hg i hi
    have ns : ∀ k < m, ¬(NR k g ∧ i = n+u k) :=
      fun k hk h => (hs k hk g h.1).1 rfl
    rw [standardPort back (standard g hg i hi ns)]
    by_cases input : i < n
    · rw [map_raw input,raw input]
    · obtain ⟨j,rfl⟩ : ∃ j, i = n+j := ⟨i-n,by omega⟩
      apply ih j (by omega) (by omega)
      intro k hk r hr
      have no := (hs k hk r hr).2
      exact ⟨fun eq => no ((inCone_iff n C r g).mpr ⟨hg,j,by omega,hi,Or.inl eq⟩),
        fun h => no ((inCone_iff n C r g).mpr ⟨hg,j,by omega,hi,Or.inr h⟩)⟩

def discrepancy (reverse : Bool) (old new : Bool) := if reverse then Bad new old else Bad old new

def endpoint (reverse : Bool) (old new : Bool) := if reverse then new else old

def standardMap (n m : ℕ) (C : Circuit) (G : List Gate) (rho : ℕ → ℕ → ℕ)
    (NR : ℕ → ℕ → Prop) (u : ℕ → ℕ) :=
  ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs,
    (∀ k < m, ¬(NR k r ∧ i = n+u k)) → rho r i = shift n G.length i

def replacement (n m : ℕ) (C : Circuit) (G : List Gate) (rho : ℕ → ℕ → ℕ)
    (NR : ℕ → ℕ → Prop) (u : ℕ → ℕ) (P : ℕ → (Fin n → Bool) → Bool) :=
  ∀ r, ∀ k < m, NR k r →
    (rho r (n+u k) < n+G.length ∧ ∀ y, v n ⟨G,0⟩ y (rho r (n+u k)) = P k y) ∨
    (∃ g < r, rho r (n+u k) = n+G.length+g ∧ (∀ y, v n C y (n+g) = P k y) ∧ safe n m C NR g) ∨
    ((∀ y, P k y = false) ∧ n+G.length+r ≤ rho r (n+u k))

-- An earlier replacement gate retains its value when its entire cone avoids narrowed reads.
lemma replacement_eval {n m C G rho NR u P} (ao : IsAO2 n C)
    (std : standardMap n m C G rho NR u) (rep : replacement n m C G rho NR u P)
    (y : Fin n → Bool) {r k} (hr : r < C.gates.length) (hk : k < m) (nr : NR k r) :
    newPort n C G rho y r (n+u k) = P k y := by
  rcases rep r k hk nr with ⟨hp,hv⟩ | ⟨g,hg,he,hv,hs⟩ | ⟨hv,hi⟩
  · rw [newPort,ite_eq_left (by omega),prefix_val hp,hv]
  · have eq : shift n G.length (n+g) = n+G.length+g := by simp [shift]; omega
    have stable := safe_eval (x := y) ao std g (by omega) hs
    rw [mapped,eq] at stable
    rw [newPort,ite_eq_left (by omega),he,stable,hv]
  · rw [newPort,ite_eq_right (by omega),hv]

lemma new_raw_port {n m C G rho NR u} (std : standardMap n m C G rho NR u)
    (x : Fin n → Bool) {r i} (hr : r < C.gates.length)
    (hi : i ∈ (gateAt C r).inputs) (rawi : i < n) :
    newPort n C G rho x r i = x ⟨i,rawi⟩ := by
  have no : ∀ k < m, ¬(NR k r ∧ i = n+u k) := by
    rintro k _ ⟨_,he⟩
    omega
  rw [standardPort (by omega) (std r hr i hi no),map_raw rawi]

def region (n : ℕ) (C : Circuit) (W : ℕ → ℕ) (k r : ℕ) :=
  OrReaches n C (W k) r ∧ (gateAt C r).op = .or

lemma compare_outputs {n m C G rho NR u P} {T W z : ℕ → ℕ}
    (ao : IsAO2 n C) (std : standardMap n m C G rho NR u)
    (rep : replacement n m C G rho NR u P)
    (nrdef : ∀ k r, NR k r ↔ r < C.gates.length ∧ n+u k ∈ (gateAt C r).inputs ∧ (r=T k ∨ region n C W k r))
    (tops : ∀ k < m, T k < C.gates.length ∧ (gateAt C (T k)).op = .and ∧
      z k < n ∧ z k ∈ (gateAt C (T k)).inputs)
    (closed : ∀ k < m, ∀ j < C.gates.length, region n C W k j → InCone n C (u k) j →
      C.output ≠ n+j ∧ ∀ r < C.gates.length, n+j ∈ (gateAt C r).inputs → r=T k ∨ region n C W k r)
    (x y : Fin n → Bool) (rev : Bool)
    (input : ∀ i, ¬discrepancy rev (x i) (y i))
    (pair : ∀ k (hk : k < m), discrepancy rev (v n C x (n+u k)) (P k y) →
      endpoint rev (x ⟨z k,(tops k hk).2.2.1⟩) (y ⟨z k,(tops k hk).2.2.1⟩) = false) :
    ¬discrepancy rev (v n C x C.output) (mapped n C G rho y C.output) := by
  let bad := fun r => discrepancy rev (v n C x (n+r)) (mapped n C G rho y (n+r))
  let active := fun k => ∃ h : z k < n, endpoint rev (x ⟨z k,h⟩) (y ⟨z k,h⟩) = true
  have top (k) (hk : k < m) (hb : bad (T k)) : active k := by
    obtain ⟨ht,op,hz,hm⟩ := tops k hk
    refine ⟨hz,?_⟩
    unfold bad at hb
    rw [oldGate ao ht,map_gate ht,op] at hb
    have o : v n C x (z k) = x ⟨z k,hz⟩ := raw hz
    have p := new_raw_port std y ht hm hz
    cases rev <;> simp only [discrepancy,endpoint,Bool.false_eq_true,ite_false,ite_true,Bad] at hb ⊢
    · have h := hb.1
      simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at h
      exact o ▸ h _ hm
    · have h := hb.1
      simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at h
      exact p ▸ h _ hm
  have cause (r) (hr : r < C.gates.length) (hb : bad r) :
      (∃ k < m, ¬active k ∧ n+u k ∈ (gateAt C r).inputs ∧ (r=T k ∨ region n C W k r)) ∨
      ∃ j < r, n+j ∈ (gateAt C r).inputs ∧ bad j := by
    have ops := ao.1 _ (gateAt_mem hr)
    unfold bad at hb
    rw [oldGate ao hr,map_gate hr] at hb
    have ports : ∃ i ∈ (gateAt C r).inputs,
        discrepancy rev (v n C x i) (newPort n C G rho y r i) := by
      cases rev <;> exact badPort _ ops _ _ _ hb
    obtain ⟨i,hi,diff⟩ := ports
    by_cases special : ∃ k < m, NR k r ∧ i = n+u k
    · obtain ⟨k,hk,hn,rfl⟩ := special
      rw [replacement_eval ao std rep y hr hk hn] at diff
      have h := (nrdef k r).mp hn
      exact Or.inl ⟨k,hk,fun ⟨_,on⟩ => Bool.noConfusion ((pair k hk diff).symm.trans on),h.2⟩
    · have no : ∀ k < m, ¬(NR k r ∧ i = n+u k) := fun k hk h => special ⟨k,hk,h⟩
      have earlier := ao.2.1 r hr i hi
      rw [standardPort earlier (std r hr i hi no)] at diff
      by_cases h : i < n
      · rw [raw h,map_raw h] at diff
        exact (input _ diff).elim
      · obtain ⟨j,rfl⟩ : ∃ j, i=n+j := ⟨i-n,by omega⟩
        exact Or.inr ⟨j,by omega,hi,diff⟩
  intro hb
  by_cases hi : C.output < n
  · rw [raw hi,map_raw hi] at hb
    exact input _ hb
  obtain ⟨j,hej⟩ : ∃ j, C.output = n+j := ⟨C.output-n,by omega⟩
  rw [hej] at hb
  by_cases hj : j < C.gates.length
  · obtain ⟨k,hk,_,zone,cone⟩ := confine ao active bad top closed cause j hj hb
    exact (closed k hk j hj zone cone).1 hej
  · have eo : v n C x (n+j) = false := val_ge (n := n) (by simp) (by omega)
    have en : mapped n C G rho y (n+j) = false := by
      have eq : shift n G.length (n+j) = n+G.length+j := by simp [shift]; omega
      unfold mapped
      rw [eq]
      apply val_ge (n := n) (by simp)
      simp [changed]; omega
    rw [eo,en] at hb
    cases rev <;> simp [discrepancy,Bad] at hb

lemma false_of_ne {b : Bool} (h : b ≠ true) : b = false := by cases b <;> simp_all
lemma true_of_ne {b : Bool} (h : b ≠ false) : b = true := by cases b <;> simp_all

end PEqualNP.Outside.L_meta_3545
open PEqualNP.Outside.L_meta_3545 PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_3545 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 := by
  intro n H q C m u T W z NR P G rho D graph ao computes nrdef pdef facts hsealed _hind _hprefix hd std rep
  subst D
  have tops (k) (hk : k < m) : T k < C.gates.length ∧ (gateAt C (T k)).op = .and ∧
      z k < n ∧ z k ∈ (gateAt C (T k)).inputs := by
    obtain ⟨_,ht,hop,hz,inputs,_,_⟩ := facts k hk
    refine ⟨ht,hop,hz,?_⟩
    rcases inputs with e | e <;> simp [e]
  have closed (k) (hk : k < m) (j) (hj : j < C.gates.length) (loc : region n C W k j) :=
    hsealed k hk j hj loc.1 loc.2
  intro y
  change mapped n C G rho y C.output = q y
  -- Compare the new output with the old output on the same input.
  have upper : mapped n C G rho y C.output = true → q y = true := by
    intro on
    rw [← computes y]
    change v n C y C.output = true
    by_contra! off
    apply compare_outputs ao std rep nrdef tops closed y y true (fun i => by simp [discrepancy,Bad]) _ ⟨on,false_of_ne off⟩
    intro k hk diff
    let center : Fin n := ⟨z k,(tops k hk).2.2.1⟩
    change y center = false
    by_contra! hcenter
    change Bad (P k y) (v n C y (n+u k)) at diff
    have exists_w := diff.1
    rw [pdef k y] at exists_w
    obtain ⟨w,hw,hit⟩ := of_decide_eq_true exists_w
    have included (j : Fin n) :
        decide (j = w ∨ (j : ℕ) = z k) = true → y j = true := by
      intro h
      rcases of_decide_eq_true h with rfl | eq
      · exact hw
      · have e : j = center := Fin.ext eq
        exact e ▸ true_of_ne hcenter
    exact Bool.noConfusion (diff.2.symm.trans (base_mono ao _ y included _ hit))
  -- Compare an old two-vertex edge input with the new output on any input containing it.
  have lower : q y = true → mapped n C G rho y C.output = true := by
    intro hy
    obtain ⟨a,b,adj,ha,hb⟩ := (graph y).mp hy
    let x : Fin n → Bool := fun j => decide (j=a ∨ j=b)
    have le (j) (hj : x j = true) : y j = true := by
      rcases of_decide_eq_true hj with rfl | rfl
      · exact ha
      · exact hb
    have hx : q x = true := (graph x).mpr ⟨a,b,adj,by simp [x],by simp [x]⟩
    have old : v n C x C.output = true := (computes x).trans hx
    by_contra! off
    apply compare_outputs ao std rep nrdef tops closed x y false
      (fun i h => Bool.noConfusion (h.2.symm.trans (le i h.1))) _ ⟨old,false_of_ne off⟩
    intro k hk diff
    let center : Fin n := ⟨z k,(tops k hk).2.2.1⟩
    change x center = false
    by_contra! hcenter
    change Bad (v n C x (n+u k)) (P k y) at diff
    have coord (j : Fin n) : (j : ℕ) = z k ↔ j = center := ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    have e : center = a ∨ center = b := of_decide_eq_true (true_of_ne hcenter)
    have choice : ∃ w : Fin n, y w = true ∧
        (fun j : Fin n => decide (j = w ∨ (j : ℕ) = z k)) = x := by
      rcases e with e | e
      · exact ⟨b,hb,funext (fun j => by simp only [coord,e,x,or_comm])⟩
      · exact ⟨a,ha,funext (fun j => by simp only [coord,e,x])⟩
    obtain ⟨w,hw,eq⟩ := choice
    have hp : P k y = true := by
      rw [pdef]
      apply decide_eq_true
      exact ⟨w,hw,eq ▸ diff.1⟩
    exact Bool.noConfusion (diff.2.symm.trans hp)
  cases hq : q y with
  | true => exact lower hq
  | false =>
    cases he : mapped n C G rho y C.output with
    | false => rfl
    | true => exact Bool.noConfusion (hq.symm.trans (upper he))
