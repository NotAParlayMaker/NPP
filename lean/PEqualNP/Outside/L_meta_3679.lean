import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3679

-- The witness starts from the fourteen Boolean sums in Ingo Wegener, The Complexity
-- of Boolean Functions, chapter 6, theorem 6.1, attributed there to Tarjan.
-- Each row receives a private left neighbor and a right selector.

namespace TarjanWitness

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover


-- Each pair is ordered from the 25 left vertices to the 14 selectors.
def edges : List (Fin 39 × Fin 39) :=
  [(0, 25), (9, 25), (11, 25),
   (1, 26), (10, 26), (12, 26),
   (2, 27), (9, 27), (13, 27),
   (3, 28), (10, 28), (14, 28),
   (6, 29), (9, 29), (15, 29),
   (6, 30), (7, 30), (9, 30), (16, 30),
   (6, 31), (7, 31), (8, 31), (9, 31), (17, 31),
   (6, 32), (10, 32), (18, 32),
   (6, 33), (7, 33), (10, 33), (19, 33),
   (6, 34), (7, 34), (8, 34), (10, 34), (20, 34),
   (0, 35), (4, 35), (6, 35), (7, 35), (8, 35), (9, 35), (21, 35),
   (1, 36), (4, 36), (6, 36), (7, 36), (8, 36), (10, 36), (22, 36),
   (2, 37), (5, 37), (6, 37), (7, 37), (8, 37), (9, 37), (23, 37),
   (3, 38), (5, 38), (6, 38), (7, 38), (8, 38), (10, 38), (24, 38)]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem separated : ∀ e ∈ edges, e.1.val < 25 ∧ 25 ≤ e.2.val := by
  have h : edges.all (fun e => decide (e.1.val < 25 ∧ 25 ≤ e.2.val)) = true := by decide
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

def graph : SimpleGraph (Fin 39) where
  Adj u v := (u, v) ∈ edges ∨ (v, u) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i h => by
    change (i, i) ∈ edges ∨ (i, i) ∈ edges at h
    have ⟨hl, hr⟩ := separated (i, i) (h.elim id id)
    exact (Nat.not_le_of_lt hl) hr⟩

instance : DecidableRel graph.Adj := fun u v =>
  inferInstanceAs (Decidable ((u, v) ∈ edges ∨ (v, u) ∈ edges))

def side (i : Fin 39) := decide (25 ≤ i.val)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem bipartite (u v) (h : graph.Adj u v) : side u ≠ side v := by
  rcases h with h | h
  · obtain ⟨hl, hr⟩ := separated (u, v) h
    change _ < 25 at hl
    change 25 ≤ _ at hr
    simp [side, Nat.not_le_of_lt hl, hr]
  · obtain ⟨hl, hr⟩ := separated (v, u) h
    change _ < 25 at hl
    change 25 ≤ _ at hr
    simp [side, Nat.not_le_of_lt hl, hr]

def circuit : Circuit :=
  ⟨[⟨.or, [0, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [3, 10]⟩,
    ⟨.or, [6, 9]⟩, ⟨.or, [7, 43]⟩, ⟨.or, [8, 44]⟩, ⟨.or, [6, 10]⟩,
    ⟨.or, [7, 46]⟩, ⟨.or, [8, 47]⟩, ⟨.and, [45, 48]⟩, ⟨.or, [49, 4]⟩,
    ⟨.or, [49, 5]⟩, ⟨.or, [39, 50]⟩, ⟨.or, [40, 50]⟩, ⟨.or, [41, 51]⟩,
    ⟨.or, [42, 51]⟩, ⟨.or, [39, 11]⟩, ⟨.and, [56, 25]⟩, ⟨.or, [40, 12]⟩,
    ⟨.and, [58, 26]⟩, ⟨.or, [41, 13]⟩, ⟨.and, [60, 27]⟩, ⟨.or, [42, 14]⟩,
    ⟨.and, [62, 28]⟩, ⟨.or, [43, 15]⟩, ⟨.and, [64, 29]⟩, ⟨.or, [44, 16]⟩,
    ⟨.and, [66, 30]⟩, ⟨.or, [45, 17]⟩, ⟨.and, [68, 31]⟩, ⟨.or, [46, 18]⟩,
    ⟨.and, [70, 32]⟩, ⟨.or, [47, 19]⟩, ⟨.and, [72, 33]⟩, ⟨.or, [48, 20]⟩,
    ⟨.and, [74, 34]⟩, ⟨.or, [52, 21]⟩, ⟨.and, [76, 35]⟩, ⟨.or, [53, 22]⟩,
    ⟨.and, [78, 36]⟩, ⟨.or, [54, 23]⟩, ⟨.and, [80, 37]⟩, ⟨.or, [55, 24]⟩,
    ⟨.and, [82, 38]⟩, ⟨.or, [57, 59]⟩, ⟨.or, [84, 61]⟩, ⟨.or, [85, 63]⟩,
    ⟨.or, [86, 65]⟩, ⟨.or, [87, 67]⟩, ⟨.or, [88, 69]⟩, ⟨.or, [89, 71]⟩,
    ⟨.or, [90, 73]⟩, ⟨.or, [91, 75]⟩, ⟨.or, [92, 77]⟩, ⟨.or, [93, 79]⟩,
    ⟨.or, [94, 81]⟩, ⟨.or, [95, 83]⟩], 96⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem size_eq : circuit.size = 58 := rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem legal : TopForm.IsAO2 39 circuit := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem graph_on (x : Fin 39 → Bool) :
    graphFun graph ∅ x = edges.any (fun e => x e.1 && x e.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases huv with h | h
    · exact ⟨(u, v), h, hu, hv⟩
    · exact ⟨(v, u), h, hv, hu⟩
  · rintro ⟨⟨u, v⟩, h, hu, hv⟩
    exact ⟨u, v, Or.inl h, hu, hv⟩

-- A single step of symbolic evaluation commutes with interpretation.
inductive Formula
  | var : Fin 39 → Formula
  | join : Formula → Formula → Formula
  | meet : Formula → Formula → Formula
  | off | on
  deriving DecidableEq

def Formula.val (x : Fin 39 → Bool) : Formula → Bool
  | .var i => x i
  | .join a b => a.val x || b.val x
  | .meet a b => a.val x && b.val x
  | .off => false
  | .on => true

def reifyGate (ws : List Formula) (g : Gate) : Formula :=
  match g.op with
  | .and => (g.inputs.map (fun i => ws.getD i .off)).foldr Formula.meet .on
  | .or => (g.inputs.map (fun i => ws.getD i .off)).foldr Formula.join .off
  | _ => .off

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem getD_map_val (ws : List Formula) (x : Fin 39 → Bool) (i : Nat) :
    (ws.map (Formula.val x)).getD i false = (ws.getD i .off).val x := by
  induction ws generalizing i with
  | nil => cases i <;> rfl
  | cons a t ih => cases i with
    | zero => rfl
    | succ j => exact ih j

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem val_meet (fs : List Formula) (x : Fin 39 → Bool) :
    (fs.foldr Formula.meet .on).val x = (fs.map (Formula.val x)).all id := by
  induction fs with
  | nil => rfl
  | cons a t ih => simp [Formula.val, ih]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem val_join (fs : List Formula) (x : Fin 39 → Bool) :
    (fs.foldr Formula.join .off).val x = (fs.map (Formula.val x)).any id := by
  induction fs with
  | nil => rfl
  | cons a t ih => simp [Formula.val, ih]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem step_correct (ws : List Formula) (g : Gate) (x : Fin 39 → Bool)
    (h : g.op = .and ∨ g.op = .or) :
    (reifyGate ws g).val x =
      g.op.eval (g.inputs.map (fun i => (ws.map (Formula.val x)).getD i false)) := by
  rcases h with h | h <;>
    simp only [reifyGate, h, GateOp.eval, val_meet, val_join, List.map_map, Function.comp_def, getD_map_val]

def reify (gs : List Gate) (ws : List Formula) :=
  gs.foldl (fun w g => w ++ [reifyGate w g]) ws

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem reify_correct (gs : List Gate) (ws : List Formula) (x : Fin 39 → Bool)
    (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (reify gs ws).map (Formula.val x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
        (ws.map (Formula.val x)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change (reify gs (ws ++ [reifyGate ws g])).map _ = _
    rw [ih _ (fun a ha => h a (by simp [ha]))]
    simp [List.foldl_cons, step_correct ws g x (h g (by simp))]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem via_formula (x : Fin 39 → Bool) :
    circuitFun 39 circuit x =
      ((reify circuit.gates (List.ofFn Formula.var)).getD circuit.output .off).val x := by
  rw [← getD_map_val, reify_correct _ _ _ legal.1]
  simp [circuitFun, Circuit.eval, Circuit.wires, Formula.val]

-- Each term lists input vertices that must all be on.
def Formula.terms : Formula → List (List (Fin 39))
  | .var i => [[i]]
  | .join a b => a.terms ++ b.terms
  | .meet a b => a.terms.flatMap (fun u => b.terms.map (u ++ ·))
  | .off => []
  | .on => [[]]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem val_iff_term (f : Formula) (x : Fin 39 → Bool) :
    f.val x = true ↔ ∃ t ∈ f.terms, ∀ i ∈ t, x i = true := by
  induction f with
  | var i => simp [Formula.val, Formula.terms]
  | off => simp [Formula.val, Formula.terms]
  | on => simp [Formula.val, Formula.terms]
  | join a b ia ib =>
    simp only [Formula.val, Formula.terms, Bool.or_eq_true, ia, ib, List.mem_append]
    aesop
  | meet a b ia ib =>
    simp only [Formula.val, Formula.terms, Bool.and_eq_true, ia, ib,
      List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨⟨u, hu, hx⟩, ⟨v, hv, hy⟩⟩
      exact ⟨u ++ v, ⟨u, hu, v, hv, rfl⟩, fun i hi => (List.mem_append.mp hi).elim (hx i) (hy i)⟩
    · rintro ⟨_, ⟨u, hu, v, hv, rfl⟩, hx⟩
      exact ⟨⟨u, hu, fun i hi => hx i (List.mem_append_left _ hi)⟩,
        ⟨v, hv, fun i hi => hx i (List.mem_append_right _ hi)⟩⟩

private def outputFormula := (reify circuit.gates (List.ofFn Formula.var)).getD circuit.output .off

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem term_has_edge : ∀ t ∈ outputFormula.terms,
    ∃ e ∈ edges, e.1 ∈ t ∧ e.2 ∈ t := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem edge_has_term : ∀ e ∈ edges, ∃ t ∈ outputFormula.terms,
    ∀ i ∈ t, i = e.1 ∨ i = e.2 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem computes : circuitFun 39 circuit = graphFun graph ∅ := by
  funext x
  rw [graph_on, via_formula]
  apply Bool.eq_iff_iff.mpr
  rw [val_iff_term, List.any_eq_true]
  change (∃ t ∈ outputFormula.terms, _) ↔ _
  constructor
  · rintro ⟨t, ht, hx⟩
    obtain ⟨e, he, hl, hr⟩ := term_has_edge t ht
    exact ⟨e, he, Bool.and_eq_true_iff.mpr ⟨hx _ hl, hx _ hr⟩⟩
  · rintro ⟨e, he, hx⟩
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hx
    obtain ⟨t, ht, hs⟩ := edge_has_term e he
    exact ⟨t, ht, fun i hi => (hs i hi).elim (fun h => h ▸ hl) (fun h => h ▸ hr)⟩

def privateVertex (j : Fin 14) : Fin 39 := ⟨11 + j.val, by omega⟩

def selector (j : Fin 14) : Fin 39 := ⟨25 + j.val, by omega⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem private_adjacent : ∀ i j : Fin 14, graph.Adj (privateVertex i) (selector j) ↔ i = j := by
  decide

-- Covering the private matching needs at least fourteen oriented rectangles.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem rectangle_count {k : ℕ} (left right : Fin k → Fin 39 → Prop)
    (valid : ∀ r u v, left r u → right r v → graph.Adj u v)
    (cover : ∀ j, ∃ r, left r (privateVertex j) ∧ right r (selector j)) : 14 ≤ k := by
  classical
  choose pick hp using cover
  have inj : Function.Injective pick := by
    intro i j h
    apply (private_adjacent i j).mp
    exact valid (pick i) _ _ (hp i).1 (h ▸ (hp j).2)
  simpa using Fintype.card_le_of_injective pick inj

def singleLevel (D : Circuit) : Prop :=
  ∀ i < D.gates.length, ∀ j < D.gates.length,
    (gateAt D i).op = GateOp.and → (gateAt D j).op = GateOp.and →
    ¬ EdgeOwnership.InCone 39 D i j

-- The only remaining separation claim for this explicit witness.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem excludes_least
    (lower : ∀ D, TopForm.IsAO2 39 D → circuitFun 39 D = graphFun graph ∅ →
      singleLevel D → 59 ≤ D.size) :
    ¬ ∃ D, TopForm.IsLeastAO graph D ∧ singleLevel D := by
  rintro ⟨D, ⟨model, eqn, minimum⟩, level⟩
  have upper := minimum circuit legal computes
  have bottom := lower D model eqn level
  rw [size_eq] at upper
  omega

end TarjanWitness

-- Wire and path lemmas adapted from the project proof of L-meta-1491.
namespace TarjanTrace.TraceBasics
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

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

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

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

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

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩


end TarjanTrace.TraceBasics
namespace TarjanTrace

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership
open TraceBasics

def Flat (n : ℕ) (C : Circuit) : Prop :=
  ∀ i < C.gates.length, ∀ j < C.gates.length,
    (gateAt C i).op = .and → (gateAt C j).op = .and → ¬ InCone n C i j

def live {n : ℕ} (C : Circuit) (i : ℕ) :=
  i < C.gates.length ∧ (gateAt C i).op = GateOp.and ∧
    Relation.ReflTransGen (OrStep n C) C.output (n+i)

def sees {n : ℕ} (C : Circuit) (i : ℕ) (pos : Fin 2) (v : Fin n) :=
  Relation.ReflTransGen (OrStep n C) (TopForm.opnd C i pos) v.val

theorem cross_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (legal : TopForm.IsAO2 n C) (eqn : circuitFun n C = graphFun G ∅)
    {i : ℕ} (hi : live (n := n) C i) {u v : Fin n} (hu : sees C i 0 u) (hv : sees C i 1 v) :
    G.Adj u v := by
  obtain ⟨hlen, hop, hr⟩ := hi
  obtain ⟨p, q, ins⟩ := List.length_eq_two.mp (legal.2.2 _ (gateAt_mem hlen))
  have ep : TopForm.opnd C i 0 = p := by simp [TopForm.opnd, ins]
  have eq : TopForm.opnd C i 1 = q := by simp [TopForm.opnd, ins]
  unfold sees at hu hv
  rw [ep] at hu
  rw [eq] at hv
  have back := legal.2.1 i hlen
  exact side_adj G (graphFun G ∅) (fun a b => (graphFun_pair G a b).mp) i hlen hop
    (below_of_reach _ (fun x => congrFun eqn x) i hr) p q ins
    (back p (by rw [ins]; simp)) (back q (by rw [ins]; simp)) u v hu hv

theorem edge_covered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (legal : TopForm.IsAO2 n C) (eqn : circuitFun n C = graphFun G ∅)
    (flat : Flat n C) {u v : Fin n} (adj : G.Adj u v) :
    ∃ i, live (n := n) C i ∧
      ((sees C i 0 u ∧ sees C i 1 v) ∨ (sees C i 0 v ∧ sees C i 1 u)) := by
  obtain ⟨i, hi, hn, hr, hv⟩ := edge_trace G (graphFun G ∅)
    (fun a b => (graphFun_pair G a b).mp) (fun x => congrFun eqn x) u v
    ((graphFun_pair G u v).mpr adj)
  have op : (gateAt C i).op = GateOp.and :=
    (legal.1 _ (gateAt_mem hi)).resolve_right hn
  have liv : live (n := n) C i := ⟨hi, op, hr⟩
  obtain ⟨p, q, ins⟩ := List.length_eq_two.mp (legal.2.2 _ (gateAt_mem hi))
  have src (b : Fin 2) : TopForm.opnd C i b ∈ (gateAt C i).inputs := by
    fin_cases b <;> simp [TopForm.opnd, ins]
  have find (b : Fin 2) : ∃ t : Fin n, (t = u ∨ t = v) ∧ sees C i b t := by
    have ⟨hlt, ht⟩ := (val_and (n := n) (by simp) hi op).mp hv _ (src b)
    rcases operand_trace u v _ ht with h | ⟨j, hj, nonor, reach, _⟩
    · exact h
    · exact (flat j hj i hi ((legal.1 _ (gateAt_mem hj)).resolve_right nonor) op
        (operand_cone hi (src b) hlt reach)).elim
  obtain ⟨a, ha, sa⟩ := find 0
  obtain ⟨b, hb, sb⟩ := find 1
  have off : a ≠ b := (cross_edge G legal eqn liv sa sb).ne
  refine ⟨i, liv, ?_⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

end TarjanTrace

namespace TarjanTrace

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership
open TraceBasics

noncomputable def upperGates (n : Nat) (C : Circuit) (op : GateOp) : Finset Nat := by
  classical
  exact (Finset.range C.gates.length).filter (fun i => (gateAt C i).op = op ∧
    Relation.ReflTransGen (OrStep n C) C.output (n + i))

theorem mem_upperGates {n : Nat} {C : Circuit} {op : GateOp} {i : Nat} :
    i ∈ upperGates n C op ↔ i < C.gates.length ∧ (gateAt C i).op = op ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + i) := by
  classical
  simp [upperGates]

theorem top_count (n : Nat) (C : Circuit) (legal : TopForm.IsAO2 n C) :
    (upperGates n C .and).card ≤ (upperGates n C .or).card + 1 := by
  classical
  let A := upperGates n C .and
  let O := upperGates n C .or
  let children := fun i => (gateAt C i).inputs.toFinset
  have cover : (A ∪ O).image (fun i => n+i) ⊆ insert C.output (O.biUnion children) := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have reach : Relation.ReflTransGen (OrStep n C) C.output (n+i) := by
      rcases Finset.mem_union.mp hi with h | h <;> exact (mem_upperGates.mp h).2.2
    rcases Relation.ReflTransGen.cases_tail reach with h | ⟨p, hr, j, hj, rfl, hop, hin, _⟩
    · simp [← h]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_biUnion.mpr ⟨j, mem_upperGates.mpr ⟨hj, hop, hr⟩, List.mem_toFinset.mpr hin⟩
  have disj : Disjoint A O := by
    rw [Finset.disjoint_left]
    intro i ha ho
    exact GateOp.noConfusion ((mem_upperGates.mp ha).2.1.symm.trans (mem_upperGates.mp ho).2.1)
  have nl : ((A ∪ O).image (fun i => n+i)).card = A.card + O.card := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h), Finset.card_union_of_disjoint disj]
  have each (j : Nat) (hj : j ∈ O) : (children j).card ≤ 2 := by
    calc
      _ ≤ (gateAt C j).inputs.length := List.toFinset_card_le _
      _ = 2 := legal.2.2 _ (gateAt_mem (mem_upperGates.mp hj).1)
  have count := Finset.card_le_card cover
  rw [nl] at count
  have one := Finset.card_insert_le C.output (O.biUnion children)
  have two : (O.biUnion children).card ≤ O.card * 2 := by
    calc
      _ ≤ ∑ j ∈ O, (children j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ O, 2 := Finset.sum_le_sum each
      _ = _ := by simp
  change A.card ≤ O.card + 1
  omega

end TarjanTrace

namespace TarjanWitness

open CircuitLowerBounds MetaComplexity TarjanTrace

private theorem private_side (i : Fin 14) : side (privateVertex i) = false := by
  unfold side privateVertex
  simp only [decide_eq_false_iff_not]
  change ¬ 25 ≤ 11 + i.val
  omega

private theorem distinct_side (i j : Fin 14) : ¬graph.Adj (privateVertex i) (privateVertex j) := by
  intro h
  exact bipartite _ _ h (by rw [private_side,private_side])

private def covered (C : Circuit) (g : Nat) (i : Fin 14) :=
  (sees C g 0 (privateVertex i) ∧ sees C g 1 (selector i)) ∨
    (sees C g 0 (selector i) ∧ sees C g 1 (privateVertex i))

theorem private_gate_unique {C : Circuit} (legal : TopForm.IsAO2 39 C)
    (eqn : circuitFun 39 C = MetaComplexity.NestedCover.graphFun graph ∅) {g : Nat}
    (live : TarjanTrace.live (n := 39) C g) {i j : Fin 14}
    (hi : covered C g i) (hj : covered C g j) : i = j := by
  rcases hi with ⟨il,ir⟩ | ⟨il,ir⟩ <;> rcases hj with ⟨jl,jr⟩ | ⟨jl,jr⟩
  · exact (private_adjacent i j).mp (cross_edge graph legal eqn live il jr)
  · exact (distinct_side i j (cross_edge graph legal eqn live il jr)).elim
  · exact (distinct_side j i (cross_edge graph legal eqn live jl ir)).elim
  · exact (private_adjacent i j).mp (cross_edge graph legal eqn live jl ir).symm

theorem live_ands_ge_fourteen {C : Circuit} (legal : TopForm.IsAO2 39 C)
    (eqn : circuitFun 39 C = MetaComplexity.NestedCover.graphFun graph ∅)
    (flat : singleLevel C) : 14 ≤ (upperGates 39 C .and).card := by
  classical
  have cover (i : Fin 14) : ∃ g, TarjanTrace.live (n := 39) C g ∧ covered C g i :=
    edge_covered graph legal eqn flat ((private_adjacent i i).mpr rfl)
  choose pick good hcov using cover
  let f : Fin 14 → ↥(upperGates 39 C .and) := fun i => ⟨pick i, mem_upperGates.mpr (good i)⟩
  have inj : Function.Injective f := by
    intro i j h
    have eqg : pick i = pick j := congrArg Subtype.val h
    exact private_gate_unique legal eqn (good i) (hcov i) (eqg ▸ hcov j)
  simpa using Fintype.card_le_of_injective f inj

end TarjanWitness

namespace TarjanWitness.SumBound


-- Supports are masks of the eleven original input variables.
def base : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 513, 1026, 516, 1032, 576, 704, 960, 1088, 1216, 1472]
def targets : List Nat := [977, 1490, 996, 1512]

def joins (available : List Nat) :=
  available.flatMap fun a => available.map fun b => a ||| b

def useful (s : Nat) : Bool :=
  !(base.contains s) && !(targets.contains s) && targets.any (fun t => s ||| t == t)

-- Auxiliary supports that can be computed in one OR using only free signals.
def initial := (joins base).filter useful |>.eraseDups

-- Extra supports available after one more signal has been constructed.
def extend (available : List Nat) (newSignal : Nat) :=
  (available.map (fun v => v ||| newSignal)).filter useful

-- The largest free subsets of each of the four target supports.
def maximalFree : List (Nat × List Nat) := [(977, [16, 513, 960]), (1490, [16, 1026, 1472]), (996, [32, 516, 960]), (1512, [32, 1032, 1472])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem maximal_free_complete : ∀ z ∈ maximalFree, ∀ b ∈ base, b ||| z.1 = z.1 →
    ∃ m ∈ z.2, b ||| m = m := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem maximal_free_sound : ∀ z ∈ maximalFree, ∀ m ∈ z.2, m ∈ base ∧ m ||| z.1 = z.1 := by decide

def oneHelper (s : Nat) : Nat :=
  (if (s ||| 16 == 977) || (s ||| 513 == 977) || (s ||| 960 == 977) then 1 else 0) +
  (if (s ||| 16 == 1490) || (s ||| 1026 == 1490) || (s ||| 1472 == 1490) then 2 else 0) +
  (if (s ||| 32 == 996) || (s ||| 516 == 996) || (s ||| 960 == 996) then 4 else 0) +
  (if (s ||| 32 == 1512) || (s ||| 1032 == 1512) || (s ||| 1472 == 1512) then 8 else 0)

def onePair (s : Nat) : Nat :=
  if s == 977 then 1 else if s == 1490 then 2 else if s == 996 then 4 else if s == 1512 then 8 else 0

def finishMask (a b c : Nat) :=
  oneHelper a ||| oneHelper b ||| oneHelper c |||
    onePair (a ||| b) ||| onePair (a ||| c) ||| onePair (b ||| c)

def failsAfter (a : Nat) : Bool :=
  let afterA := initial ++ extend base a
  afterA.all fun b =>
    let finalCandidates := afterA ++ extend (a :: base) b
    finalCandidates.all fun c => finishMask a b c != 15


def inputs : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
def required : List Nat := (base.drop 11) ++ targets

-- The support of each new OR is the union of two earlier supports.
def Program (available : List Nat) : List Nat → Prop
  | [] => True
  | v :: rest => (∃ a ∈ available, ∃ b ∈ available, a ||| b = v) ∧
      Program (v :: available) rest

def IsPart (a b : Nat) : Prop := a ||| b = b

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem parts {a b c : Nat} (h : IsPart (a ||| b) c) :
    IsPart a c ∧ IsPart b c := by
  unfold IsPart at *
  constructor
  · calc
      a ||| c = a ||| ((a ||| b) ||| c) := by rw [h]
      _ = (a ||| b) ||| c := by simp only [← Nat.or_assoc, Nat.or_self]
      _ = c := h
  · calc
      b ||| c = b ||| ((a ||| b) ||| c) := by rw [h]
      _ = (a ||| (b ||| b)) ||| c := by ac_rfl
      _ = c := by simpa only [Nat.or_self] using h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem incomparable : ∀ a ∈ targets, ∀ b ∈ targets,
    a ||| b = b → a = b := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem input_free : ∀ i ∈ inputs, i ∈ base := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem required_disjoint : ∀ i ∈ required, useful i = false := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem useful_iff (x : Nat) :
    useful x = true ↔ x ∉ base ∧ x ∉ targets ∧ ∃ t ∈ targets, IsPart x t := by
  simp [useful, IsPart, and_assoc]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem free_or_useful {x t : Nat} (ht : t ∈ targets) (hx : IsPart x t)
    (hne : x ≠ t) : x ∈ base ∨ useful x = true := by
  by_cases hb : x ∈ base
  · exact Or.inl hb
  · exact Or.inr ((useful_iff _).mpr ⟨hb, fun h => hne (incomparable x h t ht hx), t, ht, hx⟩)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem parts_of_useful {a b : Nat} (h : useful (a ||| b) = true) :
    (a ∈ base ∨ useful a = true) ∧ (b ∈ base ∨ useful b = true) := by
  obtain ⟨_, hn, t, ht, hs⟩ := (useful_iff _).mp h
  have ⟨ha, hb⟩ := parts hs
  have ltA : a ≠ t := by
    rintro rfl
    have hba : b ||| a = a := hb
    exact hn (by simpa [Nat.or_comm a b, hba] using ht)
  have ltB : b ≠ t := by
    rintro rfl
    exact hn (by simpa only [show a ||| b = b from ha] using ht)
  exact ⟨free_or_useful ht ha ltA, free_or_useful ht hb ltB⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem keep_aux (available gs : List Nat) (h : Program available gs) :
    Program (available.filter useful ++ base) (gs.filter useful) := by
  induction gs generalizing available with
  | nil => trivial
  | cons v rest ih =>
    obtain ⟨⟨a, ha, b, hb, rfl⟩, hrest⟩ := h
    by_cases hu : useful (a ||| b) = true
    · obtain ⟨hua, hub⟩ := parts_of_useful hu
      simp only [List.filter_cons_of_pos hu]
      refine ⟨⟨a, ?_, b, ?_, rfl⟩, ?_⟩
      · exact List.mem_append.mpr (hua.elim Or.inr (fun h => Or.inl (List.mem_filter.mpr ⟨ha, h⟩)))
      · exact List.mem_append.mpr (hub.elim Or.inr (fun h => Or.inl (List.mem_filter.mpr ⟨hb, h⟩)))
      · simpa only [List.filter_cons_of_pos hu, List.cons_append] using ih _ hrest
    · simpa only [List.filter_cons_of_neg hu] using ih _ hrest

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_sources (available gs : List Nat) (h : Program available gs)
    {t : Nat} (ht : t ∈ gs) (ha : t ∉ available) :
    ∃ a ∈ available ++ gs, ∃ b ∈ available ++ gs, a ≠ t ∧ b ≠ t ∧ a ||| b = t := by
  induction gs generalizing available with
  | nil => contradiction
  | cons v rest ih =>
    obtain ⟨gen, hrest⟩ := h
    by_cases eq : t = v
    · subst v
      obtain ⟨a, hav, b, hbv, hv⟩ := gen
      exact ⟨a, List.mem_append_left _ hav, b, List.mem_append_left _ hbv,
        fun he => ha (he ▸ hav), fun he => ha (he ▸ hbv), hv⟩
    · obtain ⟨a, hav, b, hbv, hne, hne', hv⟩ :=
        ih (v :: available) hrest ((List.mem_cons.mp ht).resolve_left eq)
          (by simp [eq, ha])
      have move (z : Nat) (hz : z ∈ (v :: available) ++ rest) : z ∈ available ++ v :: rest := by
        simp only [List.mem_append, List.mem_cons] at hz ⊢
        tauto
      exact ⟨a, move _ hav, b, move _ hbv, hne, hne', hv⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem no_target_input : ∀ t ∈ targets, t ∉ inputs := by decide
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem no_useful_input : inputs.filter useful = [] := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem target_joins {gs : List Nat} (h : Program inputs gs) (all : ∀ t ∈ targets, t ∈ gs) :
    ∀ t ∈ targets, t ∈ joins (base ++ gs.filter useful) := by
  intro t ht
  obtain ⟨a, ha, b, hb, hna, hnb, hsum⟩ :=
    first_sources inputs gs h (all _ ht) (no_target_input _ ht)
  have hp : IsPart (a ||| b) t := by rw [hsum]; unfold IsPart; exact Nat.or_self t
  obtain ⟨hpa, hpb⟩ := parts hp
  have mem (v : Nat) (hm : v ∈ inputs ++ gs) (hp : IsPart v t) (hn : v ≠ t) :
      v ∈ base ++ gs.filter useful := by
    apply List.mem_append.mpr
    rcases free_or_useful ht hp hn with hf | hu
    · exact Or.inl hf
    · rcases List.mem_append.mp hm with hi | hg
      · exact Or.inl (input_free v hi)
      · exact Or.inr (List.mem_filter.mpr ⟨hg, hu⟩)
  exact List.mem_flatMap.mpr ⟨a, mem _ ha hpa hna, List.mem_map.mpr ⟨b, mem _ hb hpb hnb, hsum⟩⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem auxiliary_count {gs : List Nat} (h : ∀ v ∈ required, v ∈ gs) (budget : gs.length ≤ 17) :
    (gs.filter useful).length ≤ 3 := by
  have sub : required.toFinset ⊆ (gs.filter (fun v => !useful v)).toFinset := by
    intro v hv
    have hr := List.mem_toFinset.mp hv
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨h v hr, by simp [required_disjoint v hr]⟩)
  have card := Finset.card_le_card sub
  have num : required.toFinset.card = 14 := by decide
  rw [num] at card
  have cap := (gs.filter (fun v => !useful v)).toFinset_card_le
  have split (l : List Nat) : (l.filter useful).length + (l.filter (fun v => !useful v)).length = l.length := by
    induction l with
    | nil => rfl
    | cons a l ih => cases he : useful a <;> simp [he, ih, Nat.succ_add] <;> omega
  have := split gs
  omega

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem helper_program {gs : List Nat} (h : Program inputs gs) : Program base (gs.filter useful) := by
  simpa only [no_useful_input, List.nil_append] using keep_aux inputs gs h


private def T (i : Fin 4) : Nat := [977, 1490, 996, 1512][i.val]'(by simpa using i.isLt)
private def M (i : Fin 4) : List Nat := (maximalFree[i.val]'(by simpa [maximalFree] using i.isLt)).2

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem table_spec : ∀ i : Fin 4, (T i, M i) ∈ maximalFree ∧ T i ∈ targets := by decide
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem two_base_fail : ∀ a ∈ base, ∀ b ∈ base, a ||| b ∉ targets := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem helper_m (s : Nat) (i : Fin 4) (m : Nat) (hm : m ∈ M i) (h : s ||| m = T i) :
    (oneHelper s).testBit i.val = true := by
  fin_cases i <;> simp [M, maximalFree] at hm <;>
    rcases hm with rfl | rfl | rfl <;> change _ = _ at h <;> simp [T] at h <;>
    simp [oneHelper, h] <;> split_ifs <;> decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem helper_bit (s : Nat) (i : Fin 4) (b : Nat) (hb : b ∈ base) (h : s ||| b = T i) :
    (oneHelper s).testBit i.val = true := by
  have part : IsPart (s ||| b) (T i) := by rw [h]; exact Nat.or_self _
  obtain ⟨_, hbpart⟩ := parts part
  obtain ⟨m, hm, hbsub⟩ := maximal_free_complete (T i, M i) (table_spec i).1 b hb hbpart
  obtain ⟨_, hmt⟩ := maximal_free_sound (T i, M i) (table_spec i).1 m hm
  change m ||| T i = T i at hmt
  apply helper_m s i m hm
  calc
    s ||| m = s ||| (b ||| m) := by rw [hbsub]
    _ = (s ||| b) ||| m := (Nat.or_assoc _ _ _).symm
    _ = T i := by rw [h, Nat.or_comm, hmt]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem pair_bit (i : Fin 4) : (onePair (T i)).testBit i.val = true := by decide +revert

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem flags_small (a b c : Nat) : finishMask a b c < 16 := by
  have h1 (s : Nat) : oneHelper s < 2^4 := by unfold oneHelper; split_ifs <;> decide
  have h2 (s : Nat) : onePair s < 2^4 := by unfold onePair; split_ifs <;> decide
  unfold finishMask
  repeat' apply Nat.or_lt_two_pow (n := 4)
  all_goals first | exact h1 _ | exact h2 _

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem all_flags (a b c : Nat)
    (ha : useful a = true) (hb : useful b = true) (hc : useful c = true)
    (cover : ∀ t ∈ targets, t ∈ joins (base ++ [a,b,c])) : finishMask a b c = 15 := by
  have bit (i : Fin 4) : (finishMask a b c).testBit i.val = true := by
    obtain ⟨u, hu, h⟩ := List.mem_flatMap.mp (cover _ (table_spec i).2)
    obtain ⟨v, hv, huv⟩ := List.mem_map.mp h
    change u ||| v = T i at huv
    have sq (s : Nat) (hs : useful s = true) (h : s ||| s = T i) : False :=
      (useful_iff s |>.mp hs).2.1 ((Nat.or_self s ▸ h) ▸ (table_spec i).2)
    simp only [finishMask, Nat.testBit_or, Bool.or_eq_true]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with hu | rfl | rfl | rfl <;> rcases hv with hv | rfl | rfl | rfl
    all_goals first
      | exact False.elim (two_base_fail _ hu _ hv (huv ▸ (table_spec i).2))
      | have := helper_bit _ i _ hu ((Nat.or_comm _ _).trans huv); tauto
      | have := helper_bit _ i _ hv huv; tauto
      | exact False.elim (sq _ ha huv)
      | exact False.elim (sq _ hb huv)
      | exact False.elim (sq _ hc huv)
      | have hp := pair_bit i; rw [← huv] at hp; tauto
      | have hp := pair_bit i; rw [← huv, Nat.or_comm u v] at hp; tauto
  have small := flags_small a b c
  generalize hx : finishMask a b c = x at small bit ⊢
  have h0 := bit 0
  have h1 := bit 1
  have h2 := bit 2
  have h3 := bit 3
  have verify : ∀ k : Fin 16, k.val.testBit 0 = true → k.val.testBit 1 = true → k.val.testBit 2 = true → k.val.testBit 3 = true → k.val = 15 := by decide
  exact verify ⟨x,small⟩ h0 h1 h2 h3


set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private lemma append_program {xs : List Nat} (av more : List Nat)
    (all : Program av xs) (tail : Program (xs.reverse ++ av) more) : Program av (xs ++ more) := by
  induction xs generalizing av with
  | nil => simpa using tail
  | cons a xs ih =>
    exact ⟨all.1, ih (a :: av) all.2 (by simpa [List.append_assoc] using tail)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private lemma padding (n : Nat) (av : List Nat) (h : ∀ x ∈ base, x ∈ av) :
    Program av (List.replicate n 17) := by
  induction n generalizing av with
  | zero => trivial
  | succ n ih =>
    rw [List.replicate_succ]
    exact ⟨⟨1, h _ (by decide), 16, h _ (by decide), rfl⟩,
      ih _ (fun x hx => List.mem_cons_of_mem _ (h x hx))⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private lemma padded {xs : List Nat} (gen : Program base xs)
    (use : ∀ x ∈ xs, useful x = true) (len : xs.length ≤ 3) :
    ∃ a b c, xs ⊆ [a,b,c] ∧ Program base [a,b,c] ∧ ∀ x ∈ [a,b,c], useful x = true := by
  let ys := List.replicate (3-xs.length) 17
  have count : (xs ++ ys).length = 3 := by simp [ys]; omega
  obtain ⟨a,b,c,eqn⟩ := List.length_eq_three.mp count
  refine ⟨a,b,c,?_,?_,?_⟩ <;> rw [← eqn]
  · exact fun _ h => List.mem_append_left _ h
  · exact append_program _ _ gen (padding _ _ (fun x hx => List.mem_append_right _ hx))
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact use _ hx
    · have eq : x = 17 := (List.mem_replicate.mp hx).2
      subst x
      decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem join_cons {v a : Nat} {av : List Nat} (h : v ∈ joins (a :: av)) :
    v = a ∨ v ∈ joins av ∨ ∃ x ∈ av, x ||| a = v := by
  obtain ⟨x,hx,hy⟩ := List.mem_flatMap.mp h
  obtain ⟨y,hy,e⟩ := List.mem_map.mp hy
  rcases List.mem_cons.mp hx with rfl | hxr <;> rcases List.mem_cons.mp hy with rfl | hyr
  · exact Or.inl (e.symm.trans (Nat.or_self _))
  · exact Or.inr (Or.inr ⟨y,hyr,(Nat.or_comm _ _).trans e⟩)
  · exact Or.inr (Or.inr ⟨x,hxr,e⟩)
  · exact Or.inr (Or.inl (List.mem_flatMap.mpr ⟨x,hxr,List.mem_map.mpr ⟨y,hyr,e⟩⟩))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem search_excludes (cert : initial.all failsAfter = true)
    (a b c : Nat) (gen : Program base [a,b,c]) (ha : useful a = true)
    (hb : useful b = true) (hc : useful c = true) : finishMask a b c ≠ 15 := by
  have genmem {v : Nat} {l : List Nat} (h : ∃ a ∈ l, ∃ b ∈ l, a ||| b = v) :
      v ∈ joins l := by
    obtain ⟨x,hx,y,hy,e⟩ := h
    exact List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨y,hy,e⟩⟩
  have start {v : Nat} (h : v ∈ joins base) (hv : useful v = true) : v ∈ initial :=
    List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨h,hv⟩)
  have add {v s : Nat} {l : List Nat} (h : ∃ x ∈ l, x ||| s = v) (hv : useful v = true) :
      v ∈ extend l s := List.mem_filter.mpr ⟨List.mem_map.mpr h,hv⟩
  have ia := start (genmem gen.1) ha
  have second {v} (h : v ∈ joins (a :: base)) (hv : useful v = true) :
      v ∈ initial ++ extend base a := by
    rcases join_cons h with rfl | h | h
    · exact List.mem_append_left _ ia
    · exact List.mem_append_left _ (start h hv)
    · exact List.mem_append_right _ (add h hv)
  have ib := second (genmem gen.2.1) hb
  have ic : c ∈ (initial ++ extend base a) ++ extend (a :: base) b := by
    rcases join_cons (genmem gen.2.2.1) with rfl | h | h
    · exact List.mem_append_left _ ib
    · exact List.mem_append_left _ (second h hc)
    · exact List.mem_append_right _ (add h hc)
  have h := List.all_eq_true.mp cert a ia
  change ((initial ++ extend base a).all _) = true at h
  have h' := List.all_eq_true.mp h b ib
  exact bne_iff_ne.mp (List.all_eq_true.mp h' c ic)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem or_lower_of_check (cert : initial.all failsAfter = true) {gs : List Nat}
    (gen : Program inputs gs) (cover : ∀ x ∈ required, x ∈ gs) : 18 ≤ gs.length := by
  by_contra! small
  have n := auxiliary_count cover (by omega)
  obtain ⟨a,b,c,sub,gen3,huse⟩ := padded (helper_program gen)
    (fun _ h => (List.mem_filter.mp h).2) n
  have subset : base ++ gs.filter useful ⊆ base ++ [a,b,c] := fun _ h =>
    (List.mem_append.mp h).elim (List.mem_append_left _) (fun hv => List.mem_append_right _ (sub hv))
  have hits : ∀ t ∈ targets, t ∈ joins (base ++ [a,b,c]) := by
    intro t ht
    have h := target_joins gen (fun x hx => cover x (List.mem_append_right _ hx)) t ht
    obtain ⟨x,hx,hy⟩ := List.mem_flatMap.mp h
    obtain ⟨y,hy,e⟩ := List.mem_map.mp hy
    exact List.mem_flatMap.mpr ⟨x,subset hx,List.mem_map.mpr ⟨y,subset hy,e⟩⟩
  exact search_excludes cert a b c gen3 (huse a (by simp)) (huse b (by simp)) (huse c (by simp))
    (all_flags a b c (huse a (by simp)) (huse b (by simp)) (huse c (by simp)) hits)

end TarjanWitness.SumBound

namespace TarjanWitness.SumBound

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem initial_eq : initial = [17, 65, 129, 257, 577, 705, 961, 18, 66, 130, 258, 1090, 1218, 1474, 36, 68, 132, 260, 580, 708, 964, 40, 72, 136, 264, 1096, 1224, 1480, 80, 144, 272, 528, 1040, 529, 1042, 592, 720, 976, 1104, 1232, 1488, 96, 160, 288, 544, 1056, 548, 1064, 608, 736, 992, 1120, 1248, 1504, 192, 320, 384, 640, 1152, 641, 1154, 644, 1160, 768, 1280, 769, 1282, 772, 1288, 832, 1344] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_17 : failsAfter 17 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_65 : failsAfter 65 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_129 : failsAfter 129 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_257 : failsAfter 257 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_577 : failsAfter 577 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_705 : failsAfter 705 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_961 : failsAfter 961 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_18 : failsAfter 18 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_66 : failsAfter 66 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_130 : failsAfter 130 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_258 : failsAfter 258 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1090 : failsAfter 1090 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1218 : failsAfter 1218 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1474 : failsAfter 1474 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_36 : failsAfter 36 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_68 : failsAfter 68 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_132 : failsAfter 132 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_260 : failsAfter 260 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_580 : failsAfter 580 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_708 : failsAfter 708 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_964 : failsAfter 964 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_40 : failsAfter 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_72 : failsAfter 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_136 : failsAfter 136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_264 : failsAfter 264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1096 : failsAfter 1096 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1224 : failsAfter 1224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1480 : failsAfter 1480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_80 : failsAfter 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_144 : failsAfter 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_272 : failsAfter 272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_528 : failsAfter 528 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1040 : failsAfter 1040 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_529 : failsAfter 529 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1042 : failsAfter 1042 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_592 : failsAfter 592 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_720 : failsAfter 720 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_976 : failsAfter 976 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1104 : failsAfter 1104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1232 : failsAfter 1232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1488 : failsAfter 1488 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_96 : failsAfter 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_160 : failsAfter 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_288 : failsAfter 288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_544 : failsAfter 544 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1056 : failsAfter 1056 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_548 : failsAfter 548 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1064 : failsAfter 1064 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_608 : failsAfter 608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_736 : failsAfter 736 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_992 : failsAfter 992 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1120 : failsAfter 1120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1248 : failsAfter 1248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1504 : failsAfter 1504 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_192 : failsAfter 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_320 : failsAfter 320 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_384 : failsAfter 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_640 : failsAfter 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1152 : failsAfter 1152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_641 : failsAfter 641 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1154 : failsAfter 1154 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_644 : failsAfter 644 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1160 : failsAfter 1160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_768 : failsAfter 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1280 : failsAfter 1280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_769 : failsAfter 769 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1282 : failsAfter 1282 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_772 : failsAfter 772 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1288 : failsAfter 1288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_832 : failsAfter 832 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem first_1344 : failsAfter 1344 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem no_three_auxiliaries : initial.all failsAfter = true := by
  simp only [initial_eq, List.all_cons, List.all_nil, first_17, first_65, first_129, first_257, first_577, first_705, first_961, first_18, first_66, first_130, first_258, first_1090, first_1218, first_1474, first_36, first_68, first_132, first_260, first_580, first_708, first_964, first_40, first_72, first_136, first_264, first_1096, first_1224, first_1480, first_80, first_144, first_272, first_528, first_1040, first_529, first_1042, first_592, first_720, first_976, first_1104, first_1232, first_1488, first_96, first_160, first_288, first_544, first_1056, first_548, first_1064, first_608, first_736, first_992, first_1120, first_1248, first_1504, first_192, first_320, first_384, first_640, first_1152, first_641, first_1154, first_644, first_1160, first_768, first_1280, first_769, first_1282, first_772, first_1288, first_832, first_1344]
  rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem or_lower {gs : List Nat} (gen : Program inputs gs) (cover : ∀ x ∈ required, x ∈ gs) : 18 ≤ gs.length := or_lower_of_check no_three_auxiliaries gen cover

end TarjanWitness.SumBound

namespace TarjanWitness.SumBound

namespace Reverse

def pool (av gs : List Nat) := gs.reverse ++ av

theorem extendProgram {xs : List Nat} (av ys : List Nat)
    (hx : Program av xs) (hy : Program (pool av xs) ys) : Program av (xs ++ ys) := by
  induction xs generalizing av with
  | nil => simpa [pool] using hy
  | cons x xs ih => exact ⟨hx.1, ih (x :: av) hx.2 (by simpa [pool, List.append_assoc] using hy)⟩

theorem inPool {v : Nat} {av gs : List Nat} : v ∈ pool av gs ↔ v ∈ gs ∨ v ∈ av := by
  simp [pool]

def total (xs : List Nat) : Nat := xs.foldr (· ||| ·) 0

theorem merge {xs : List Nat} (av : List Nat) (ok : xs ⊆ av) (hne : xs ≠ []) :
    ∃ gs, Program av gs ∧ total xs ∈ pool av gs ∧ gs.length + 1 = xs.length := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    by_cases hx : xs = []
    · subst xs
      exact ⟨[], trivial, by simpa [total, pool] using ok (by simp : x ∈ [x]), rfl⟩
    · obtain ⟨gs,hgs,hm,hlen⟩ := ih (fun a ha => ok (List.mem_cons_of_mem _ ha)) hx
      let z := x ||| total xs
      have hz : Program (pool av gs) [z] :=
        ⟨⟨x, inPool.mpr (Or.inr (ok (by simp))), total xs, hm, rfl⟩, trivial⟩
      refine ⟨gs ++ [z], extendProgram av _ hgs hz, ?_, ?_⟩
      · exact inPool.mpr (Or.inl (List.mem_append_right _ (by simp [z, total])))
      · simp; omega

abbrev Request := Nat × Nat

def contribution (rs : List Request) (key : Nat) : Nat :=
  rs.foldr (fun p acc => (if p.1.testBit key then p.2 else 0) ||| acc) 0

def select (v : Nat) (rs : List Request) := rs.filter (fun p => p.1 == v)
def other (v : Nat) (rs : List Request) := rs.filter (fun p => p.1 != v)

theorem contribution_split (v : Nat) (rs : List Request) (j : Nat) :
    contribution rs j = contribution (select v rs) j ||| contribution (other v rs) j := by
  induction rs with
  | nil => simp [contribution, select, other]
  | cons p ps ih =>
    by_cases h : p.1 = v <;>
      simp [select, other, contribution, h, select, other] at ih ⊢ <;> rw [ih] <;> ac_rfl

theorem length_split (v : Nat) (rs : List Request) :
    (select v rs).length + (other v rs).length = rs.length := by
  induction rs with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : p.1 = v <;> simp [select, other, h] at ih ⊢ <;> omega

theorem uniform (v : Nat) (rs : List Request) (j : Nat) (h : ∀ p ∈ rs, p.1 = v) :
    contribution rs j = if v.testBit j then total (rs.map Prod.snd) else 0 := by
  induction rs with
  | nil => simp [contribution, total]
  | cons p ps ih =>
    have hp := h p (by simp)
    have hps := ih (fun t ht => h t (by simp [ht]))
    change (if p.1.testBit j then p.2 else 0) ||| contribution ps j = _
    rw [hp, hps]
    cases hbit : v.testBit j <;> simp [total]

def valid (right left : List Nat) (rs : List Request) :=
  ∀ p ∈ rs, p.1 ∈ right ∧ p.2 ∈ left

theorem pull_one {v a b : Nat} {rv av : List Nat} (ha : a ∈ rv) (hb : b ∈ rv) (hv : a ||| b = v)
    (rs : List Request) (hr : valid (v :: rv) av rs) :
    ∃ gs next, Program av gs ∧ valid rv (pool av gs) next ∧
      (∀ j, contribution rs j = contribution next j) ∧
      gs.length + next.length ≤ rs.length + 1 := by
  let used := select v rs
  let rest := other v rs
  have restOK {p : Request} (h : p ∈ rest) : p.1 ∈ rv ∧ p.2 ∈ av := by
    obtain ⟨hm,hn⟩ := List.mem_filter.mp h
    obtain ⟨h1,h2⟩ := hr p hm
    exact ⟨(List.mem_cons.mp h1).resolve_left (bne_iff_ne.mp hn), h2⟩
  have hlen : used.length + rest.length = rs.length := length_split v rs
  have split (j) : contribution rs j = contribution used j ||| contribution rest j :=
    contribution_split v rs j
  by_cases empty : used = []
  · refine ⟨[],rest,trivial,?_,?_,?_⟩
    · intro p hp; simpa [pool] using restOK hp
    · intro j; rw [split, empty]; simp [contribution]
    · simp [empty] at hlen; simp [hlen]
  · let vals := used.map Prod.snd
    have leftOK : vals ⊆ av := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
      exact (hr p (List.mem_filter.mp hp).1).2
    obtain ⟨gs,gen,hwire,len⟩ := merge av leftOK (by simpa [vals] using empty)
    let w := total vals
    refine ⟨gs,(a,w) :: (b,w) :: rest,gen,?_,?_,?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨ha,hwire⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hb,hwire⟩
      exact ⟨(restOK hp).1,inPool.mpr (Or.inr (restOK hp).2)⟩
    · intro j
      rw [split, uniform v used j (fun p hp => beq_iff_eq.mp (List.mem_filter.mp hp).2)]
      rw [← hv, Nat.testBit_or]
      change (if a.testBit j || b.testBit j then w else 0) ||| contribution rest j =
        (if a.testBit j then w else 0) ||| ((if b.testBit j then w else 0) ||| contribution rest j)
      cases a.testBit j <;> cases b.testBit j <;> simp [← Nat.or_assoc, Nat.or_self]
    · have : vals.length = used.length := by simp [vals]
      simp only [List.length_cons]; omega

-- Reverse all right-side ORs and charge every binary merge once.
theorem transpose {rv rg : List Nat} (gen : Program rv rg) (av : List Nat) (rs : List Request)
    (hr : valid (pool rv rg) av rs) :
    ∃ gs next, Program av gs ∧ valid rv (pool av gs) next ∧
      (∀ j, contribution rs j = contribution next j) ∧
      gs.length + next.length ≤ rg.length + rs.length := by
  induction rg generalizing rv av rs with
  | nil => exact ⟨[],rs,trivial,by simpa [pool] using hr,fun _ => rfl,by simp⟩
  | cons v tail ih =>
    obtain ⟨⟨a,ha,b,hb,e⟩,ht⟩ := gen
    have hpool : pool rv (v :: tail) = pool (v :: rv) tail := by simp [pool, List.append_assoc]
    rw [hpool] at hr
    obtain ⟨gA,rA,pA,okA,preserveA,lenA⟩ := ih ht av rs hr
    obtain ⟨gB,rB,pB,okB,preserveB,lenB⟩ := pull_one ha hb e rA okA
    refine ⟨gA ++ gB,rB,extendProgram av _ pA pB,?_,fun j => (preserveA j).trans (preserveB j),?_⟩
    · simpa [pool,List.append_assoc] using okB
    · simp only [List.length_append, List.length_cons]; omega

def atKey (v : Nat) (rs : List Request) := total ((select v rs).map Prod.snd)

theorem select_other {v w : Nat} (hne : w ≠ v) (rs : List Request) :
    select w (other v rs) = select w rs := by
  unfold select other
  rw [List.filter_filter]
  apply List.filter_congr
  intro p _
  by_cases h : p.1 = w
  · have hn : p.1 ≠ v := fun e => hne (h.symm.trans e)
    simp [h, hne, hn]
  · simp [h]

theorem drain (keys : List Nat) (unique : keys.Nodup) (av : List Nat) (rs : List Request)
    (signal : ∀ p ∈ rs, p.2 ∈ av) (needed : ∀ v ∈ keys, select v rs ≠ []) :
    ∃ gs, Program av gs ∧ (∀ v ∈ keys, atKey v rs ∈ pool av gs) ∧
      gs.length + keys.length ≤ rs.length := by
  induction keys generalizing av rs with
  | nil => exact ⟨[],trivial,by simp,by simp⟩
  | cons v vs ih =>
    have hnodup := List.nodup_cons.mp unique
    let vals := (select v rs).map Prod.snd
    have sub : vals ⊆ av := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact signal p (List.mem_filter.mp hp).1
    obtain ⟨g,hg,wire,cost⟩ := merge av sub (by simpa [vals] using needed v (by simp))
    have restOK (p : Request) (hp : p ∈ other v rs) : p.2 ∈ pool av g :=
      inPool.mpr (Or.inr (signal p (List.mem_filter.mp hp).1))
    have still (w : Nat) (hw : w ∈ vs) : select w (other v rs) = select w rs :=
      select_other (v := v) (w := w) (fun e => hnodup.1 (e ▸ hw)) _
    obtain ⟨g2,hg2,rows,cost2⟩ := ih hnodup.2 (pool av g) (other v rs) restOK
      (fun w hw => by rw [still w hw]; exact needed w (by simp [hw]))
    refine ⟨g ++ g2, extendProgram av g2 hg hg2, ?_, ?_⟩
    · intro k hk
      have hp : atKey k rs ∈ pool (pool av g) g2 := by
        rcases List.mem_cons.mp hk with rfl | hk
        · exact inPool.mpr (Or.inr wire)
        · have h := rows k hk
          unfold atKey at h ⊢
          rw [still k hk] at h
          exact h
      simpa [pool, List.append_assoc] using hp
    · have split := length_split v rs
      have l : vals.length = (select v rs).length := by simp [vals]
      simp only [List.length_append,List.length_cons]; omega

theorem column (rs : List Request) (j : Nat)
    (h : ∀ p ∈ rs, p.1.testBit j = (p.1 == 2^j)) :
    contribution rs j = atKey (2^j) rs := by
  induction rs with
  | nil => rfl
  | cons p ps ih =>
    have tail := ih (fun q hq => h q (by simp [hq]))
    have head := h p (by simp)
    change (if p.1.testBit j then p.2 else 0) ||| contribution ps j = _
    rw [head, tail]
    by_cases he : p.1 = 2^j <;> simp [atKey,select,total,he]

end Reverse
end TarjanWitness.SumBound

namespace TarjanWitness.SumBound.Projection

def cut (k x : Nat) := x % 2^k
def wires (av gs : List Nat) := gs.reverse ++ av

def imageOK (k : Nat) (src dst : List Nat) :=
  ∀ x ∈ src, cut k x ≠ 0 → cut k x ∈ dst

def clean (k : Nat) (av : List Nat) :=
  ∀ x ∈ av, x.testBit k = true → cut k x = 0

theorem project (k : Nat) {av gs : List Nat} (program : Program av gs) (dst : List Nat)
    (image : imageOK k av dst) :
    ∃ es, Program dst es ∧ imageOK k (wires av gs) (wires dst es) ∧ es.length ≤ gs.length ∧
      (es.length = gs.length → clean k av → clean k (wires av gs)) := by
  induction gs generalizing av dst with
  | nil => exact ⟨[],trivial,by simpa [wires] using image,by simp,by simp [wires]⟩
  | cons z gs ih =>
    obtain ⟨⟨a,ha,b,hb,eq⟩,rest⟩ := program
    have hz : cut k z = cut k a ||| cut k b := by rw [← eq]; exact Nat.or_mod_two_pow
    have extend (d : List Nat) (keep : dst ⊆ d) (new : cut k z ≠ 0 → cut k z ∈ d) :
        imageOK k (z :: av) d := by
      intro x hx hx0
      rcases List.mem_cons.mp hx with rfl | h
      · exact new hx0
      · exact keep (image x h hx0)
    by_cases hzold : cut k a = 0 ∨ cut k b = 0
    · have new : cut k z ≠ 0 → cut k z ∈ dst := by
        rcases hzold with h | h
        · simpa [hz,h] using image b hb
        · simpa [hz,h] using image a ha
      obtain ⟨es,ok,rng,le,_⟩ := ih rest dst (extend dst (fun _ h => h) new)
      refine ⟨es,ok,by simpa [wires,List.append_assoc] using rng,by simp; omega,?_⟩
      intro h; simp at h; omega
    · have ha0 : cut k a ≠ 0 := fun h => hzold (Or.inl h)
      have hb0 : cut k b ≠ 0 := fun h => hzold (Or.inr h)
      obtain ⟨es,ok,rng,le,all⟩ := ih rest (cut k z :: dst)
        (extend _ (fun _ h => List.mem_cons_of_mem _ h) (fun _ => by simp))
      refine ⟨cut k z :: es, ⟨⟨cut k a,image a ha ha0,cut k b,image b hb hb0,hz.symm⟩,ok⟩,
        by simpa [wires,List.append_assoc] using rng,by simpa using le,?_⟩
      intro count start
      have notag : (a ||| b).testBit k = false := by
        rw [Nat.testBit_or]
        cases he : a.testBit k <;> cases hf : b.testBit k <;>
          first | rfl | exact (ha0 (start a ha he)).elim | exact (hb0 (start b hb hf)).elim
      have still : clean k (z :: av) := by
        intro x hx hbit
        rcases List.mem_cons.mp hx with rfl | h
        · rw [eq] at notag
          simp [hbit] at notag
        · exact start x h hbit
      simpa [wires,List.append_assoc] using all (by simpa using count) still

def sources (n : Nat) := (List.range n).map (fun j => 2^j)

theorem source_image (k : Nat) : imageOK k (sources (k+1)) (sources k) := by
  intro x hx hn
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
  have le : j ≤ k := by simpa [Nat.lt_succ_iff] using List.mem_range.mp hj
  by_cases eq : j = k
  · subst j; simp [cut] at hn
  · have lt : j < k := by omega
    have sm : (2:Nat)^j < 2^k := Nat.pow_lt_pow_right (by decide) lt
    rw [cut,Nat.mod_eq_of_lt sm]
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr lt,rfl⟩

theorem source_clean (k : Nat) : clean k (sources (k+1)) := by
  intro x hx hbit
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  have eq : j = k := by simpa [Nat.testBit_two_pow] using hbit
  simp [eq,cut]

theorem save_one (k : Nat) {gs : List Nat} (h : Program (sources (k+1)) gs)
    (mixed : ∃ x ∈ wires (sources (k+1)) gs, x.testBit k = true ∧ cut k x ≠ 0) :
    ∃ es, Program (sources k) es ∧ imageOK k (wires (sources (k+1)) gs) (wires (sources k) es) ∧
      es.length < gs.length := by
  obtain ⟨es,hs,im,le,if_eq⟩ := project k h _ (source_image k)
  refine ⟨es,hs,im,lt_of_le_of_ne le ?_⟩
  intro eq
  obtain ⟨x,hx,hb,hn⟩ := mixed
  exact hn (if_eq eq (source_clean k) x hx hb)

end TarjanWitness.SumBound.Projection

namespace TarjanRows
open TarjanWitness.SumBound TarjanWitness.SumBound.Projection

def row (j : Fin 14) : Nat :=
  [513,1026,516,1032,576,704,960,1088,1216,1472,977,1490,996,1512][j.val]'(by simp)

def augmented (k : Nat) (j : Fin 14) : Nat :=
  row j ||| (if j.val < k then 2^(11+j.val) else 0)

def leftVertex (i : Fin 25) : Fin 39 := ⟨i.val,by omega⟩

theorem var_inj : Function.Injective leftVertex := fun _ _ h => Fin.ext (congrArg (fun z : Fin 39 => z.val) h)
theorem sel_inj : Function.Injective TarjanWitness.selector := by
  intro i j h
  exact Fin.ext (Nat.add_left_cancel (show 25+i.val = 25+j.val from congrArg Fin.val h))

theorem edge_bit : ∀ (i : Fin 25) (j : Fin 14),
    (augmented 14 j).testBit i.val = true ↔ TarjanWitness.graph.Adj (leftVertex i) (TarjanWitness.selector j) := by
  decide

theorem bounded_row : ∀ j : Fin 14, augmented 14 j < 2^25 := by decide

private theorem cut_row : ∀ (k j : Fin 14),
    cut (11+k.val) (augmented (k.val+1) j) = augmented k.val j := by decide

private theorem cut_nonzero : ∀ (k j : Fin 14), augmented k.val j ≠ 0 := by decide

private theorem mixed_row : ∀ k : Fin 14, (augmented (k.val+1) k).testBit (11+k.val) = true := by decide

private theorem lookup : ∀ t ∈ required, ∃ j : Fin 14, t = augmented 0 j := by decide

private theorem row_not_input : ∀ j : Fin 14, augmented 0 j ∉ inputs := by decide

theorem strip (k : Nat) (bound : k ≤ 14) {gs : List Nat} (gen : Program (sources (11+k)) gs)
    (cover : ∀ j, augmented k j ∈ wires (sources (11+k)) gs) :
    ∃ es, Program inputs es ∧ (∀ t ∈ required, t ∈ es) ∧ es.length + k ≤ gs.length := by
  induction k generalizing gs with
  | zero =>
    have e : sources (11+0) = inputs := by decide
    refine ⟨gs,e ▸ gen,?_,by simp⟩
    intro t ht
    obtain ⟨j,rfl⟩ := lookup t ht
    have h := cover j
    rw [wires,e,List.mem_append] at h
    exact List.mem_reverse.mp (h.resolve_right (row_not_input j))
  | succ k ih =>
    let key : Fin 14 := ⟨k,by omega⟩
    have smix : ∃ x ∈ wires (sources ((11+k)+1)) gs,
        x.testBit (11+k) = true ∧ cut (11+k) x ≠ 0 := by
      exact ⟨augmented (k+1) key,cover key,mixed_row key,by rw [cut_row key key]; exact cut_nonzero key key⟩
    obtain ⟨es,hen,images,save⟩ := save_one (11+k) gen smix
    have cov (j : Fin 14) : augmented k j ∈ wires (sources (11+k)) es := by
      have e := cut_row key j
      change cut (11+k) (augmented (k+1) j) = augmented k j at e
      rw [← e]
      exact images _ (cover j) (fun h => cut_nonzero key j (e.symm.trans h))
    obtain ⟨gs',pg,good,len⟩ := ih (by omega) hen cov
    exact ⟨gs',pg,good,by omega⟩

end TarjanRows

namespace TarjanMasks
open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership
open TarjanTrace TarjanTrace.TraceBasics
open TarjanWitness.SumBound

abbrev Reach (n : Nat) (C : Circuit) := Relation.ReflTransGen (OrStep n C)

noncomputable def mask {n m : Nat} (C : Circuit) (embed : Fin m → Fin n) (w : Nat) : Nat := by
  classical
  exact (BitVec.ofBoolListLE (List.ofFn fun k => decide (Reach n C w (embed k).val))).toNat

theorem bit_mask {n m : Nat} (C : Circuit) (embed : Fin m → Fin n) (w j : Nat) :
    (mask C embed w).testBit j = true ↔ ∃ i : Fin m, i.val = j ∧ Reach n C w (embed i).val := by
  classical
  unfold mask
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  by_cases hj : j < m
  · simp [hj]
    constructor
    · intro h; exact ⟨⟨j,hj⟩,rfl,h⟩
    · rintro ⟨i,rfl,h⟩; exact h
  · simp [List.getElem?_ofFn,hj]
    intro i eq
    exact (hj (eq ▸ i.isLt)).elim

theorem mask_nonzero {n m : Nat} {C : Circuit} {e : Fin m → Fin n} {w : Nat} :
    mask C e w ≠ 0 ↔ ∃ i, Reach n C w (e i).val := by
  constructor
  · contrapose!
    intro none
    apply Nat.eq_of_testBit_eq
    intro j
    cases h : (mask C e w).testBit j
    · simp
    · obtain ⟨i,_,hi⟩ := (bit_mask _ _ _ _).mp h
      exact (none i hi).elim
  · rintro ⟨i,hi⟩ h
    have bit := (bit_mask _ _ _ _).mpr ⟨i,rfl,hi⟩
    simp [h] at bit

private theorem reach_input {n : Nat} {C : Circuit} {w z : Nat} (hw : w < n) :
    Reach n C w z ↔ w = z := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with eq | ⟨_,⟨k,_,he,_⟩,_⟩
    · exact eq
    · omega
  · rintro rfl
    exact Relation.ReflTransGen.refl

theorem source_mask {n m : Nat} {C : Circuit} (e : Fin m → Fin n) (inj : Function.Injective e)
    {w : Nat} (hw : w < n) (nonzero : mask C e w ≠ 0) :
    mask C e w ∈ (List.range m).map (fun j => 2^j) := by
  obtain ⟨i,hi⟩ := mask_nonzero.mp nonzero
  have he := (reach_input hw).mp hi
  apply List.mem_map.mpr
  refine ⟨i.val,List.mem_range.mpr i.isLt,?_⟩
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.mpr
  rw [Nat.testBit_two_pow, decide_eq_true_eq, bit_mask]
  constructor
  · rintro rfl; exact ⟨i,rfl,hi⟩
  · rintro ⟨t,rfl,ht⟩
    exact congrArg Fin.val (inj (Fin.ext (he.symm.trans ((reach_input hw).mp ht))))

private theorem reach_gate {n : Nat} {C : Circuit} {i : Nat} (hi : i < C.gates.length)
    (legal : TopForm.IsAO2 n C) {p q : Nat} (ins : (gateAt C i).inputs = [p,q]) (t : Fin n) :
    Reach n C (n+i) t.val ↔ (gateAt C i).op = .or ∧ (Reach n C p t.val ∨ Reach n C q t.val) := by
  constructor
  · intro path
    rcases Relation.ReflTransGen.cases_head path with eq | ⟨w,⟨k,hk,eq,op,hw,_⟩,tail⟩
    · have := t.isLt; omega
    · have eqi : i = k := by omega
      subst k; rw [ins] at hw
      rcases List.mem_cons.mp hw with rfl | h
      · exact ⟨op,Or.inl tail⟩
      · have e : w = q := by simpa using h
        exact ⟨op,Or.inr (e ▸ tail)⟩
  · rintro ⟨op,h | h⟩
    · have hp : p ∈ (gateAt C i).inputs := by simp [ins]
      exact Relation.ReflTransGen.head ⟨i,hi,rfl,op,hp,legal.2.1 i hi p hp⟩ h
    · have hq : q ∈ (gateAt C i).inputs := by simp [ins]
      exact Relation.ReflTransGen.head ⟨i,hi,rfl,op,hq,legal.2.1 i hi q hq⟩ h

theorem mask_join {n m : Nat} {C : Circuit} (e : Fin m → Fin n) {i p q : Nat}
    (hi : i < C.gates.length) (legal : TopForm.IsAO2 n C) (op : (gateAt C i).op = .or)
    (ins : (gateAt C i).inputs = [p,q]) :
    mask C e (n+i) = mask C e p ||| mask C e q := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.mpr
  rw [Nat.testBit_or, Bool.or_eq_true, bit_mask, bit_mask, bit_mask]
  constructor
  · rintro ⟨k,hk,h⟩
    rcases ((reach_gate hi legal ins _).mp h).2 with hp | hq
    · exact Or.inl ⟨k,hk,hp⟩
    · exact Or.inr ⟨k,hk,hq⟩
  · rintro (⟨k,hk,hp⟩ | ⟨k,hk,hq⟩)
    · exact ⟨k,hk,(reach_gate hi legal ins _).mpr ⟨op,Or.inl hp⟩⟩
    · exact ⟨k,hk,(reach_gate hi legal ins _).mpr ⟨op,Or.inr hq⟩⟩

def Pure {n m l : Nat} (C : Circuit) (a : Fin m → Fin n) (b : Fin l → Fin n) (w : Nat) :=
  mask C a w ≠ 0 ∧ mask C b w = 0

noncomputable def pureGates {n m l : Nat} (C : Circuit) (a : Fin m → Fin n) (b : Fin l → Fin n)
    (limit : Nat) : Finset Nat := by
  classical
  exact (Finset.range limit).filter (fun i => Pure C a b (n+i))

theorem emit_pure {n m l : Nat} {C : Circuit} (a : Fin m → Fin n) (b : Fin l → Fin n)
    (inj : Function.Injective a) (legal : TopForm.IsAO2 n C) (limit : Nat) (bound : limit ≤ C.gates.length) :
    ∃ gs, Program ((List.range m).map (fun j => 2^j)) gs ∧
      gs.length ≤ (pureGates C a b limit).card ∧
      ∀ w < n+limit, Pure C a b w → mask C a w ∈ gs.reverse ++ (List.range m).map (fun j => 2^j) := by
  classical
  let av := (List.range m).map (fun j => 2^j)
  induction limit with
  | zero =>
    refine ⟨[],trivial,by simp,?_⟩
    intro w hw h
    simpa using source_mask a inj (by simpa using hw) h.1
  | succ k ih =>
    have hk : k < C.gates.length := by omega
    obtain ⟨gs,hg,cost,values⟩ := ih (by omega)
    by_cases hp : Pure C a b (n+k)
    · have card : (pureGates C a b (k+1)).card = (pureGates C a b k).card + 1 := by
        simp [pureGates, Finset.range_add_one, Finset.filter_insert, hp]
      obtain ⟨p,q,ins⟩ := List.length_eq_two.mp (legal.2.2 _ (gateAt_mem hk))
      have pp : p < n+k := legal.2.1 k hk p (by simp [ins])
      have pq : q < n+k := legal.2.1 k hk q (by simp [ins])
      obtain ⟨i,reach⟩ := mask_nonzero.mp hp.1
      have op := ((reach_gate hk legal ins _).mp reach).1
      have va := mask_join a hk legal op ins
      have vb := mask_join b hk legal op ins
      have both0 := hp.2
      rw [vb] at both0
      have zp : mask C b p = 0 := by have := @Nat.left_le_or (mask C b p) (mask C b q); omega
      have zq : mask C b q = 0 := by have := @Nat.right_le_or (mask C b p) (mask C b q); omega
      let out := mask C a (n+k)
      have emit (outMem : out ∈ gs.reverse ++ av) :
          ∃ more, Program av more ∧ more.length ≤ (pureGates C a b (k+1)).card ∧
          ∀ w < n+(k+1), Pure C a b w → mask C a w ∈ more.reverse ++ av := by
        refine ⟨gs,hg,by omega,?_⟩
        intro w hw hwgood
        by_cases last : w = n+k
        · subst w; exact outMem
        · exact values w (by omega) hwgood
      by_cases ap : mask C a p = 0
      · have apq : mask C a q ≠ 0 := by intro z; exact hp.1 (by simp [va,ap,z])
        exact emit (by simpa [out,va,ap,av] using values q pq ⟨apq,zq⟩)
      by_cases aq : mask C a q = 0
      · exact emit (by simpa [out,va,aq,av] using values p pp ⟨ap,zp⟩)
      have add (av0 gs0 : List Nat) (h0 : Program av0 gs0) {z} (gen : ∃ x ∈ gs0.reverse ++ av0,
          ∃ y ∈ gs0.reverse ++ av0, x ||| y = z) : Program av0 (gs0 ++ [z]) := by
        induction gs0 generalizing av0 with
        | nil => exact ⟨by simpa using gen,trivial⟩
        | cons g tail ih => exact ⟨h0.1, ih _ h0.2 (by simpa [List.append_assoc] using gen)⟩
      refine ⟨gs ++ [out],add _ _ hg ⟨_,values p pp ⟨ap,zp⟩,_,values q pq ⟨aq,zq⟩,va.symm⟩,by simp; omega,?_⟩
      intro w hw hwgood
      by_cases last : w = n+k
      · subst w; simp [out]
      · have found := values w (by omega) hwgood
        simpa [out,List.append_assoc] using (List.mem_cons_of_mem out found)
    · have card : pureGates C a b (k+1) = pureGates C a b k := by
        simp [pureGates, Finset.range_add_one, Finset.filter_insert, hp]
      refine ⟨gs,hg,by simpa [card] using cost,?_⟩
      intro w hw hwgood
      have notLast : w ≠ n+k := fun e => hp (e ▸ hwgood)
      exact values w (by omega) hwgood

end TarjanMasks

namespace TarjanRectangles

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership
open TarjanTrace TarjanTrace.TraceBasics TarjanMasks TarjanWitness TarjanRows
open TarjanWitness.SumBound.Reverse

private theorem no_left (u v : Fin 25) : ¬ graph.Adj (leftVertex u) (leftVertex v) := by
  intro h
  have ls (u : Fin 25) : TarjanWitness.side (leftVertex u) = false := by
    simp [TarjanWitness.side,leftVertex, Nat.not_le_of_lt u.isLt]
  exact bipartite _ _ h (by rw [ls,ls])

private theorem no_right (u v : Fin 14) : ¬ graph.Adj (selector u) (selector v) := by
  intro h
  exact bipartite _ _ h (by simp [TarjanWitness.side,selector])

abbrev w0 (C : Circuit) (i : Nat) := TopForm.opnd C i 0
abbrev w1 (C : Circuit) (i : Nat) := TopForm.opnd C i 1

noncomputable def orient (C : Circuit) (i : Nat) : Nat × Nat := by
  classical
  exact if mask C leftVertex (w0 C i) ≠ 0 then (w0 C i,w1 C i) else (w1 C i,w0 C i)

def usable (C : Circuit) (i : Nat) :=
  Pure C leftVertex selector (orient C i).1 ∧ Pure C selector leftVertex (orient C i).2

noncomputable def kept (C : Circuit) : Finset Nat := by
  classical
  exact (upperGates 39 C .and).filter (usable C)

theorem mem_kept {C : Circuit} {i : Nat} : i ∈ kept C ↔ live (n := 39) C i ∧ usable C i := by
  classical
  simp [kept,mem_upperGates,live]

theorem cross (C : Circuit) (legal : TopForm.IsAO2 39 C) (eqn : circuitFun 39 C = graphFun graph ∅)
    {i : Nat} (li : live (n := 39) C i) {s t : Fin 39}
    (a : Reach 39 C (orient C i).1 s.val) (b : Reach 39 C (orient C i).2 t.val) : graph.Adj s t := by
  classical
  by_cases h : mask C leftVertex (w0 C i) ≠ 0
  · exact cross_edge graph legal eqn li (by simpa [sees,orient,h] using a) (by simpa [sees,orient,h] using b)
  · exact (cross_edge graph legal eqn li (by simpa [sees,orient,h] using b) (by simpa [sees,orient,h] using a)).symm

private theorem measurable {C : Circuit} (legal : TopForm.IsAO2 39 C) (eqn : circuitFun 39 C = graphFun graph ∅)
    {i : Nat} (li : live (n := 39) C i) {u : Fin 25} {v : Fin 14}
    (pair : (sees C i 0 (leftVertex u) ∧ sees C i 1 (selector v)) ∨
      (sees C i 0 (selector v) ∧ sees C i 1 (leftVertex u))) :
    i ∈ kept C ∧ Reach 39 C (orient C i).1 (leftVertex u).val ∧ Reach 39 C (orient C i).2 (selector v).val := by
  classical
  have oriented : Reach 39 C (orient C i).1 (leftVertex u).val ∧
      Reach 39 C (orient C i).2 (selector v).val := by
    rcases pair with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · have pos : mask C leftVertex (w0 C i) ≠ 0 := mask_nonzero.mpr ⟨u,hu⟩
      rw [orient, if_pos pos]; exact ⟨hu,hv⟩
    · have zero : mask C leftVertex (w0 C i) = 0 := by
        by_contra nz
        obtain ⟨l,hl⟩ := mask_nonzero.mp nz
        exact no_left l u (cross_edge graph legal eqn li hl hu)
      rw [orient, if_neg (not_not_intro zero)]; exact ⟨hu,hv⟩
  have left0 : mask C selector (orient C i).1 = 0 := by
    by_contra nz
    obtain ⟨r,hr⟩ := mask_nonzero.mp nz
    exact no_right r v (cross C legal eqn li hr oriented.2)
  have right0 : mask C leftVertex (orient C i).2 = 0 := by
    by_contra nz
    obtain ⟨l,hl⟩ := mask_nonzero.mp nz
    exact no_left u l (cross C legal eqn li oriented.1 hl)
  exact ⟨mem_kept.mpr ⟨li,⟨mask_nonzero.mpr ⟨u,oriented.1⟩,left0⟩,
    ⟨mask_nonzero.mpr ⟨v,oriented.2⟩,right0⟩⟩,oriented⟩

noncomputable def requests (C : Circuit) : List Request :=
  (kept C).toList.map fun i => (mask C selector (orient C i).2, mask C leftVertex (orient C i).1)

theorem request_count (C : Circuit) : (requests C).length ≤ (upperGates 39 C .and).card := by
  classical
  simpa [requests] using Finset.card_le_card (show kept C ⊆ upperGates 39 C .and from Finset.filter_subset _ _)

theorem bit_contribution (rs : List Request) (j t : Nat) :
    (contribution rs j).testBit t = true ↔ ∃ p ∈ rs, p.1.testBit j = true ∧ p.2.testBit t = true := by
  induction rs with
  | nil => simp [contribution]
  | cons p ps ih =>
    change ((if p.1.testBit j then p.2 else 0) ||| contribution ps j).testBit t = true ↔ _
    cases he : p.1.testBit j <;> simp [Nat.testBit_or,ih,he]

theorem row_exact {C : Circuit} (legal : TopForm.IsAO2 39 C) (eqn : circuitFun 39 C = graphFun graph ∅)
    (flat : singleLevel C) (j : Fin 14) : contribution (requests C) j.val = augmented 14 j := by
  apply Nat.eq_of_testBit_eq
  intro t
  apply Bool.eq_iff_iff.mpr
  rw [bit_contribution]
  constructor
  · rintro ⟨p,hp,hr,hl⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    obtain ⟨l,lt,pathL⟩ := (bit_mask C leftVertex _ t).mp hl
    obtain ⟨r,rt,pathR⟩ := (bit_mask C selector _ j.val).mp hr
    have eqr : r = j := Fin.ext rt
    subst r
    rw [← lt]
    exact (edge_bit l j).mpr (cross C legal eqn (mem_kept.mp (Finset.mem_toList.mp hi)).1 pathL pathR)
  · intro bit
    have lt : t < 25 := by
      by_contra! ge
      have he := Nat.ge_two_pow_of_testBit bit
      have hpow : (2:Nat)^25 ≤ 2^t := Nat.pow_le_pow_right (by decide) ge
      have := bounded_row j
      omega
    let l : Fin 25 := ⟨t,lt⟩
    have adj := (edge_bit l j).mp bit
    obtain ⟨i,hi,orientCases⟩ := edge_covered graph legal eqn flat adj
    obtain ⟨kept_i,hl,hr⟩ := measurable legal eqn hi orientCases
    exact ⟨_,List.mem_map.mpr ⟨i,Finset.mem_toList.mpr kept_i,rfl⟩,
      (bit_mask _ _ _ _).mpr ⟨j,rfl,hr⟩,(bit_mask _ _ _ _).mpr ⟨l,rfl,hl⟩⟩

end TarjanRectangles

namespace TarjanBudget

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership
open TarjanTrace TarjanTrace.TraceBasics TarjanMasks TarjanWitness TarjanRows

private theorem unreachable_input {C : Circuit} (eqn : circuitFun 39 C = graphFun graph ∅)
    (x : Fin 39) : ¬Reach 39 C C.output x.val := by
  intro reach
  have yes := reach_var_val (pairInput x x) C.output x reach (pairInput_left x x)
  change circuitFun 39 C (pairInput x x) = true at yes
  rw [eqn] at yes
  exact graph.irrefl ((graphFun_pair graph x x).mp yes)

private theorem disjoint_top {C : Circuit} (eqn : circuitFun 39 C = graphFun graph ∅)
    {m l : Nat} (a : Fin m → Fin 39) (b : Fin l → Fin 39) (op : GateOp) :
    Disjoint (pureGates C a b C.gates.length) (upperGates 39 C op) := by
  classical
  rw [Finset.disjoint_left]
  intro i hp ht
  have good := (Finset.mem_filter.mp hp).2
  obtain ⟨v,hv⟩ := mask_nonzero.mp good.1
  exact unreachable_input eqn (a v) ((mem_upperGates.mp ht).2.2.trans hv)

theorem budget {C : Circuit} (eqn : circuitFun 39 C = graphFun graph ∅) :
    (pureGates C leftVertex selector C.gates.length).card +
    (pureGates C selector leftVertex C.gates.length).card +
    (upperGates 39 C .and).card + (upperGates 39 C .or).card ≤ C.size := by
  classical
  let L := pureGates C leftVertex selector C.gates.length
  let R := pureGates C selector leftVertex C.gates.length
  let A := upperGates 39 C .and
  let O := upperGates 39 C .or
  have lr : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro i hl hr
    exact (Finset.mem_filter.mp hl).2.1 (Finset.mem_filter.mp hr).2.2
  have ao : Disjoint A O := by
    rw [Finset.disjoint_left]
    intro i ha ho
    exact GateOp.noConfusion ((mem_upperGates.mp ha).2.1.symm.trans (mem_upperGates.mp ho).2.1)
  have groups : Disjoint (L ∪ R) (A ∪ O) := by
    rw [Finset.disjoint_union_left,Finset.disjoint_union_right,Finset.disjoint_union_right]
    exact ⟨⟨disjoint_top eqn _ _ _,disjoint_top eqn _ _ _⟩,⟨disjoint_top eqn _ _ _,disjoint_top eqn _ _ _⟩⟩
  have sub : (L ∪ R) ∪ (A ∪ O) ⊆ Finset.range C.gates.length := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_union.mp h with h | h <;> exact (Finset.mem_filter.mp h).1
    · rcases Finset.mem_union.mp h with h | h <;> exact Finset.mem_range.mpr (mem_upperGates.mp h).1
  have count := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint groups,Finset.card_union_of_disjoint lr,Finset.card_union_of_disjoint ao,
    Finset.card_range] at count
  change L.card + R.card + A.card + O.card ≤ C.gates.length
  omega

end TarjanBudget

namespace TarjanEnd

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership
open TarjanTrace TarjanTrace.TraceBasics TarjanMasks TarjanWitness TarjanRows TarjanRectangles
open TarjanWitness.SumBound TarjanWitness.SumBound.Projection
open TarjanWitness.SumBound.Reverse

private theorem opnd_bound {C : Circuit} (legal : TopForm.IsAO2 39 C) {i : Nat}
    (hi : i < C.gates.length) (b : Fin 2) : TopForm.opnd C i b < 39+C.gates.length := by
  obtain ⟨p,q,ins⟩ := List.length_eq_two.mp (legal.2.2 _ (gateAt_mem hi))
  have h : TopForm.opnd C i b ∈ (gateAt C i).inputs := by fin_cases b <;> simp [TopForm.opnd,ins]
  have := legal.2.1 i hi _ h
  omega

private theorem upperRows {C : Circuit} (legal : TopForm.IsAO2 39 C) (eqn : circuitFun 39 C = graphFun graph ∅)
    (flat : singleLevel C) :
    ∃ gs, Program (sources 25) gs ∧ (∀ j, augmented 14 j ∈ wires (sources 25) gs) ∧
      gs.length + 14 ≤ (pureGates C leftVertex selector C.gates.length).card +
        (pureGates C selector leftVertex C.gates.length).card + (upperGates 39 C .and).card := by
  classical
  obtain ⟨gl,legalL,cL,getL⟩ := emit_pure leftVertex selector var_inj legal C.gates.length le_rfl
  obtain ⟨gr,legalR,cR,getR⟩ := emit_pure selector leftVertex sel_inj legal C.gates.length le_rfl
  have reqOK : valid (pool (sources 14) gr) (pool (sources 25) gl) (requests C) := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨live, good⟩ := mem_kept.mp (Finset.mem_toList.mp hi)
    have limits : (orient C i).1 < 39+C.gates.length ∧ (orient C i).2 < 39+C.gates.length := by
      by_cases h : mask C leftVertex (w0 C i) ≠ 0
      · simpa [orient,h] using And.intro (opnd_bound legal live.1 0) (opnd_bound legal live.1 1)
      · simpa [orient,h] using And.intro (opnd_bound legal live.1 1) (opnd_bound legal live.1 0)
    exact ⟨getR _ limits.2 good.2,getL _ limits.1 good.1⟩
  obtain ⟨ge,next,extra,typed,values,countE⟩ := transpose legalR (pool (sources 25) gl) (requests C) reqOK
  have col (j : Fin 14) : atKey (2^j.val) next = augmented 14 j := by
    have hc : ∀ p ∈ next, p.1.testBit j.val = (p.1 == 2^j.val) := by
      intro p hp
      obtain ⟨k,_,h⟩ := List.mem_map.mp (typed p hp).1
      rw [← h,Nat.testBit_two_pow]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,beq_iff_eq]
      exact ⟨fun eq => eq ▸ rfl,fun eq => (Nat.pow_right_injective (by decide : 1 < (2:Nat))) eq⟩
    rw [← column next j.val hc,← values j.val,row_exact legal eqn flat]
  have needed (v : Nat) (hv : v ∈ sources 14) : select v next ≠ [] := by
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
    let q : Fin 14 := ⟨j,List.mem_range.mp hj⟩
    intro empty
    have eq := col q
    have nonzero : ∀ k : Fin 14, augmented 14 k ≠ 0 := by decide
    apply nonzero q
    rw [← eq]
    unfold atKey
    change total ((select (2^j) next).map Prod.snd) = 0
    rw [empty]; rfl
  have nodup : (sources 14).Nodup := by decide
  obtain ⟨gd,drained,outputs,countD⟩ :=
    drain (sources 14) nodup (pool (pool (sources 25) gl) ge) next (fun p h => (typed p h).2) needed
  have len : (sources 14).length = 14 := rfl
  have ck := request_count C
  refine ⟨gl ++ (ge ++ gd),extendProgram _ _ legalL (extendProgram _ _ extra drained),?_,?_⟩
  · intro j
    have hj : 2^j.val ∈ sources 14 := List.mem_map.mpr ⟨j.val,List.mem_range.mpr j.isLt,rfl⟩
    have h := outputs _ hj
    rw [col j] at h
    simpa [pool,wires,List.append_assoc] using h
  · simp only [List.length_append]; omega

theorem lower {C : Circuit} (legal : TopForm.IsAO2 39 C) (eqn : circuitFun 39 C = graphFun graph ∅)
    (flat : singleLevel C) : 59 ≤ C.size := by
  obtain ⟨gs,gen,cover,cost⟩ := upperRows legal eqn flat
  obtain ⟨es,proj,has,cut⟩ := strip 14 (by decide) gen cover
  have rows := or_lower proj has
  have all := TarjanBudget.budget eqn
  have ands := live_ands_ge_fourteen legal eqn flat
  have ors := top_count 39 C legal
  omega

end TarjanEnd

end PEqualNP.Outside.L_meta_3679

theorem PEqualNP.Outside.L_meta_3679 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C ∧
    PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧
    ∀ i < D.gates.length, ∀ j < D.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ¬ PEqualNP.EdgeOwnership.InCone n D i j) := by
  intro general
  apply PEqualNP.Outside.L_meta_3679.TarjanWitness.excludes_least (fun _ => PEqualNP.Outside.L_meta_3679.TarjanEnd.lower)
  exact general 39 PEqualNP.Outside.L_meta_3679.TarjanWitness.graph PEqualNP.Outside.L_meta_3679.TarjanWitness.side PEqualNP.Outside.L_meta_3679.TarjanWitness.bipartite
    ⟨PEqualNP.Outside.L_meta_3679.TarjanWitness.circuit, PEqualNP.Outside.L_meta_3679.TarjanWitness.legal, PEqualNP.Outside.L_meta_3679.TarjanWitness.computes⟩
