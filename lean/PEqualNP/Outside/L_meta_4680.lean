import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4680

open PEqualNP.CircuitLowerBounds

def dualOp : GateOp → GateOp
  | GateOp.and => GateOp.or
  | GateOp.or => GateOp.and
  | op => op

def remapWire (bound i : ℕ) : ℕ :=
  if i < bound then i + 1 else 0

def dualGate (bound : ℕ) (g : Gate) : Gate :=
  { op := dualOp g.op, inputs := g.inputs.map (remapWire bound) }

def dualGates : ℕ → List Gate → List Gate
  | _, [] => []
  | bound, g :: gs => dualGate bound g :: dualGates (bound + 1) gs

lemma dualGates_length (bound : ℕ) (gs : List Gate) :
    (dualGates bound gs).length = gs.length := by
  induction gs generalizing bound with
  | nil => rfl
  | cons g gs ih => simp [dualGates, ih]

lemma dualGates_monotone (bound : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ dualGates bound gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing bound with
  | nil =>
    intro g hg
    simp [dualGates] at hg
  | cons g gs ih =>
    intro g' hg'
    simp only [dualGates, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · have hg := h g (by simp)
      rcases hg with ⟨hop, hlen⟩
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
        rcases hop with h1 | h2
        · right; simp [dualGate, dualOp, h1]
        · left; simp [dualGate, dualOp, h2]
      · simpa [dualGate] using hlen
    · exact ih (bound + 1) (fun x hx => h x (by simp [hx])) g' hg'

lemma dualGates_getElem_op (bound : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    ((dualGates bound gs)[k]'(by rw [dualGates_length]; exact hk)).op = dualOp (gs[k]'hk).op := by
  induction gs generalizing bound k with
  | nil => simp at hk
  | cons g gs ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [dualGates, List.getElem_cons_succ]
      exact ih (bound + 1) k' (Nat.lt_of_succ_lt_succ hk)

lemma dualOp_eq_and_iff (op : GateOp)
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    dualOp op = GateOp.and ↔ op = GateOp.or := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl <;> simp [dualOp]

lemma getD_cons_map_not (w : List Bool) (i : ℕ) :
    (true :: w.map (! ·)).getD (remapWire w.length i) false = !(w.getD i false) := by
  by_cases hi : i < w.length
  · simp [remapWire, hi, List.getD_eq_getElem?_getD]
  · simp [remapWire, hi, List.getD_eq_getElem?_getD]

lemma list_any_map_not (l : List Bool) :
    (l.map (! ·)).any id = !(l.all id) := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [ih]

lemma list_all_map_not (l : List Bool) :
    (l.map (! ·)).all id = !(l.any id) := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [ih]

lemma eval_dualGate (w : List Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    (dualGate w.length g).op.eval
      ((dualGate w.length g).inputs.map (fun i => (true :: w.map (! ·)).getD i false)) =
    !(g.op.eval (g.inputs.map (fun i => w.getD i false))) := by
  have hmap : (dualGate w.length g).inputs.map (fun i => (true :: w.map (! ·)).getD i false) =
      (g.inputs.map (fun i => w.getD i false)).map (! ·) := by
    simp only [dualGate, List.map_map, Function.comp_def]
    congr 1
    funext i
    exact getD_cons_map_not w i
  rw [hmap]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hop | hop
  · simp only [dualGate, dualOp, hop, GateOp.eval]
    exact list_any_map_not (g.inputs.map (fun i => w.getD i false))
  · simp only [dualGate, dualOp, hop, GateOp.eval]
    exact list_all_map_not (g.inputs.map (fun i => w.getD i false))

lemma foldl_dualGates (gs : List Gate) (w : List Bool)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    (dualGates w.length gs).foldl
      (fun u g => u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])
      (true :: w.map (! ·)) =
    true :: (gs.foldl
      (fun u g => u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])
      w).map (! ·) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [dualGates, List.foldl_cons]
    have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := h g (by simp)
    have hgs : ∀ x ∈ gs, x.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun x hx => h x (by simp [hx])
    rw [eval_dualGate w g hg]
    have hstep : (true :: w.map (! ·)) ++
        [!(g.op.eval (g.inputs.map fun i => w.getD i false))] =
        true :: (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).map (! ·) := by
      simp [List.map_append]
    rw [hstep]
    have hlen : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1 := by
      simp
    rw [← hlen]
    exact ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) hgs

lemma foldl_wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun u g => u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma ofFn_fin_cases (x4 : Fin 26 → Bool) :
    List.ofFn (fun (x5 : Fin ((26 : ℕ) + (1 : ℕ))) =>
      Fin.cases Bool.true (fun (x6 : Fin (26 : ℕ)) => !x4 x6) x5) =
    true :: (List.ofFn x4).map (! ·) := by
  rw [List.ofFn_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, List.map_ofFn, Function.comp_def]

end PEqualNP.Outside.L_meta_4680

theorem PEqualNP.Outside.L_meta_4680 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ Nat.card { x4 : Fin x3.gates.length // (x3.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and } ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x3 fun (x5 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.cases Bool.true (fun (x6 : Fin (26 : ℕ)) => !x4 x6) x5) = !PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x4 := by
  intro x1 hx1
  refine ⟨{ gates := PEqualNP.Outside.L_meta_4680.dualGates 26 x1.gates
            output := PEqualNP.Outside.L_meta_4680.remapWire (26 + x1.gates.length) x1.output }, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_4680.dualGates_monotone 26 x1.gates hx1
  · have hlen : (PEqualNP.Outside.L_meta_4680.dualGates 26 x1.gates).length = x1.gates.length :=
      PEqualNP.Outside.L_meta_4680.dualGates_length 26 x1.gates
    let e : { x4 : Fin (PEqualNP.Outside.L_meta_4680.dualGates 26 x1.gates).length //
          ((PEqualNP.Outside.L_meta_4680.dualGates 26 x1.gates).get x4).op =
            PEqualNP.CircuitLowerBounds.GateOp.and } ≃
        { x4 : Fin x1.gates.length //
          (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or } :=
      { toFun := fun x => ⟨x.1.cast hlen, by
          have hx := x.2
          simp only [List.get_eq_getElem] at hx ⊢
          rw [PEqualNP.Outside.L_meta_4680.dualGates_getElem_op 26 x1.gates x.1.1 (hlen ▸ x.1.2)] at hx
          exact (PEqualNP.Outside.L_meta_4680.dualOp_eq_and_iff _ (hx1 (x1.gates[x.1.1]'(hlen ▸ x.1.2)) (List.getElem_mem _)).1).mp hx⟩
        invFun := fun y => ⟨y.1.cast hlen.symm, by
          have hy := y.2
          simp only [List.get_eq_getElem, Fin.val_cast] at hy ⊢
          rw [PEqualNP.Outside.L_meta_4680.dualGates_getElem_op 26 x1.gates y.1.1 y.1.2]
          exact (PEqualNP.Outside.L_meta_4680.dualOp_eq_and_iff _ (hx1 (x1.gates[y.1.1]'y.1.2) (List.getElem_mem _)).1).mpr hy⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun y => by ext; rfl }
    rw [Set.ncard_def]
    exact le_of_eq (Nat.card_congr e)
  · intro x4
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires]
    rw [PEqualNP.Outside.L_meta_4680.ofFn_fin_cases x4]
    have hlen26 : (List.ofFn x4).length = 26 := List.length_ofFn
    have hfold := PEqualNP.Outside.L_meta_4680.foldl_dualGates x1.gates (List.ofFn x4)
      (fun g hg => (hx1 g hg).1)
    rw [hlen26] at hfold
    rw [hfold]
    have hwlen : (x1.gates.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x4)).length = 26 + x1.gates.length := by
      rw [PEqualNP.Outside.L_meta_4680.foldl_wires_length, hlen26]
    rw [← hwlen]
    exact PEqualNP.Outside.L_meta_4680.getD_cons_map_not _ x1.output
