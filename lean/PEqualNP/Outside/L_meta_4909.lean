import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4909

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def clamp25 (n : ℕ) : Fin 25 :=
  ⟨min n 24, Nat.lt_succ_of_le (Nat.min_le_right n 24)⟩

def decodeGate (w : Fin 3 × Fin 3 × Fin 25 × Fin 25) : Gate :=
  { op := if w.1 = (0 : Fin 3) then GateOp.and
          else if w.1 = (1 : Fin 3) then GateOp.or
          else GateOp.not,
    inputs := List.take ↑w.2.1 [↑w.2.2.1, ↑w.2.2.2] }

def encodeOp (op : GateOp) : Fin 3 :=
  match op with
  | GateOp.and => 0
  | GateOp.or => 1
  | _ => 2

def encodeGate (g : Gate) : Fin 3 × Fin 3 × Fin 25 × Fin 25 :=
  (encodeOp g.op,
   ⟨min g.inputs.length 2, Nat.lt_succ_of_le (Nat.min_le_right g.inputs.length 2)⟩,
   clamp25 (g.inputs.getD 0 0),
   clamp25 (g.inputs.getD 1 0))

def encodeGates (x1 : Circuit) (hsize : x1.size = 13) :
    Fin 13 → Fin 3 × Fin 3 × Fin 25 × Fin 25 :=
  fun i => encodeGate (x1.gates[i.val]'(by
    change x1.gates.length = 13 at hsize
    omega))

lemma getD_clamp25 (w : List Bool) (hw : w.length ≤ 24) (i : ℕ) :
    w.getD (clamp25 i).val false = w.getD i false := by
  simp only [clamp25, List.getD_eq_getElem?_getD]
  by_cases h : i ≤ 24
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (Nat.le_of_not_le h),
        List.getElem?_eq_none hw,
        List.getElem?_eq_none (by omega)]

lemma decodeGate_op (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (decodeGate (encodeGate g)).op = g.op := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp [decodeGate, encodeGate, encodeOp, h]
  · simp [decodeGate, encodeGate, encodeOp, h]
  · simp only [decodeGate, encodeGate, encodeOp, h]
    rw [if_neg (by decide), if_neg (by decide)]

lemma decodeGate_eval_eq (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (w : List Bool) (hw : w.length ≤ 24) :
    (decodeGate (encodeGate g)).op.eval
        ((decodeGate (encodeGate g)).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rw [decodeGate_op g hop]
  congr 1
  cases h : g.inputs with
  | nil =>
    simp [decodeGate, encodeGate, h]
  | cons a t =>
    cases t with
    | nil =>
      simp [decodeGate, encodeGate, h]
      simpa only [List.getD_eq_getElem?_getD] using getD_clamp25 w hw a
    | cons b u =>
      cases u with
      | nil =>
        simp [decodeGate, encodeGate, h]
        exact ⟨by simpa only [List.getD_eq_getElem?_getD] using getD_clamp25 w hw a,
               by simpa only [List.getD_eq_getElem?_getD] using getD_clamp25 w hw b⟩
      | cons c v =>
        simp [h] at hlen

lemma ofFn_eq_map_encode (x1 : Circuit) (hsize : x1.size = 13) :
    (List.ofFn fun i : Fin 13 => decodeGate (encodeGates x1 hsize i)) =
      x1.gates.map (fun g => decodeGate (encodeGate g)) := by
  have hlen : x1.gates.length = 13 := hsize
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, hlen]
  · intro i hi1 hi2
    simp only [List.getElem_ofFn, List.getElem_map]
    rfl

lemma length_foldl_wires (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_map (gs : List Gate) (w : List Bool)
    (hfan : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hlen : w.length + gs.length ≤ 24) :
    (gs.map (fun g => decodeGate (encodeGate g))).foldl
        (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w =
      gs.foldl
        (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := hfan g (List.mem_cons_self ..)
    have hw24 : w.length ≤ 24 := by
      simp only [List.length_cons] at hlen
      omega
    rw [decodeGate_eval_eq g hg.1 hg.2 w hw24]
    apply ih
    · intro g' hg'
      exact hfan g' (List.mem_cons_of_mem g hg')
    · simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
      omega

lemma main_proof (x1 : Circuit) (hfan : FanInTwo x1) (hsize : x1.size = 13) :
    ∀ (x8 : List Bool), x8.length = 11 →
      ({ gates := List.ofFn fun i : Fin 13 => decodeGate (encodeGates x1 hsize i),
         output := (clamp25 x1.output).val } : Circuit).eval x8 = x1.eval x8 := by
  intro x8 hx8
  have hlen : x1.gates.length = 13 := hsize
  have hwires :
      ({ gates := List.ofFn fun i : Fin 13 => decodeGate (encodeGates x1 hsize i),
         output := (clamp25 x1.output).val } : Circuit).wires x8 = x1.wires x8 := by
    simp only [Circuit.wires]
    rw [ofFn_eq_map_encode x1 hsize]
    exact foldl_wires_map x1.gates x8 hfan (by omega)
  simp only [Circuit.eval, hwires]
  have hwl : (x1.wires x8).length ≤ 24 := by
    simp only [Circuit.wires, length_foldl_wires]
    omega
  exact getD_clamp25 (x1.wires x8) hwl x1.output

end PEqualNP.Outside.L_meta_4909

theorem PEqualNP.Outside.L_meta_4909 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (13 : ℕ) →       ∃ (x4 : Fin (13 : ℕ) → Fin (3 : ℕ) × Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)),         have x6 : Fin (3 : ℕ) × Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ) → PEqualNP.CircuitLowerBounds.Gate := fun (x6 : Fin (3 : ℕ) × Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ)) => { op := if x6.1 = (0 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.and else if x6.1 = (1 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.not, inputs := List.take ↑x6.2.1 [↑x6.2.2.1, ↑x6.2.2.2] : PEqualNP.CircuitLowerBounds.Gate };         have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x7 : Fin (13 : ℕ)) => x6 (x4 x7), output := ↑x5 : PEqualNP.CircuitLowerBounds.Circuit };         ∀ (x8 : List Bool), x8.length = (11 : ℕ) → x7.eval x8 = x1.eval x8 := by
  intro x1 hfan hsize
  exact ⟨PEqualNP.Outside.L_meta_4909.encodeGates x1 hsize,
    PEqualNP.Outside.L_meta_4909.clamp25 x1.output,
    PEqualNP.Outside.L_meta_4909.main_proof x1 hfan hsize⟩
