import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_237_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def translateGate (g : Gate) : BinaryGate :=
  match g.op, g.inputs with
  | .and, [] => ⟨fun _ _ => true, 0, 0⟩
  | .and, [i] => ⟨fun a _ => a, i, 0⟩
  | .and, i :: j :: _ => ⟨fun a b => a && b, i, j⟩
  | .or, [] => ⟨fun _ _ => false, 0, 0⟩
  | .or, [i] => ⟨fun a _ => a, i, 0⟩
  | .or, i :: j :: _ => ⟨fun a b => a || b, i, j⟩
  | .not, [] => ⟨fun _ _ => true, 0, 0⟩
  | .not, i :: _ => ⟨fun a _ => !a, i, 0⟩
  | _, _ => ⟨fun _ _ => false, 0, 0⟩

theorem translateGate_eval (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) :
    (translateGate g).op (w.getD (translateGate g).left false)
      (w.getD (translateGate g).right false) =
    g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  cases op with
  | and =>
    match ins, hlen with
    | [], _ => rfl
    | [i], _ => simp [translateGate, GateOp.eval]
    | [i, j], _ => simp [translateGate, GateOp.eval]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => rfl
    | [i], _ => simp [translateGate, GateOp.eval]
    | [i, j], _ => simp [translateGate, GateOp.eval]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil => rfl
    | cons i is => simp [translateGate, GateOp.eval]
  | mod m => simp at hop
  | maj => simp at hop

theorem translateGates_wires (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) :
    (gs.map translateGate).foldl
      (fun acc bg => acc ++ [bg.op (acc.getD bg.left false) (acc.getD bg.right false)]) w =
    gs.foldl
      (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := translateGate_eval g (hgs g List.mem_cons_self) w
    rw [hg]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _

theorem main (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (h : HasCircuitSize n f s) : HasBinarySize n f s := by
  obtain ⟨C, hfan, hsize, heval⟩ := h
  refine ⟨⟨C.gates.map translateGate, C.output⟩, ?_, ?_⟩
  · simpa [BinaryCircuit.size, Circuit.size] using hsize
  · intro x
    have hw := translateGates_wires C.gates hfan (List.ofFn x)
    change ((C.gates.map translateGate).foldl
      (fun acc bg => acc ++ [bg.op (acc.getD bg.left false) (acc.getD bg.right false)])
      (List.ofFn x)).getD C.output false = f x
    rw [hw]
    exact heval x

end PEqualNP.Outside.L_meta_237_aux

theorem PEqualNP.Outside.L_meta_237 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasCircuitSize n f s → PEqualNP.MetaComplexity.HasBinarySize n f s :=
  PEqualNP.Outside.L_meta_237_aux.main
