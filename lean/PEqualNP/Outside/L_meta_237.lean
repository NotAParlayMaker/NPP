import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_237_impl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A gate of fan-in at most two, read as a gate over the full binary basis. The binary basis
-- allows an arbitrary function of two bits, so the gate's own evaluator can be reused: the
-- two wires it reads are its first and second input (0 when absent), and the list handed to
-- the evaluator is cut back to the number of wires the gate actually reads.
def toBin (g : Gate) : BinaryGate where
  op := fun a b => g.op.eval (List.take g.inputs.length [a, b])
  left := g.inputs.getD 0 0
  right := g.inputs.getD 1 0

-- On any wire values, the translated gate agrees with the original. Only the fan-in bound is
-- used; which operation it is does not matter.
lemma gate_agree (g : Gate) (hg : g.inputs.length ≤ 2) (w : List Bool) :
    (toBin g).op (w.getD (toBin g).left false) (w.getD (toBin g).right false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  match g, hg with
  | ⟨_, []⟩, _ => simp [toBin]
  | ⟨_, [_]⟩, _ => simp [toBin]
  | ⟨_, [_, _]⟩, _ => simp [toBin]
  | ⟨_, _ :: _ :: _ :: _⟩, hg => simp at hg

-- Hence the two circuits give every wire the same value.
lemma wires_agree (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) (w : List Bool) :
    List.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w
        (gs.map toBin)
      = List.foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w gs := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [gate_agree g (h g (by simp))]
      exact ih (fun g' hg' => h g' (by simp [hg'])) _

end PEqualNP.Outside.L_meta_237_impl

theorem PEqualNP.Outside.L_meta_237 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ),
      PEqualNP.MetaComplexity.HasCircuitSize n f s →
      PEqualNP.MetaComplexity.HasBinarySize n f s := by
  intro n f s h
  obtain ⟨C, hfan, hsize, heval⟩ := h
  refine ⟨⟨C.gates.map PEqualNP.Outside.L_meta_237_impl.toBin, C.output⟩, ?_, ?_⟩
  · simpa [PEqualNP.MetaComplexity.BinaryCircuit.size,
      PEqualNP.CircuitLowerBounds.Circuit.size] using hsize
  · intro x
    have hx := heval x
    rw [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires] at hx
    rw [PEqualNP.MetaComplexity.BinaryCircuit.eval,
      PEqualNP.MetaComplexity.BinaryCircuit.wires,
      PEqualNP.Outside.L_meta_237_impl.wires_agree _ (fun g hg => (hfan g hg).2)]
    exact hx
