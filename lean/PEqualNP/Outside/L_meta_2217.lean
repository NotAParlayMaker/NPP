import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2217_aux

open PEqualNP.CircuitLowerBounds

def sh (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun i => i + 1)⟩

theorem fold_shift (b : Bool) (gs : List Gate) : ∀ w : List Bool,
    (gs.map sh).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (b :: w)
      = b :: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih]
    congr 1
    simp [sh, List.map_map, Function.comp_def]

theorem fold_len (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp; omega

end PEqualNP.Outside.L_meta_2217_aux

open PEqualNP.Outside.L_meta_2217_aux in
theorem PEqualNP.Outside.L_meta_2217 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output < (25 : ℕ) + x1.size → x2 < (25 : ℕ) + x1.size → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x1.size + (2 : ℕ) ∧ ∀ (x7 : Bool) (x8 : Fin (25 : ℕ) → Bool), x6.eval (x7 :: List.ofFn x8) = (x1.eval (List.ofFn x8) || x7 && (x1.wires (List.ofFn x8)).getD x2 Bool.false) := by
  intro C j hm ho hj
  refine ⟨⟨C.gates.map sh ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, j + 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output + 1, 26 + C.size]⟩], 26 + C.size + 1⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil] at hg
    rcases hg with ⟨g0, h0, rfl⟩ | h | h
    · have := hm g0 h0
      simpa [sh] using this
    · subst h; simp
    · rcases h with h | h
      · subst h; simp
      · simp at h
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro b x
    have hl : (C.wires (List.ofFn x)).length = 25 + C.size := by
      rw [PEqualNP.CircuitLowerBounds.Circuit.wires, fold_len]; simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_append, fold_shift] at *
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at *
    set W := C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)
    simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
      PEqualNP.CircuitLowerBounds.GateOp.eval]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hl, List.getElem?_cons]
    have e1 : 26 + C.gates.length - (25 + C.gates.length) = 1 := by omega
    simp [e1, ho]
