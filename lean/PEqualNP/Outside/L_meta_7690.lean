import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7690_aux

open PEqualNP.CircuitLowerBounds

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl]; rw [ih]; simp; omega

theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.size := by
  unfold Circuit.wires Circuit.size; exact fold_len _ _

end PEqualNP.Outside.L_meta_7690_aux

open PEqualNP.Outside.L_meta_7690_aux in
theorem PEqualNP.Outside.L_meta_7690 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.GateOp), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 ∈ x1.gates, x6.inputs.Nodup) → x4 = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x4 = PEqualNP.CircuitLowerBounds.GateOp.and → x2 < (14 : ℕ) + x1.size → x3 < (14 : ℕ) + x1.size → x2 ≠ x3 → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x11.size = x1.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x11 ∧ (∀ x12 ∈ x11.gates, x12.inputs.Nodup) ∧ x11.output = (14 : ℕ) + x1.size ∧ x11.gates[x1.size]? = Option.some { op := x4, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x12 : Fin (14 : ℕ) → Bool), (∀ x13 < (14 : ℕ) + x1.size, PEqualNP.BlindGate.wireValue x11 (14 : ℕ) x12 x13 = PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x12 x13) ∧ PEqualNP.BlindGate.wireValue x11 (14 : ℕ) x12 x11.output = x4.eval [PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x12 x2, PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x12 x3] := by
  intro x1 x2 x3 x4 hA hN hop h2 h3 h23
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨x1.gates ++ [⟨x4, [x2, x3]⟩], 14 + x1.size⟩
  have hs : x1.size = x1.gates.length := rfl
  have hw : ∀ x : Fin 14 → Bool, C.wires (List.ofFn x) =
      x1.wires (List.ofFn x) ++ [x4.eval [(x1.wires (List.ofFn x)).getD x2 false, (x1.wires (List.ofFn x)).getD x3 false]] := by
    intro x
    show List.foldl _ _ (x1.gates ++ _) = _
    rw [List.foldl_append]
    rfl
  have hl : ∀ x : Fin 14 → Bool, (x1.wires (List.ofFn x)).length = 14 + x1.size := by
    intro x; rw [wires_len]; simp
  obtain ⟨hao, hrb, hlen⟩ := hA
  refine ⟨C, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [C, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro g hg
    simp only [C, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl
    · exact hao g hg
    · rcases hop with h | h <;> simp [h]
  · intro j hj i hi
    simp only [C, List.length_append, List.length_cons, List.length_nil] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    simp only [C] at hi
    by_cases hjl : j < x1.gates.length
    · rw [List.getD_append _ _ _ _ hjl] at hi
      have := hrb j hjl i hi
      omega
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      have : j - x1.gates.length = 0 := by omega
      rw [this] at hi
      simp at hi
      omega
  · intro g hg
    simp only [C, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl
    · exact hlen g hg
    · simp
  · intro g hg
    simp only [C, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl
    · exact hN g hg
    · simp [h23]
  · rfl
  · simp [C, hs]
  · intro x
    refine ⟨?_, ?_⟩
    · intro i hi
      unfold PEqualNP.BlindGate.wireValue
      rw [hw x]
      exact List.getD_append _ _ _ _ (by rw [hl x]; exact hi)
    · unfold PEqualNP.BlindGate.wireValue
      rw [hw x]
      show List.getD _ (14 + x1.size) false = _
      rw [← hl x]
      simp
