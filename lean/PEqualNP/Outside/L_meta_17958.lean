import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17958_aux

open PEqualNP.CircuitLowerBounds

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires; exact fold_len _ _

theorem append_and : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (∀ x6 ∈ x2.gates, x6.inputs.Nodup) →       x3 ≠ x4 →         x3 < x1 + x2.size →           x4 < x1 + x2.size →             have x10 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate }], output := x1 + x2.size : PEqualNP.CircuitLowerBounds.Circuit };             PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : Fin x1 → Bool), ∀ x12 < x1 + x2.size, PEqualNP.BlindGate.wireValue x10 x1 x11 x12 = PEqualNP.BlindGate.wireValue x2 x1 x11 x12 := by
  intro n C a b hC hN hab ha hb
  obtain ⟨hA, hR, hL⟩ := hC
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hA g hg
    · exact Or.inl rfl
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · have := hR j hj i
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at this
      rw [List.getD_append _ _ _ _ hj] at hi
      exact this hi
    · subst hj
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp at hi
      unfold PEqualNP.CircuitLowerBounds.Circuit.size at ha hb
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hL g hg
    · rfl
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hN g hg
    · simp [hab]
  · intro x w hw
    unfold PEqualNP.BlindGate.wireValue PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hl := fold_len C.gates (List.ofFn x)
    unfold PEqualNP.CircuitLowerBounds.Circuit.size at hw
    simp only [List.length_ofFn] at hl
    rw [List.getD_append _ _ _ _ (by omega)]

end PEqualNP.Outside.L_meta_17958_aux

open PEqualNP.Outside.L_meta_17958_aux in
theorem PEqualNP.Outside.L_meta_17958 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) → x2 ≠ x3 → x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), x9.size ≤ x1.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x9 ∧ (∀ x11 ∈ x9.gates, x11.inputs.Nodup) ∧ x9.output = (26 : ℕ) + x10 ∧ x9.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), ∀ x12 < (26 : ℕ) + x1.size, PEqualNP.BlindGate.wireValue x9 (26 : ℕ) x11 x12 = PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 x12 := by
  intro C a b hC hN hab ha hb
  obtain ⟨h1, h2, h3⟩ := append_and 26 C a b hC hN hab ha hb
  refine ⟨_, C.size, ?_, h1, h2, rfl, ?_, h3⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
