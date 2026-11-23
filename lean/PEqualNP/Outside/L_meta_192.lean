import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_192 : ∀ C C2 : PEqualNP.CircuitLowerBounds.Circuit, C = { gates := [⟨.and, [0, 4]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [5]⟩, ⟨.not, [6]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [9, 10]⟩], output := 11 } → C2 = { gates := [⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [7, 8]⟩, ⟨.not, [4]⟩, ⟨.or, [9, 10]⟩], output := 11 } → PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.FanInTwo C2 ∧ C.size = 7 ∧ C2.size = 7 ∧ PEqualNP.MetaComplexity.circuitFun 5 C = (fun x : Fin 5 → Bool => !x 4 || ((!x 0 || x 2) && (!x 1 || x 3))) ∧ PEqualNP.MetaComplexity.circuitFun 5 C2 = PEqualNP.MetaComplexity.circuitFun 5 C ∧ C.gates.zipIdx.countP (fun p => decide (4 < 5 + p.2) && (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains 4) = 2 := by
  intro C C2 hC hC2
  subst hC
  subst hC2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rfl
  · rfl
  · have hall : ∀ x : Fin 5 → Bool, PEqualNP.MetaComplexity.circuitFun 5 { gates := [⟨.and, [0, 4]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [5]⟩, ⟨.not, [6]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [9, 10]⟩], output := 11 } x = (!x 4 || ((!x 0 || x 2) && (!x 1 || x 3))) := by
      decide
    exact funext hall
  · have hall2 : ∀ x : Fin 5 → Bool, PEqualNP.MetaComplexity.circuitFun 5 { gates := [⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [7, 8]⟩, ⟨.not, [4]⟩, ⟨.or, [9, 10]⟩], output := 11 } x = PEqualNP.MetaComplexity.circuitFun 5 { gates := [⟨.and, [0, 4]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [5]⟩, ⟨.not, [6]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [9, 10]⟩], output := 11 } x := by
      decide
    exact funext hall2
  · decide
