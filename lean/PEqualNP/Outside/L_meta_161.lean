import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

/-- Each AND tests whether both sides of a partition contain a true input.
The two partitions distinguish every pair of inputs. -/
private def thresholdCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [7, 8]⟩,
    ⟨.or, [6, 9]⟩], 10⟩

theorem PEqualNP.Outside.L_meta_161 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (∃ i j : Fin C.gates.length, i ≠ j ∧ ∀ k : Fin C.gates.length, (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ (k = i ∨ k = j)) ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)) := by
  refine ⟨thresholdCircuit, ?_, by decide, ?_, ?_, ?_⟩
  · intro g hg
    simp only [thresholdCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp
  · intro g hg
    simp only [thresholdCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp
  · refine ⟨⟨2, by decide⟩, ⟨5, by decide⟩, by decide, ?_⟩
    change ∀ k : Fin 7, _
    intro k
    fin_cases k <;> simp [thresholdCircuit] <;> decide
  · intro x
    change thresholdCircuit.eval [x 0, x 1, x 2, x 3] = _
    generalize x 0 = a
    generalize x 1 = b
    generalize x 2 = c
    generalize x 3 = d
    cases a <;> cases b <;> cases c <;> cases d <;> rfl
