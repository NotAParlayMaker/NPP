import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_272

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  { gates := [⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [6, 9]⟩],
    output := 10 }

theorem mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ands : ∀ (j : ℕ) (g : Gate), circ.gates[j]? = some g →
    (g.op = GateOp.and ↔ j ∈ ({0, 1, 3, 4, 6} : Finset ℕ)) := by
  intro j g hg
  rcases j with _ | _ | _ | _ | _ | _ | _ | j <;>
    simp [circ] at hg <;> subst hg <;> simp

theorem computes : ∀ x : Fin 4 → Bool,
    (circ.eval (List.ofFn x) = true ↔ 3 ≤ (List.ofFn x).count true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_272

theorem PEqualNP.Outside.L_meta_272 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 7 ∧ (∃ A : Finset ℕ, A.card = 5 ∧ (∀ j ∈ A, j < C.size) ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ j ∈ A)) ∧ (∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ 3 ≤ (List.ofFn x).count true)) := by
  rintro C rfl
  exact ⟨PEqualNP.Outside.L_meta_272.mono, rfl,
    ⟨{0, 1, 3, 4, 6}, rfl, by decide, PEqualNP.Outside.L_meta_272.ands⟩,
    PEqualNP.Outside.L_meta_272.computes⟩
