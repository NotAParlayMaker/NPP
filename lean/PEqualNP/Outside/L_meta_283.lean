import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_283

def circ : PEqualNP.CircuitLowerBounds.Circuit :=
  ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit)

set_option maxRecDepth 100000 in
theorem key : ∀ a0 a1 a2 a3 a4 a5 : Bool,
    (circ.eval [a0, a1, a2, a3, a4, a5] = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)] : List (ℕ × ℕ)) ∧
      (![a0, a1, a2, a3, a4, a5] : Fin 6 → Bool) u = true ∧
      (![a0, a1, a2, a3, a4, a5] : Fin 6 → Bool) v = true) := by
  decide +kernel

theorem evalOk (x : Fin 6 → Bool) :
    (circ.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true) := by
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  have hv : (![x 0, x 1, x 2, x 3, x 4, x 5] : Fin 6 → Bool) = x := by
    funext i
    fin_cases i <;> rfl
  have h := key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  rw [hv] at h
  rw [hx]
  exact h

theorem mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ands : ∃ A : Finset ℕ, A.card ≤ 2 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
    circ.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A := by
  refine ⟨{3, 8}, by decide, ?_⟩
  intro j g h hop
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;> simp [circ] at h <;> subst h <;>
    simp at hop ⊢

end PEqualNP.Outside.L_meta_283

theorem PEqualNP.Outside.L_meta_283 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 2 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  exact ⟨⟨PEqualNP.Outside.L_meta_283.mono, PEqualNP.Outside.L_meta_283.ands⟩,
    PEqualNP.Outside.L_meta_283.evalOk⟩
