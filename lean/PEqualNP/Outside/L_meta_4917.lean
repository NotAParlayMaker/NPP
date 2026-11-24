import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4917

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := ⟨[⟨GateOp.or, [26, 38]⟩, ⟨GateOp.or, [29, 41]⟩, ⟨GateOp.or, [32, 23]⟩,
  ⟨GateOp.or, [35, 26]⟩, ⟨GateOp.or, [38, 29]⟩, ⟨GateOp.or, [41, 32]⟩, ⟨GateOp.or, [23, 35]⟩,
  ⟨GateOp.or, [42, 41]⟩, ⟨GateOp.or, [43, 23]⟩, ⟨GateOp.or, [44, 26]⟩, ⟨GateOp.or, [45, 29]⟩,
  ⟨GateOp.or, [46, 32]⟩, ⟨GateOp.or, [47, 35]⟩, ⟨GateOp.or, [48, 38]⟩], 55⟩

theorem mono0 : PEqualNP.MetaComplexity.Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem wires0 (x2 : Fin 42 → Bool) :
    C0.wires (List.ofFn x2) =
      (List.ofFn x2 ++ List.ofFn fun (x4 : Fin 7) =>
          x2 (Fin.ofNat 42 (21 + (3 * ↑x4 + 5) % 21)) || x2 (Fin.ofNat 42 (21 + (3 * ↑x4 + 17) % 21))) ++
        List.ofFn fun (x4 : Fin 7) =>
          x2 (Fin.ofNat 42 (21 + (3 * ↑x4 + 5) % 21)) || x2 (Fin.ofNat 42 (21 + (3 * ↑x4 + 17) % 21)) ||
            x2 (Fin.ofNat 42 (21 + (3 * ↑x4 + 20) % 21)) := by
  simp [C0, PEqualNP.CircuitLowerBounds.Circuit.wires, GateOp.eval, List.ofFn_succ,
    List.getD_eq_getElem?_getD, Fin.ofNat]

end PEqualNP.Outside.L_meta_4917

theorem PEqualNP.Outside.L_meta_4917 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (14 : ℕ) ∧       ∀ (x2 : Fin (42 : ℕ) → Bool),         x1.wires (List.ofFn x2) =           have x3 : Fin (7 : ℕ) → ℕ → Bool := fun (x3 : Fin (7 : ℕ)) (x4 : ℕ) => x2 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x3 + x4) % (21 : ℕ)));           (List.ofFn x2 ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ)) ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ) || x3 x4 (20 : ℕ) := by
  refine ⟨PEqualNP.Outside.L_meta_4917.C0, PEqualNP.Outside.L_meta_4917.mono0, by decide, ?_⟩
  intro x2
  exact PEqualNP.Outside.L_meta_4917.wires0 x2
