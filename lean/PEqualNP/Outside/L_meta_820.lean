import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_820

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem fan : FanInTwo ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem evalB : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    Circuit.eval ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = ((b0 && b1) || (b0 && b5) || (b1 && b2) || (b1 && b7) || (b2 && b3) || (b3 && b4) || (b3 && b6) || (b4 && b5)) := by
  decide +kernel

theorem ofFnN (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

theorem edges (x : Fin 8 → Bool) :
    (((x 0 && x 1) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 7) || (x 2 && x 3) || (x 3 && x 4) || (x 3 && x 6) || (x 4 && x 5)) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 5), (1, 2), (1, 7), (2, 3), (3, 4), (3, 6), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
  constructor
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (((((((h | h) | h) | h) | h) | h) | h) | h)
    · exact ⟨0, 1, by decide, h.1, h.2⟩
    · exact ⟨0, 5, by decide, h.1, h.2⟩
    · exact ⟨1, 2, by decide, h.1, h.2⟩
    · exact ⟨1, 7, by decide, h.1, h.2⟩
    · exact ⟨2, 3, by decide, h.1, h.2⟩
    · exact ⟨3, 4, by decide, h.1, h.2⟩
    · exact ⟨3, 6, by decide, h.1, h.2⟩
    · exact ⟨4, 5, by decide, h.1, h.2⟩
  · rintro ⟨u, v, hm, hu, hv⟩
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl : u = 0 := Fin.ext h1
      obtain rfl : v = 1 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 0 := Fin.ext h1
      obtain rfl : v = 5 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 1 := Fin.ext h1
      obtain rfl : v = 2 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 1 := Fin.ext h1
      obtain rfl : v = 7 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 2 := Fin.ext h1
      obtain rfl : v = 3 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 3 := Fin.ext h1
      obtain rfl : v = 4 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 3 := Fin.ext h1
      obtain rfl : v = 6 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 4 := Fin.ext h1
      obtain rfl : v = 5 := Fin.ext h2
      simp [hu, hv]

end PEqualNP.Outside.L_meta_820

theorem PEqualNP.Outside.L_meta_820 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 5), (1, 2), (1, 7), (2, 3), (3, 4), (3, 6), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨PEqualNP.Outside.L_meta_820.fan, rfl, fun x => ?_⟩
  rw [PEqualNP.Outside.L_meta_820.ofFnN, PEqualNP.Outside.L_meta_820.evalB]
  exact PEqualNP.Outside.L_meta_820.edges x
