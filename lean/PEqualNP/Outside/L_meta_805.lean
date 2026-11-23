import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_805 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 9 ∧ (∀ x : Fin 7 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 7, (u.val, v.val) ∈ ([(0, 1), (0, 4), (1, 2), (2, 3), (3, 4), (3, 5), (4, 6)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := rfl
    have hform : ∀ a0 a1 a2 a3 a4 a5 a6 : Bool,
        ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit).eval [a0, a1, a2, a3, a4, a5, a6] =
        ((a1 && (a0 || a2)) || ((a3 || ((a6 || a0) && a4)) && (a4 || (a5 || a2)))) := by
      intro a0 a1 a2 a3 a4 a5 a6
      simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
        PEqualNP.CircuitLowerBounds.GateOp.eval]
    have hbool : ∀ a0 a1 a2 a3 a4 a5 a6 : Bool,
        ((a1 && (a0 || a2)) || ((a3 || ((a6 || a0) && a4)) && (a4 || (a5 || a2)))) =
        ((a0 && a1) || (a0 && a4) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a3 && a5) || (a4 && a6)) := by
      decide
    rw [hx, hform, hbool]
    constructor
    · intro h
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ((((((⟨h0, h1⟩ | ⟨h0, h4⟩) | ⟨h1, h2⟩) | ⟨h2, h3⟩) | ⟨h3, h4⟩) | ⟨h3, h5⟩) | ⟨h4, h6⟩)
      · exact ⟨0, 1, by decide, h0, h1⟩
      · exact ⟨0, 4, by decide, h0, h4⟩
      · exact ⟨1, 2, by decide, h1, h2⟩
      · exact ⟨2, 3, by decide, h2, h3⟩
      · exact ⟨3, 4, by decide, h3, h4⟩
      · exact ⟨3, 5, by decide, h3, h5⟩
      · exact ⟨4, 6, by decide, h4, h6⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at huv
      rcases huv with ⟨hu0, hv1⟩ | ⟨hu0, hv4⟩ | ⟨hu1, hv2⟩ | ⟨hu2, hv3⟩ | ⟨hu3, hv4⟩ | ⟨hu3, hv5⟩ | ⟨hu4, hv6⟩
      · have hu' : u = 0 := Fin.ext hu0
        have hv' : v = 1 := Fin.ext hv1
        subst hu'; subst hv'; simp [hu, hv]
      · have hu' : u = 0 := Fin.ext hu0
        have hv' : v = 4 := Fin.ext hv4
        subst hu'; subst hv'; simp [hu, hv]
      · have hu' : u = 1 := Fin.ext hu1
        have hv' : v = 2 := Fin.ext hv2
        subst hu'; subst hv'; simp [hu, hv]
      · have hu' : u = 2 := Fin.ext hu2
        have hv' : v = 3 := Fin.ext hv3
        subst hu'; subst hv'; simp [hu, hv]
      · have hu' : u = 3 := Fin.ext hu3
        have hv' : v = 4 := Fin.ext hv4
        subst hu'; subst hv'; simp [hu, hv]
      · have hu' : u = 3 := Fin.ext hu3
        have hv' : v = 5 := Fin.ext hv5
        subst hu'; subst hv'; simp [hu, hv]
      · have hu' : u = 4 := Fin.ext hu4
        have hv' : v = 6 := Fin.ext hv6
        subst hu'; subst hv'; simp [hu, hv]
