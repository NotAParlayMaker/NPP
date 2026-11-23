import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_936_Proof

theorem edgeCons (x : Fin 8 → Bool) (a b : ℕ) (ha : a < 8) (hb : b < 8) (es : List (ℕ × ℕ)) :
    (∃ u v : Fin 8, (u.val, v.val) ∈ (a, b) :: es ∧ x u = true ∧ x v = true) ↔
    (x ⟨a, ha⟩ = true ∧ x ⟨b, hb⟩ = true) ∨
      ∃ u v : Fin 8, (u.val, v.val) ∈ es ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Or.inl ⟨(show u = ⟨a, ha⟩ from Fin.ext h1) ▸ hu, (show v = ⟨b, hb⟩ from Fin.ext h2) ▸ hv⟩
    · exact Or.inr ⟨u, v, h, hu, hv⟩
  · rintro (⟨h1, h2⟩ | ⟨u, v, h, hu, hv⟩)
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩, List.mem_cons_self, h1, h2⟩
    · exact ⟨u, v, List.mem_cons_of_mem _ h, hu, hv⟩

set_option maxRecDepth 100000 in
theorem aux1 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b5) || ((b1 && b5) || ((b2 && b6) || ((b3 && b7) || ((b4 && b6) || ((b4 && b7) || ((b5 && b7) || (b6 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux2 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b5) || ((b1 && b5) || ((b2 && b7) || ((b3 && b7) || ((b4 && b6) || ((b4 && b7) || ((b5 && b6) || (b6 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux3 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b5) || ((b1 && b6) || ((b2 && b6) || ((b3 && b7) || ((b4 && b7) || ((b5 && b6) || ((b5 && b7) || (b6 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux4 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b5) || ((b1 && b6) || ((b2 && b7) || ((b3 && b5) || ((b3 && b6) || ((b4 && b5) || ((b4 && b7) || (b6 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux5 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b5) || ((b1 && b6) || ((b2 && b7) || ((b3 && b7) || ((b4 && b7) || ((b5 && b6) || ((b5 && b7) || (b6 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux6 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b5) || ((b1 && b7) || ((b2 && b7) || ((b3 && b7) || ((b4 && b5) || ((b4 && b6) || ((b5 && b6) || (b6 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux7 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b6) || ((b1 && b6) || ((b2 && b6) || ((b3 && b7) || ((b4 && b5) || ((b4 && b7) || ((b5 && b7) || (b6 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux8 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b6) || ((b1 && b6) || ((b2 && b7) || ((b3 && b4) || ((b3 && b7) || ((b4 && b7) || ((b5 && b6) || (b5 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux9 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b6) || ((b1 && b6) || ((b2 && b7) || ((b3 && b7) || ((b4 && b5) || ((b4 && b7) || ((b5 && b7) || (b6 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux10 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b6) || ((b1 && b7) || ((b2 && b7) || ((b3 && b4) || ((b3 && b5) || ((b4 && b6) || ((b5 && b7) || (b6 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux11 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b6) || ((b1 && b7) || ((b2 && b7) || ((b3 && b4) || ((b3 && b6) || ((b4 && b7) || ((b5 && b6) || (b5 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux12 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b7) || ((b1 && b7) || ((b2 && b3) || ((b2 && b4) || ((b3 && b5) || ((b4 && b6) || ((b5 && b7) || (b6 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux13 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b7) || ((b1 && b7) || ((b2 && b7) || ((b3 && b4) || ((b3 && b5) || ((b4 && b6) || ((b5 && b7) || (b6 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux14 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b7) || ((b1 && b7) || ((b2 && b7) || ((b3 && b4) || ((b3 && b6) || ((b4 && b6) || ((b5 && b6) || (b5 && b7)))))))) = true) := by decide

set_option maxRecDepth 100000 in
theorem aux15 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b7) || ((b1 && b7) || ((b2 && b7) || ((b3 && b7) || ((b4 && b5) || ((b4 && b6) || ((b5 && b6) || (b6 && b7)))))))) = true) := by decide

end PEqualNP.Outside.L_meta_936_Proof

theorem PEqualNP.Outside.L_meta_936 : (∀ C1 : PEqualNP.CircuitLowerBounds.Circuit, C1 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C1 ∧ C1.size = 10 ∧ (∀ x1 : Fin 8 → Bool, (C1.eval (List.ofFn x1) = true ↔ ∃ u1 v1 : Fin 8, (u1.val, v1.val) ∈ ([(0, 5), (1, 5), (2, 6), (3, 7), (4, 6), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x1 u1 = true ∧ x1 v1 = true))) ∧ (∀ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C2 ∧ C2.size = 10 ∧ (∀ x2 : Fin 8 → Bool, (C2.eval (List.ofFn x2) = true ↔ ∃ u2 v2 : Fin 8, (u2.val, v2.val) ∈ ([(0, 5), (1, 5), (2, 7), (3, 7), (4, 6), (4, 7), (5, 6), (6, 7)] : List (ℕ × ℕ)) ∧ x2 u2 = true ∧ x2 v2 = true))) ∧ (∀ C3 : PEqualNP.CircuitLowerBounds.Circuit, C3 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C3 ∧ C3.size = 10 ∧ (∀ x3 : Fin 8 → Bool, (C3.eval (List.ofFn x3) = true ↔ ∃ u3 v3 : Fin 8, (u3.val, v3.val) ∈ ([(0, 5), (1, 6), (2, 6), (3, 7), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x3 u3 = true ∧ x3 v3 = true))) ∧ (∀ C4 : PEqualNP.CircuitLowerBounds.Circuit, C4 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C4 ∧ C4.size = 10 ∧ (∀ x4 : Fin 8 → Bool, (C4.eval (List.ofFn x4) = true ↔ ∃ u4 v4 : Fin 8, (u4.val, v4.val) ∈ ([(0, 5), (1, 6), (2, 7), (3, 5), (3, 6), (4, 5), (4, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x4 u4 = true ∧ x4 v4 = true))) ∧ (∀ C5 : PEqualNP.CircuitLowerBounds.Circuit, C5 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C5 ∧ C5.size = 10 ∧ (∀ x5 : Fin 8 → Bool, (C5.eval (List.ofFn x5) = true ↔ ∃ u5 v5 : Fin 8, (u5.val, v5.val) ∈ ([(0, 5), (1, 6), (2, 7), (3, 7), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x5 u5 = true ∧ x5 v5 = true))) ∧ (∀ C6 : PEqualNP.CircuitLowerBounds.Circuit, C6 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C6 ∧ C6.size = 10 ∧ (∀ x6 : Fin 8 → Bool, (C6.eval (List.ofFn x6) = true ↔ ∃ u6 v6 : Fin 8, (u6.val, v6.val) ∈ ([(0, 5), (1, 7), (2, 7), (3, 7), (4, 5), (4, 6), (5, 6), (6, 7)] : List (ℕ × ℕ)) ∧ x6 u6 = true ∧ x6 v6 = true))) ∧ (∀ C7 : PEqualNP.CircuitLowerBounds.Circuit, C7 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C7 ∧ C7.size = 10 ∧ (∀ x7 : Fin 8 → Bool, (C7.eval (List.ofFn x7) = true ↔ ∃ u7 v7 : Fin 8, (u7.val, v7.val) ∈ ([(0, 6), (1, 6), (2, 6), (3, 7), (4, 5), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x7 u7 = true ∧ x7 v7 = true))) ∧ (∀ C8 : PEqualNP.CircuitLowerBounds.Circuit, C8 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C8 ∧ C8.size = 10 ∧ (∀ x8 : Fin 8 → Bool, (C8.eval (List.ofFn x8) = true ↔ ∃ u8 v8 : Fin 8, (u8.val, v8.val) ∈ ([(0, 6), (1, 6), (2, 7), (3, 4), (3, 7), (4, 7), (5, 6), (5, 7)] : List (ℕ × ℕ)) ∧ x8 u8 = true ∧ x8 v8 = true))) ∧ (∀ C9 : PEqualNP.CircuitLowerBounds.Circuit, C9 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C9 ∧ C9.size = 10 ∧ (∀ x9 : Fin 8 → Bool, (C9.eval (List.ofFn x9) = true ↔ ∃ u9 v9 : Fin 8, (u9.val, v9.val) ∈ ([(0, 6), (1, 6), (2, 7), (3, 7), (4, 5), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x9 u9 = true ∧ x9 v9 = true))) ∧ (∀ C10 : PEqualNP.CircuitLowerBounds.Circuit, C10 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C10 ∧ C10.size = 10 ∧ (∀ x10 : Fin 8 → Bool, (C10.eval (List.ofFn x10) = true ↔ ∃ u10 v10 : Fin 8, (u10.val, v10.val) ∈ ([(0, 6), (1, 7), (2, 7), (3, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x10 u10 = true ∧ x10 v10 = true))) ∧ (∀ C11 : PEqualNP.CircuitLowerBounds.Circuit, C11 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C11 ∧ C11.size = 10 ∧ (∀ x11 : Fin 8 → Bool, (C11.eval (List.ofFn x11) = true ↔ ∃ u11 v11 : Fin 8, (u11.val, v11.val) ∈ ([(0, 6), (1, 7), (2, 7), (3, 4), (3, 6), (4, 7), (5, 6), (5, 7)] : List (ℕ × ℕ)) ∧ x11 u11 = true ∧ x11 v11 = true))) ∧ (∀ C12 : PEqualNP.CircuitLowerBounds.Circuit, C12 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C12 ∧ C12.size = 10 ∧ (∀ x12 : Fin 8 → Bool, (C12.eval (List.ofFn x12) = true ↔ ∃ u12 v12 : Fin 8, (u12.val, v12.val) ∈ ([(0, 7), (1, 7), (2, 3), (2, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x12 u12 = true ∧ x12 v12 = true))) ∧ (∀ C13 : PEqualNP.CircuitLowerBounds.Circuit, C13 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C13 ∧ C13.size = 10 ∧ (∀ x13 : Fin 8 → Bool, (C13.eval (List.ofFn x13) = true ↔ ∃ u13 v13 : Fin 8, (u13.val, v13.val) ∈ ([(0, 7), (1, 7), (2, 7), (3, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x13 u13 = true ∧ x13 v13 = true))) ∧ (∀ C14 : PEqualNP.CircuitLowerBounds.Circuit, C14 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C14 ∧ C14.size = 10 ∧ (∀ x14 : Fin 8 → Bool, (C14.eval (List.ofFn x14) = true ↔ ∃ u14 v14 : Fin 8, (u14.val, v14.val) ∈ ([(0, 7), (1, 7), (2, 7), (3, 4), (3, 6), (4, 6), (5, 6), (5, 7)] : List (ℕ × ℕ)) ∧ x14 u14 = true ∧ x14 v14 = true))) ∧ (∀ C15 : PEqualNP.CircuitLowerBounds.Circuit, C15 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C15 ∧ C15.size = 10 ∧ (∀ x15 : Fin 8 → Bool, (C15.eval (List.ofFn x15) = true ↔ ∃ u15 v15 : Fin 8, (u15.val, v15.val) ∈ ([(0, 7), (1, 7), (2, 7), (3, 7), (4, 5), (4, 6), (5, 6), (6, 7)] : List (ℕ × ℕ)) ∧ x15 u15 = true ∧ x15 v15 = true))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux2 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux3 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux4 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux5 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux6 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux7 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux8 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 4 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux9 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux10 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 4 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux11 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 4 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux12 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 3 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 4 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux13 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 4 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux14 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 4 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_936_Proof.aux15 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 0 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 1 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 2 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 3 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 5 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 4 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 5 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_936_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
