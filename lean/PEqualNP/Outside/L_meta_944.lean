import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_944_Proof

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
    (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 16]⟩], output := 20 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ((b0 && b1) || ((b0 && b2) || ((b1 && b2) || ((b3 && b4) || ((b3 && b7) || ((b4 && b7) || ((b5 && b6) || ((b5 && b7) || (b6 && b7))))))))) = true) := by decide

end PEqualNP.Outside.L_meta_944_Proof

theorem PEqualNP.Outside.L_meta_944 : (∀ C1 : PEqualNP.CircuitLowerBounds.Circuit, C1 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 16]⟩], output := 20 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C1 ∧ C1.size = 13 ∧ (∀ x1 : Fin 8 → Bool, (C1.eval (List.ofFn x1) = true ↔ ∃ u1 v1 : Fin 8, (u1.val, v1.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 7), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x1 u1 = true ∧ x1 v1 = true))) := by
  refine ?_
  · rintro C rfl
    refine ⟨?_, rfl, ?_⟩
    · intro gate hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
      rw [hx, PEqualNP.Outside.L_meta_944_Proof.aux1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)]
      rw [PEqualNP.Outside.L_meta_944_Proof.edgeCons x 0 1 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_944_Proof.edgeCons x 0 2 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_944_Proof.edgeCons x 1 2 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_944_Proof.edgeCons x 3 4 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_944_Proof.edgeCons x 3 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_944_Proof.edgeCons x 4 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_944_Proof.edgeCons x 5 6 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_944_Proof.edgeCons x 5 7 (by decide) (by decide)]
      rw [PEqualNP.Outside.L_meta_944_Proof.edgeCons x 6 7 (by decide) (by decide)]
      have e0 : (⟨0, by decide⟩ : Fin 8) = 0 := rfl
      have e1 : (⟨1, by decide⟩ : Fin 8) = 1 := rfl
      have e2 : (⟨2, by decide⟩ : Fin 8) = 2 := rfl
      have e3 : (⟨3, by decide⟩ : Fin 8) = 3 := rfl
      have e4 : (⟨4, by decide⟩ : Fin 8) = 4 := rfl
      have e5 : (⟨5, by decide⟩ : Fin 8) = 5 := rfl
      have e6 : (⟨6, by decide⟩ : Fin 8) = 6 := rfl
      have e7 : (⟨7, by decide⟩ : Fin 8) = 7 := rfl
      simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_true, Bool.and_eq_true, e0, e1, e2, e3, e4, e5, e6, e7]
