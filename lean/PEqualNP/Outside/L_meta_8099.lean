import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8099_aux

open PEqualNP.AndCount

theorem key {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true →
      ∃ k : Fin C.size, (∃ v ∈ C.leftVars k, v ∈ U) ∧ (∃ v ∈ C.rightVars k, v ∈ U) := by
  intro d
  induction d with
  | zero => intro i h; simp [AndCountCircuit.gateValFuel] at h
  | succ d ih =>
    intro i h
    simp only [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨hl, hr⟩ := h
    rcases hl with hl | ⟨j, _, _, hj⟩
    · rcases hr with hr | ⟨j, _, _, hj⟩
      · exact ⟨i, hl, hr⟩
      · exact ih j hj
    · exact ih j hj

end PEqualNP.Outside.L_meta_8099_aux

theorem PEqualNP.Outside.L_meta_8099 : ∀ (x1 : ℕ) (x2 : PEqualNP.AndCount.AndCountCircuit x1) (x3 : SimpleGraph (Fin x1)), x2.Computes x3 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) → ∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → ∃ (x10 : Fin x2.size), x7 ∈ x2.leftVars x10 ∧ x8 ∈ x2.rightVars x10 ∨ x8 ∈ x2.leftVars x10 ∧ x7 ∈ x2.rightVars x10 := by
  intro n C G hC hout hdis x y hxy
  have hne : x ≠ y := G.ne_of_adj hxy
  have he : C.eval {x, y} = true := (hC {x, y}).2 ⟨x, by simp, y, by simp, hxy⟩
  simp only [PEqualNP.AndCount.AndCountCircuit.eval, hout, decide_eq_true_eq] at he
  rcases he with ⟨v, hv, _⟩ | ⟨j, _, hj⟩
  · simp at hv
  obtain ⟨k, ⟨a, ha, haU⟩, ⟨b, hb, hbU⟩⟩ :=
    PEqualNP.Outside.L_meta_8099_aux.key C {x, y} C.size j hj
  refine ⟨k, ?_⟩
  have hd := Finset.disjoint_left.mp (hdis k)
  simp only [Finset.mem_insert, Finset.mem_singleton] at haU hbU
  rcases haU with rfl | rfl <;> rcases hbU with rfl | rfl
  · exact absurd hb (hd ha)
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact absurd hb (hd ha)
