import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1996

theorem fuel_mono {n : ℕ} (C : PEqualNP.AndCount.AndCountCircuit n) (U V : Finset (Fin n))
    (h : U ⊆ V) : ∀ (d : ℕ) (i : Fin C.size),
      C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [PEqualNP.AndCount.AndCountCircuit.gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [PEqualNP.AndCount.AndCountCircuit.gateValFuel, Bool.and_eq_true,
      PEqualNP.AndCount.AndCountCircuit.sideTrue, decide_eq_true_eq] at hi ⊢
    obtain ⟨h1, h2⟩ := hi
    refine ⟨?_, ?_⟩
    · rcases h1 with ⟨v, hv, hvU⟩ | ⟨j, hj, hji, hval⟩
      · exact Or.inl ⟨v, hv, h hvU⟩
      · exact Or.inr ⟨j, hj, hji, ih j hval⟩
    · rcases h2 with ⟨v, hv, hvU⟩ | ⟨j, hj, hji, hval⟩
      · exact Or.inl ⟨v, hv, h hvU⟩
      · exact Or.inr ⟨j, hj, hji, ih j hval⟩

end PEqualNP.Outside.L_meta_1996

theorem PEqualNP.Outside.L_meta_1996 : ∀ (x1 : ℕ) (x2 : PEqualNP.AndCount.AndCountCircuit x1) (x3 x4 : Finset (Fin x1)), x3 ⊆ x4 → x2.eval x3 = Bool.true → x2.eval x4 = Bool.true := by
  intro n C U V h hU
  simp only [PEqualNP.AndCount.AndCountCircuit.eval, decide_eq_true_eq] at hU ⊢
  rcases hU with ⟨v, hv, hvU⟩ | ⟨j, hj, hval⟩
  · exact Or.inl ⟨v, hv, h hvU⟩
  · exact Or.inr ⟨j, hj, PEqualNP.Outside.L_meta_1996.fuel_mono C U V h C.size j hval⟩
