import PEqualNP.Defs
namespace PEqualNP.Outside
open CircuitLowerBounds
private def gate1184 (op : GateOp) (a b : Nat) : Gate := ⟨op,[a,b]⟩
theorem L_meta_1184 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x := by
  refine ⟨⟨[gate1184 .or 1 2,
    gate1184 .or 8 3,
    gate1184 .and 0 9,
    gate1184 .or 2 4,
    gate1184 .and 1 11,
    gate1184 .and 3 5,
    gate1184 .and 6 7,
    gate1184 .or 10 12,
    gate1184 .or 15 13,
    gate1184 .or 16 14],17⟩,?_,?_,?_⟩
  · simp [MetaComplexity.Monotone2,gate1184]
  all_goals decide +kernel
end PEqualNP.Outside
