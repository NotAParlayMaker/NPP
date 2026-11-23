import PEqualNP.Defs
namespace PEqualNP.Outside
open CircuitLowerBounds
private def gate1176 (op : GateOp) (a b : Nat) : Gate := ⟨op,[a,b]⟩
theorem L_meta_1176 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x := by
  refine ⟨⟨[gate1176 .or 1 2,
    gate1176 .or 8 3,
    gate1176 .or 9 4,
    gate1176 .and 0 10,
    gate1176 .or 5 6,
    gate1176 .and 1 12,
    gate1176 .and 2 7,
    gate1176 .or 11 13,
    gate1176 .or 15 14],16⟩,?_,?_,?_⟩
  · simp [MetaComplexity.Monotone2,gate1176]
  all_goals decide +kernel
end PEqualNP.Outside
