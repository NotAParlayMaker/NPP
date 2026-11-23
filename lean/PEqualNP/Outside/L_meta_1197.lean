import PEqualNP.Defs
namespace PEqualNP.Outside
open CircuitLowerBounds
private def gate1197 (op : GateOp) (a b : Nat) : Gate := ⟨op,[a,b]⟩
theorem L_meta_1197 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨⟨[gate1197 .or 1 2,
    gate1197 .or 8 3,
    gate1197 .and 0 9,
    gate1197 .and 1 4,
    gate1197 .or 2 4,
    gate1197 .and 5 12,
    gate1197 .and 6 7,
    gate1197 .or 10 11,
    gate1197 .or 15 13,
    gate1197 .or 16 14],17⟩,?_,?_,?_⟩
  · simp [MetaComplexity.Monotone2,gate1197]
  all_goals decide +kernel
end PEqualNP.Outside
