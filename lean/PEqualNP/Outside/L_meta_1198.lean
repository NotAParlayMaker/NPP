import PEqualNP.Defs
namespace PEqualNP.Outside
open CircuitLowerBounds
private def G1198 (op : GateOp) (a b : Nat) : Gate := ⟨op,[a,b]⟩
theorem L_meta_1198 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 4 && x 7)) x := by
  refine ⟨⟨[G1198 .or 0 5, G1198 .and 2 8, G1198 .or 1 3, G1198 .and 0 10,
    G1198 .or 1 6, G1198 .or 12 7, G1198 .and 4 13, G1198 .or 9 11,
    G1198 .or 15 14],16⟩,?_,?_,?_⟩
  · simp [MetaComplexity.Monotone2,G1198]
  all_goals decide +kernel
end PEqualNP.Outside
