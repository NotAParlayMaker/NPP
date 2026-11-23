import PEqualNP.Defs
namespace PEqualNP.Outside
open CircuitLowerBounds
private def G1188 (op : GateOp) (a b : Nat) : Gate := ⟨op,[a,b]⟩
theorem L_meta_1188 : ∃ C : Circuit, MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool =>
    (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) ||
    (x 5 && x 6) || (x 5 && x 7)) x := by
  refine ⟨⟨[G1188 .or 1 2, G1188 .and 0 8, G1188 .and 1 2, G1188 .or 9 10,
    G1188 .or 0 4, G1188 .and 3 12, G1188 .or 6 7, G1188 .and 5 14,
    G1188 .or 11 13, G1188 .or 16 15],17⟩,?_,?_,?_⟩
  · simp [MetaComplexity.Monotone2,G1188]
  all_goals decide +kernel
end PEqualNP.Outside
