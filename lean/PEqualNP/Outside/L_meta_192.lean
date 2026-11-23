import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem L_meta_192_ofFn (x : Fin 5 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
  simp [List.ofFn_succ]

private theorem L_meta_192_C (a b c d e : Bool) :
    Circuit.eval
      { gates := [⟨.and, [0, 4]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [5]⟩, ⟨.not, [6]⟩, ⟨.or, [7, 2]⟩,
        ⟨.or, [8, 3]⟩, ⟨.and, [9, 10]⟩], output := 11 } [a, b, c, d, e] =
      (!e || ((!a || c) && (!b || d))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

private theorem L_meta_192_C2 (a b c d e : Bool) :
    Circuit.eval
      { gates := [⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [7, 8]⟩,
        ⟨.not, [4]⟩, ⟨.or, [9, 10]⟩], output := 11 } [a, b, c, d, e] =
      (!e || ((!a || c) && (!b || d))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

theorem L_meta_192 : ∀ C C2 : PEqualNP.CircuitLowerBounds.Circuit, C = { gates := [⟨.and, [0, 4]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [5]⟩, ⟨.not, [6]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [9, 10]⟩], output := 11 } → C2 = { gates := [⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [7, 8]⟩, ⟨.not, [4]⟩, ⟨.or, [9, 10]⟩], output := 11 } → PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.FanInTwo C2 ∧ C.size = 7 ∧ C2.size = 7 ∧ PEqualNP.MetaComplexity.circuitFun 5 C = (fun x : Fin 5 → Bool => !x 4 || ((!x 0 || x 2) && (!x 1 || x 3))) ∧ PEqualNP.MetaComplexity.circuitFun 5 C2 = PEqualNP.MetaComplexity.circuitFun 5 C ∧ C.gates.zipIdx.countP (fun p => decide (4 < 5 + p.2) && (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains 4) = 2 := by
  intro C C2 hC hC2
  subst hC hC2
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, rfl⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · funext x
    simp only [circuitFun, L_meta_192_ofFn, L_meta_192_C]
  · funext x
    simp only [circuitFun, L_meta_192_ofFn, L_meta_192_C, L_meta_192_C2]

end PEqualNP.Outside
