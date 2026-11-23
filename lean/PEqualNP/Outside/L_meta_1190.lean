import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1190_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def A (a b : ℕ) : Gate := ⟨GateOp.and, [a, b]⟩

def O (a b : ℕ) : Gate := ⟨GateOp.or, [a, b]⟩

theorem mono_of (gs : List Gate) (o : ℕ)
    (h1 : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    Monotone2 ⟨gs, o⟩ := by
  intro g hg
  obtain ⟨hop, hlen⟩ := h1 g hg
  refine ⟨?_, by omega⟩
  rcases hop with h | h <;> simp [h]

end PEqualNP.Outside.L_meta_1190_aux

theorem PEqualNP.Outside.L_meta_1190 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  refine ⟨⟨[PEqualNP.Outside.L_meta_1190_aux.O 1 2, PEqualNP.Outside.L_meta_1190_aux.O 8 3, PEqualNP.Outside.L_meta_1190_aux.A 0 9, PEqualNP.Outside.L_meta_1190_aux.A 1 2, PEqualNP.Outside.L_meta_1190_aux.O 5 6, PEqualNP.Outside.L_meta_1190_aux.A 4 12, PEqualNP.Outside.L_meta_1190_aux.A 5 7, PEqualNP.Outside.L_meta_1190_aux.O 10 11, PEqualNP.Outside.L_meta_1190_aux.O 15 13, PEqualNP.Outside.L_meta_1190_aux.O 16 14], 17⟩, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_1190_aux.mono_of _ _ (by simp [PEqualNP.Outside.L_meta_1190_aux.A, PEqualNP.Outside.L_meta_1190_aux.O])
  · decide
  · decide +kernel
