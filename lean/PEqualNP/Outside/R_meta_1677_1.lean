import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1677_1
  (h1 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 1 → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
  (h2 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[1]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
  (h3 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[1]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
  (h4 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[1]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) :
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hfan hwire hfun
  rcases le_or_gt C.size 1 with h1le | h2ge
  · exact h1 C hfan h1le hwire hfun
  · have hpos : 1 < C.gates.length := h2ge
    obtain ⟨g, hg⟩ : ∃ g, C.gates[1]? = Option.some g :=
      ⟨C.gates[1], getElem?_pos C.gates 1 hpos⟩
    have hmem := (hfan g (List.mem_of_getElem? hg)).1
    cases hop : g.op
    · exact h2 C hfan ⟨g, hg, hop⟩ hwire hfun
    · exact h3 C hfan ⟨g, hg, hop⟩ hwire hfun
    · exact h4 C hfan ⟨g, hg, hop⟩ hwire hfun
    · rw [hop] at hmem; simp at hmem
    · rw [hop] at hmem; simp at hmem
