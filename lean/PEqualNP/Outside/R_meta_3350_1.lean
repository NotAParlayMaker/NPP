import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3350_1

def targetFun (x4 : Fin 9 → Bool) : Bool :=
  x4 0 && x4 1 || x4 1 && x4 2 || x4 2 && x4 3 || x4 3 && x4 4 || x4 4 && x4 0 ||
    x4 0 && x4 5 || x4 1 && x4 6 || x4 2 && x4 7 || x4 3 && x4 8 ||
    x4 5 && x4 7 || x4 6 && x4 8 || x4 8 && x4 5

theorem main
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      (∀ (x3 : Fin 9 → Bool), (x1.wires (List.ofFn x3)).getD 9 Bool.false = (x3 4 || x3 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 x1 = targetFun →
      ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate),
      x1.gates[1]? = some g1 →
      g1.op = PEqualNP.CircuitLowerBounds.GateOp.not →
      (4 ∈ g1.inputs ∨ 6 ∈ g1.inputs ∨ 9 ∈ g1.inputs) →
      16 ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      (∀ (x3 : Fin 9 → Bool), (x1.wires (List.ofFn x3)).getD 9 Bool.false = (x3 4 || x3 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 x1 = targetFun →
      ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate),
      x1.gates[1]? = some g1 →
      g1.op = PEqualNP.CircuitLowerBounds.GateOp.not →
      4 ∉ g1.inputs →
      6 ∉ g1.inputs →
      9 ∉ g1.inputs →
      16 ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size := by
  intro x1 hfan hwire hfun hgate1
  have hfun' : PEqualNP.MetaComplexity.circuitFun 9 x1 = targetFun := hfun
  rcases h1q : x1.gates[1]? with _ | g1
  · simp [h1q] at hgate1
  · have hg1op : g1.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      simp [h1q] at hgate1
      exact hgate1
    by_cases hmem : 4 ∈ g1.inputs ∨ 6 ∈ g1.inputs ∨ 9 ∈ g1.inputs
    · exact h1 x1 hfan hwire hfun' g1 h1q hg1op hmem
    · push Not at hmem
      exact h2 x1 hfan hwire hfun' g1 h1q hg1op hmem.1 hmem.2.1 hmem.2.2

end PEqualNP.Outside.R_meta_3350_1
