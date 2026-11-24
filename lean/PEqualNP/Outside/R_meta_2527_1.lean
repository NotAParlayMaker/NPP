import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_2527_1

def targetFun (x : Fin 9 → Bool) : Bool :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)].any
    fun e => x e.1 && x e.2

theorem main
    (h1 : ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x2 →
      (∀ (x4 : Fin 9 → Bool), (x2.wires (List.ofFn x4)).getD 9 Bool.false = (x4 0 || x4 4)) →
      PEqualNP.MetaComplexity.circuitFun 9 x2 = targetFun →
      ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate),
      x2.gates[1]? = some g1 →
      g1.op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (0 ∈ g1.inputs ∨ 4 ∈ g1.inputs ∨ 9 ∈ g1.inputs) →
      (∃ x7 ∈ List.drop 1 x2.gates, 0 ∈ x7.inputs) →
      (∃ x8 ∈ List.drop 1 x2.gates, 4 ∈ x8.inputs) →
      16 ≤ x2.size)
    (h2 : ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x2 →
      (∀ (x4 : Fin 9 → Bool), (x2.wires (List.ofFn x4)).getD 9 Bool.false = (x4 0 || x4 4)) →
      PEqualNP.MetaComplexity.circuitFun 9 x2 = targetFun →
      ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate),
      x2.gates[1]? = some g1 →
      g1.op = PEqualNP.CircuitLowerBounds.GateOp.or →
      0 ∉ g1.inputs →
      4 ∉ g1.inputs →
      9 ∉ g1.inputs →
      (∃ x7 ∈ List.drop 1 x2.gates, 0 ∈ x7.inputs) →
      (∃ x8 ∈ List.drop 1 x2.gates, 4 ∈ x8.inputs) →
      16 ≤ x2.size) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x2.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (∃ x7 ∈ List.drop (1 : ℕ) x2.gates, (0 : ℕ) ∈ x7.inputs) → (∃ x8 ∈ List.drop (1 : ℕ) x2.gates, (4 : ℕ) ∈ x8.inputs) → (16 : ℕ) ≤ x2.size := by
  intro x1 x2 hfan hwire hfun hgate1 hx7 hx8
  have hfun' : PEqualNP.MetaComplexity.circuitFun 9 x2 = targetFun := hfun
  rcases h1q : x2.gates[1]? with _ | g1
  · simp [h1q] at hgate1
  · have hg1op : g1.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      simp [h1q] at hgate1
      exact hgate1
    by_cases hmem : 0 ∈ g1.inputs ∨ 4 ∈ g1.inputs ∨ 9 ∈ g1.inputs
    · exact h1 x2 hfan hwire hfun' g1 h1q hg1op hmem hx7 hx8
    · push Not at hmem
      exact h2 x2 hfan hwire hfun' g1 h1q hg1op hmem.1 hmem.2.1 hmem.2.2 hx7 hx8

end PEqualNP.Outside.R_meta_2527_1
