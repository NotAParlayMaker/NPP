import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2539_741
    (hCover : ∀ x : Fin 9 → Bool, ∃ m : BitVec 9,
      x = fun i : Fin 9 => m.getLsbD (i.val % 9))
    (hCut : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (m : BitVec 9), let x4 := fun i : Fin 9 => m.getLsbD (i.val % 9); (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = !x4 (0 : Fin (9 : ℕ))) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x6 : ℕ) => x5.inputs.contains x6) x2).length ≤ (1 : ℕ) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Bool), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size < x1.size ∧ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (0 : ℕ)) x6.gates).length ≤ (1 : ℕ) ∧ ∀ (m : BitVec 9), let x8 := fun i : Fin 9 => m.getLsbD (i.val % 9); PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x6 fun (x9 : Fin (9 : ℕ)) => if x9 = (0 : Fin (9 : ℕ)) then x7 != x8 (0 : Fin (9 : ℕ)) else x8 x9) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = !x4 (0 : Fin (9 : ℕ))) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x6 : ℕ) => x5.inputs.contains x6) x2).length ≤ (1 : ℕ) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Bool), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size < x1.size ∧ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (0 : ℕ)) x6.gates).length ≤ (1 : ℕ) ∧ ∀ (x8 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x6 fun (x9 : Fin (9 : ℕ)) => if x9 = (0 : Fin (9 : ℕ)) then x7 != x8 (0 : Fin (9 : ℕ)) else x8 x9 := by
  intro C tail hFan hFirst hReads
  obtain ⟨D, b, hD, hSize, hSmall, hValues⟩ :=
    hCut C hFan (fun m => hFirst (fun i => m.getLsbD (i.val % 9))) hReads
  refine ⟨D, b, hD, hSize, hSmall, ?_⟩
  intro x
  obtain ⟨m, rfl⟩ := hCover x
  exact hValues m
