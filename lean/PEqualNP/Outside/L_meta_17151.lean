import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17151 : (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin (13 : ℕ)) (x7 : Bool), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x9 : Fin x5.gates.length), ∀ x10 ∈ (x5.gates.get x9).inputs, x10 < (27 : ℕ) + ↑x9) → (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x1 → x10 ≠ (0 : Fin (13 : ℕ)) ∨ x11 ≠ x6 → x5.eval (x2 x10 x11 ++ [x7]) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x4 x11 → x5.eval (x3 x11 ++ [x7]) = Bool.false) → x5.gates = [] → (63 : ℕ) ≤ x5.size) := by
  intro d pos neg quad c exc visible hmono back good bad empty
  have one := good 1 1 (by decide) (Or.inl (by decide))
  have two := good 2 2 (by decide) (Or.inl (by decide))
  let q : Finset (Fin 13) := {0,1,2,5}
  have zero := bad q (by decide +kernel)
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
    empty, List.foldl_nil] at one two zero
  by_cases h : c.output < 27
  · let o : Fin 27 := ⟨c.output,h⟩
    have clash : ∀ (v : Bool) (j : Fin 27),
        (pos 1 1 ++ [v]).getD j.val false = true →
        (pos 2 2 ++ [v]).getD j.val false = true →
        (neg q ++ [v]).getD j.val false = false → False := by decide +kernel
    exact False.elim (clash visible o one two zero)
  · have hl : (pos 1 1 ++ [visible]).length ≤ c.output := by
      change 27 ≤ c.output
      omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl, Option.getD_none] at one
    contradiction
