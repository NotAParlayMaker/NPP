import PEqualNP.Defs

-- Complement inputs and values so each original OR becomes one counted AND.
-- The first premise removes free gates. The second is a finite lower bound
-- on the resulting circuits with two unrestricted disjunctions per gate.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_1896_1
    (normalize : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∃ input, PEqualNP.MetaComplexity.circuitFun 26 C input = true) →
      ∃ D : PEqualNP.AndCount.AndCountCircuit 26, D.WellFormed ∧
        D.size ≤ {i : Fin C.gates.length | (C.gates.get i).op =
          PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧
        ∀ input, PEqualNP.MetaComplexity.circuitFun 26 C input =
          !(D.eval (Finset.univ.filter (fun i => !input i))))
    (bound :
      let incident := fun p w : Fin 13 => p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26, D.WellFormed →
        let value := fun (input : Fin 26 → Bool) =>
          !(D.eval (Finset.univ.filter (fun i => !input i)))
        (∀ p w, incident p w →
          value (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w)) = true) →
        (∀ P : Finset (Fin 13),
          (∀ v ∉ P, ∃ w, (∀ p ∈ P, ¬ incident p w) ∧ incident v w) →
          ((¬ ∃ w, ∀ p ∈ P, incident p w) ∧
            ¬ ∃ v, ∀ w, (∀ p ∈ P, ¬ incident p w) → incident v w) →
          value (fun i => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
            ∃ w, i = Fin.natAdd 13 w ∧ ∀ p ∈ P, ¬ incident p w)) = false) →
        51 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (51 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C hm hp hn
  obtain ⟨D, hw, hs, he⟩ := normalize C hm ⟨_, hp 0 0 (Or.inl rfl)⟩
  simp only [he] at hp hn
  exact (bound D hw hp hn).trans hs
