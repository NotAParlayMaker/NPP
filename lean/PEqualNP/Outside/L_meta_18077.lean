import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18077 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → x1.gates.head? ≠ Option.none := by
  intro C _ computes empty
  have hg : C.gates = [] := List.head?_eq_none_iff.mp empty
  let bits (k : Fin 13) (u : Fin 26) : Bool :=
    decide (u = Fin.castAdd 13 k ∨ u = Fin.natAdd 13 k)
  have active (k : Fin 13) : (List.ofFn (bits k)).getD C.output false = true := by
    have yes := (computes (bits k)).mpr ⟨k,k,Or.inl rfl,by simp [bits],by simp [bits]⟩
    simpa only [Circuit.eval, Circuit.wires, hg, List.foldl_nil] using yes
  have a := active 0
  have b := active 1
  by_cases h : C.output < 26
  · have read (k : Fin 13) : (List.ofFn (bits k)).getD C.output false = bits k ⟨C.output,h⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left h, Option.getD_some]
    rw [read] at a b
    have disjoint : ∀ i : Fin 26, bits 0 i = true → bits 1 i = false := by decide +kernel
    exact Bool.false_ne_true ((disjoint _ a).symm.trans b)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h)] at a
    cases a
