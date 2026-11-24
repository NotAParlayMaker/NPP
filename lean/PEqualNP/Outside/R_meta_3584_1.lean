import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3584_1
    (hCircuitCover :
      ∀ (f : (Fin 9 → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ x : Fin 9 → Bool,
          f x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
            (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
            (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
            (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
        PEqualNP.MetaComplexity.FanInTwo C →
        (∀ x : Fin 9 → Bool,
          C.eval (List.ofFn x ++ [x 0 || x 2]) = f x) →
        (let used : List ℕ := List.flatMap
          (fun g : PEqualNP.CircuitLowerBounds.Gate =>
            List.take (bif g.op.eval [Bool.false] then 1 else 2) g.inputs) C.gates;
         (∀ i : ℕ, i < 10 + C.size → i ≠ C.output → i ∈ used) ∧
          (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate =>
            g.op.eval [Bool.false]) C.gates).length +
            (used.length - used.toFinset.card) ≤ 5) →
        (∀ (v : Fin 9) (w : Fin 10), v ≠ 0 → v ≠ 2 → v.castSucc ≠ w →
          ∀ g ∈ C.gates,
            g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
              g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
            g.inputs = [↑v, ↑w] ∨ g.inputs = [↑w, ↑v] →
            2 ≤ (List.filter (fun g' : PEqualNP.CircuitLowerBounds.Gate =>
              (List.take (bif g'.op.eval [Bool.false] then 1 else 2) g'.inputs).contains ↑v)
              C.gates).length) →
        C.size < 15 →
        ∃ T : Finset (Fin 11), T.card < 7 ∧
          ∀ e ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
            (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
            (6, 7), (6, 10), (7, 9), (8, 9)] : List (Fin 11 × Fin 11)),
            e.1 ∈ T ∨ e.2 ∈ T)
    (hNoCover :
      ∀ T : Finset (Fin 11), T.card < 7 →
        ∃ e ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
          (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
          (6, 7), (6, 10), (7, 9), (8, 9)] : List (Fin 11 × Fin 11)),
          e.1 ∉ T ∧ e.2 ∉ T ∧ e.1 ≠ e.2) :
    have x1 : (Fin 9 → Bool) → Bool := fun x =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
      (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
      (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 2]) = x1 x) →
      (have x5 : List ℕ := List.flatMap
        (fun x5 : PEqualNP.CircuitLowerBounds.Gate =>
          List.take (bif x5.op.eval [Bool.false] then 1 else 2) x5.inputs) C.gates;
       (∀ x6 < 10 + C.size, x6 ≠ C.output → x6 ∈ x5) ∧
        (List.filter (fun x6 : PEqualNP.CircuitLowerBounds.Gate =>
          x6.op.eval [Bool.false]) C.gates).length +
          (x5.length - x5.toFinset.card) ≤ 5) →
      (∀ (x6 : Fin 9) (x7 : Fin 10), x6 ≠ 0 → x6 ≠ 2 → x6.castSucc ≠ x7 →
        ∀ x11 ∈ C.gates,
          x11.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            x11.op = PEqualNP.CircuitLowerBounds.GateOp.or →
          x11.inputs = [↑x6, ↑x7] ∨ x11.inputs = [↑x7, ↑x6] →
          2 ≤ (List.filter (fun x15 : PEqualNP.CircuitLowerBounds.Gate =>
            (List.take (bif x15.op.eval [Bool.false] then 1 else 2) x15.inputs).contains ↑x6)
            C.gates).length) →
      15 ≤ C.size := by
  classical
  intro x1 C hFan hEval hUsed hPair
  by_contra hNot
  have hSmall : C.size < 15 := Nat.lt_of_not_ge hNot
  have hSpec : ∀ x : Fin 9 → Bool,
      x1 x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
        (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
        (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    intro x
    rfl
  obtain ⟨T, hT, hCover⟩ := hCircuitCover x1 C hSpec hFan hEval hUsed hPair hSmall
  obtain ⟨e, he, hLeft, hRight, _⟩ := hNoCover T hT
  rcases hCover e he with h | h
  · exact hLeft h
  · exact hRight h
