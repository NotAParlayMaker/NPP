import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5040_1 :
    let incident : Fin 13 → Fin 13 → Prop :=
      fun p w =>
        p = w + (0 : Fin 13) ∨ p = w + (1 : Fin 13) ∨
          p = w + (3 : Fin 13) ∨ p = w + (9 : Fin 13)
    let admissible : Finset (Fin 13) → Finset (Fin 13) → Prop :=
      fun P W =>
        (∀ p ∈ P, ∀ w ∈ W, ¬ incident p w) ∧
          (∀ w : Fin 13, (P.filter (fun p => incident p w)).card ≤ 2) ∧
          (∀ p : Fin 13, (W.filter (fun w => incident p w)).card ≤ 2)
    let contains : Finset (Fin 13) → Finset (Fin 13) → (Fin 26 → Bool) → Prop :=
      fun P W z =>
        (∀ p ∈ P, z (Fin.castAdd 13 p) = Bool.true) ∧
          (∀ w ∈ W, z (Fin.natAdd 13 w) = Bool.true)
    let rowInput : ℕ → Fin 13 → (Fin 26 → Bool) :=
      fun m t x =>
        Decidable.decide
          ((∃ q : Fin 13,
              m.testBit ↑(q - t) = Bool.true ∧ x = Fin.castAdd 13 q) ∨
            ∃ q : Fin 13,
              m.testBit (13 + ↑(q - t)) = Bool.true ∧ x = Fin.natAdd 13 q)
    let rows : List ℕ :=
      [ (7405575 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ),
        (21757977 : ℕ), (21233693 : ℕ), (3735587 : ℕ), (19988517 : ℕ),
        (3211303 : ℕ), (19415081 : ℕ), (7372867 : ℕ), (24117317 : ℕ),
        (7340103 : ℕ), (23085129 : ℕ), (23068749 : ℕ), (22052945 : ℕ),
        (5275731 : ℕ), (22020181 : ℕ), (19939425 : ℕ), (19923045 : ℕ),
        (18890857 : ℕ), (6389891 : ℕ), (6619269 : ℕ), (6357127 : ℕ),
        (6570121 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ),
        (21512457 : ℕ), (21528849 : ℕ), (4751635 : ℕ), (21496089 : ℕ),
        (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ) ]
    (∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      C.size ≤ (63 : ℕ) →
      C.output + (1 : ℕ) = (26 : ℕ) + C.size →
      (∀ g ∈ C.gates.zipIdx, ∀ i ∈ g.1.inputs,
        i < (26 : ℕ) + g.2 ∨ i = (89 : ℕ)) →
      ¬PEqualNP.CircuitLowerBounds.HasLineDegree
        (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) C (1 : ℕ) →
      ¬PEqualNP.CircuitLowerBounds.HasLineDegree
        (26 : ℕ) (Finset.range (13 : ℕ)) C (1 : ℕ) →
      (∀ (p d : Fin 13),
        d = (0 : Fin 13) ∨ d = (1 : Fin 13) ∨ d = (3 : Fin 13) ∨ d = (9 : Fin 13) →
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun x : Fin 26 =>
              Decidable.decide
                (x = Fin.castAdd 13 (p + d) ∨ x = Fin.natAdd 13 p)) = Bool.true) →
      ∃ (P W : Finset (Fin 13)),
        admissible P W ∧
          ∀ z : Fin 26 → Bool, contains P W z →
            PEqualNP.MetaComplexity.circuitFun 26 C z = Bool.true) →
    (∀ (P W : Finset (Fin 13)), admissible P W →
      ∃ (m : ℕ), m ∈ rows ∧
        ∃ t : Fin 13, contains P W (rowInput m t)) →
    ¬∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (63 : ℕ) ∧
        C.output + (1 : ℕ) = (26 : ℕ) + C.size ∧
        (∀ g ∈ C.gates.zipIdx, ∀ i ∈ g.1.inputs,
          i < (26 : ℕ) + g.2 ∨ i = (89 : ℕ)) ∧
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree
          (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) C (1 : ℕ) ∧
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree
          (26 : ℕ) (Finset.range (13 : ℕ)) C (1 : ℕ) ∧
        (∀ (p d : Fin 13),
          d = (0 : Fin 13) ∨ d = (1 : Fin 13) ∨ d = (3 : Fin 13) ∨ d = (9 : Fin 13) →
            PEqualNP.MetaComplexity.circuitFun 26 C
              (fun x : Fin 26 =>
                Decidable.decide
                  (x = Fin.castAdd 13 (p + d) ∨ x = Fin.natAdd 13 p)) = Bool.true) ∧
        ∀ m ∈ rows, ∀ t : Fin 13,
          PEqualNP.MetaComplexity.circuitFun 26 C (rowInput m t) = Bool.false := by
  dsimp
  intro hStructure hCover
  rintro ⟨C, hC⟩
  rcases hC with
    ⟨hMono, hSize, hOutput, hInputs, hRightDegree, hLeftDegree, hIncident, hRows⟩
  rcases hStructure C hMono hSize hOutput hInputs hRightDegree hLeftDegree hIncident with
    ⟨P, W, hAdmissible, hAccept⟩
  rcases hCover P W hAdmissible with ⟨m, hm, t, hContains⟩
  have hTrue := hAccept
    (fun x : Fin 26 =>
      Decidable.decide
        ((∃ q : Fin 13, m.testBit ↑(q - t) = Bool.true ∧ x = Fin.castAdd 13 q) ∨
          ∃ q : Fin 13, m.testBit (13 + ↑(q - t)) = Bool.true ∧ x = Fin.natAdd 13 q))
    hContains
  have hFalse := hRows m hm t
  exact Bool.noConfusion (hTrue.symm.trans hFalse)
