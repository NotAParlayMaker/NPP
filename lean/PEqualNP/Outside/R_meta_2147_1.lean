import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2147_1
    (hor : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ p w : Fin 13,
        (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) →
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) →
      (∀ P : Finset (Fin 13),
        (∀ v : Fin 13, v ∉ P →
          ∃ w2 : Fin 13,
            (∀ pp ∈ P, ¬ ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd) ∧
            (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) →
        (¬ ∃ w3 : Fin 13, ∀ p3 ∈ P,
          ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd) ∧
        (¬ ∃ v4 : Fin 13, ∀ w4 : Fin 13,
          (∀ pp ∈ P, ¬ ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd) →
          ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd) →
        PEqualNP.MetaComplexity.circuitFun 26 C
          (fun kk : Fin 26 => decide
            ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
              ∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
                ∀ pp ∈ P, ¬ ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd)) = false) →
      51 ≤ {i : Fin C.gates.length |
        (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)
    (hand : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ p w : Fin 13,
        (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) →
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) →
      (∀ P : Finset (Fin 13),
        (∀ v : Fin 13, v ∉ P →
          ∃ w2 : Fin 13,
            (∀ pp ∈ P, ¬ ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd) ∧
            (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) →
        (¬ ∃ w3 : Fin 13, ∀ p3 ∈ P,
          ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd) ∧
        (¬ ∃ v4 : Fin 13, ∀ w4 : Fin 13,
          (∀ pp ∈ P, ¬ ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd) →
          ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd) →
        PEqualNP.MetaComplexity.circuitFun 26 C
          (fun kk : Fin 26 => decide
            ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
              ∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
                ∀ pp ∈ P, ¬ ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd)) = false) →
      13 ≤ {i : Fin C.gates.length |
        (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) :
    have x1 : Finset (Fin 13) := {0, 1, 3, 9};
    ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧
      ¬ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 ∧
      ¬ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.range 13) C 1 ∧
      (∀ p w : Fin 13,
        (∃ dd ∈ x1, p = w + dd) →
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
      (∀ P : Finset (Fin 13),
        (∀ v : Fin 13, v ∉ P →
          ∃ w2 : Fin 13,
            (∀ pp ∈ P, ¬ ∃ dd ∈ x1, pp = w2 + dd) ∧
            (∃ dd ∈ x1, v = w2 + dd)) →
        (¬ ∃ w3 : Fin 13, ∀ p3 ∈ P, ∃ dd ∈ x1, p3 = w3 + dd) ∧
        (¬ ∃ v4 : Fin 13, ∀ w4 : Fin 13,
          (∀ pp ∈ P, ¬ ∃ dd ∈ x1, pp = w4 + dd) →
          ∃ dd ∈ x1, v4 = w4 + dd) →
        PEqualNP.MetaComplexity.circuitFun 26 C
          (fun kk : Fin 26 => decide
            ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
              ∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
                ∀ pp ∈ P, ¬ ∃ dd ∈ x1, pp = ww + dd)) = false) := by
  intro x1
  intro hx1
  obtain ⟨C, hmono, hsize, hld1, hld2, hpos, hneg⟩ := hx1
  have hor' := hor C hmono hpos hneg
  have hand' := hand C hmono hpos hneg
  have hdisj : Disjoint
      {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}
      {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
    rw [Set.disjoint_left]
    intro i ha hb
    rw [Set.mem_ofPred_eq] at ha hb
    rw [ha] at hb
    exact PEqualNP.CircuitLowerBounds.GateOp.noConfusion hb
  have hsum := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle :
      ({i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or} ∪
        {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}).ncard ≤
        C.gates.length := by
    calc
      _ ≤ (Set.univ : Set (Fin C.gates.length)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = C.gates.length := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hs : C.size = C.gates.length := rfl
  have hcount : 64 ≤
      ({i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or} ∪
        {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}).ncard := by
    calc
      64 = 51 + 13 := by decide
      _ ≤
          {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard +
            {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
        Nat.add_le_add hor' hand'
      _ = _ := hsum.symm
  have hlen : 64 ≤ C.gates.length := hcount.trans hle
  have hsize64 : 64 ≤ C.size := by
    calc
      64 ≤ C.gates.length := hlen
      _ = C.size := hs.symm
  have hbad : 64 ≤ 63 := Nat.le_trans hsize64 hsize
  exact (Nat.not_le_of_gt (by decide : 63 < 64)) hbad
