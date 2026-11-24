import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3262_1
    (h1 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (U : Finset ℕ),
      PEqualNP.TopForm.IsAO2 (n + n) C →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ((∀ w ∈ g.inputs, ∃ x : Fin n → Bool,
              (C.wires (List.ofFn x ++ List.replicate n false)).getD w false ≠
                (C.wires (List.ofFn x ++ List.replicate n true)).getD w false) ∨
           ∀ w ∈ g.inputs, ∃ x : Fin n → Bool,
              (C.wires (List.replicate n false ++ List.ofFn x)).getD w false ≠
                (C.wires (List.replicate n true ++ List.ofFn x)).getD w false)) →
        j ∈ U) →
      ∀ (j : ℕ), j < C.size → j ∉ U →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ P L : Finset (Fin n) → Bool, ∀ (X Y : Finset (Fin n)),
          PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) (n + n + j) = (P X && L Y))
    (h2 : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (π : Equiv.Perm (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (U : Finset ℕ),
      (∀ (a b c d : Fin n), a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
      (∀ (i : Fin n), (i, π i) ∈ E) →
      PEqualNP.TopForm.IsAO2 (n + n) C →
      (∀ (z : Fin (n + n) → Bool), PEqualNP.MetaComplexity.circuitFun (n + n) C z = Decidable.decide (∃ (i : Fin n) (j : Fin n), (i, j) ∈ E ∧ z (Fin.castAdd n i) = Bool.true ∧ z (Fin.natAdd n j) = Bool.true)) →
      U ⊆ Finset.range C.size →
      (∀ (j : ℕ), j < C.size → j ∉ U →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ P L : Finset (Fin n) → Bool, ∀ (X Y : Finset (Fin n)),
          PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) (n + n + j) = (P X && L Y)) →
      U.card < E.card + n →
      E.card + n ≤ C.size + 1) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x2 ∧ (x5, x8) ∈ x2 ∧ (x6, x7) ∈ x2 ∧ (x6, x8) ∈ x2)) → (∀ (x6 : Fin x1), (x6, x3 x6) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x2 ∧ x8 (Fin.castAdd x1 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 hC4 hMatch hAO hFun
  classical
  set U : Finset ℕ := (Finset.range x4.size).filter (fun j => ∃ g, x4.gates[j]? = some g ∧
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ((∀ w ∈ g.inputs, ∃ x : Fin x1 → Bool,
          (x4.wires (List.ofFn x ++ List.replicate x1 false)).getD w false ≠
            (x4.wires (List.ofFn x ++ List.replicate x1 true)).getD w false) ∨
       ∀ w ∈ g.inputs, ∃ x : Fin x1 → Bool,
          (x4.wires (List.replicate x1 false ++ List.ofFn x)).getD w false ≠
            (x4.wires (List.replicate x1 true ++ List.ofFn x)).getD w false))) with hUdef
  have hUsub : U ⊆ Finset.range x4.size := by
    rw [hUdef]
    exact Finset.filter_subset _ _
  have hUcard : U.card ≤ x4.size := by
    calc U.card ≤ (Finset.range x4.size).card := Finset.card_le_card hUsub
    _ = x4.size := Finset.card_range _
  have hrect : ∀ (j : ℕ), j < x4.size → j ∉ U →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∃ P L : Finset (Fin x1) → Bool, ∀ (X Y : Finset (Fin x1)),
        PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput X Y) (x1 + x1 + j) = (P X && L Y) := by
    intro j hj hjU hop
    refine h1 x1 x4 U hAO ?_ j hj hjU hop
    intro jj g hget hover
    rw [hUdef, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hget).1, g, hget, hover⟩
  by_cases hsmall : U.card < x2.card + x1
  · exact h2 x1 x2 x3 x4 U hC4 hMatch hAO hFun hUsub hrect hsmall
  · have hle : x2.card + x1 ≤ U.card := by omega
    calc x2.card + x1 ≤ U.card := hle
    _ ≤ x4.size := hUcard
    _ ≤ x4.size + 1 := Nat.le_succ _
