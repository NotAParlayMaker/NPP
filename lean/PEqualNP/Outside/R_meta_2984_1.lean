import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2984_1
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
    (h2 : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit) (U : Finset ℕ),
      (200 : ℕ) ≤ q → N = q ^ (2 : ℕ) + q + (1 : ℕ) →
      (∀ (l : Fin N), (S l).card = q + (1 : ℕ)) →
      (∀ (p p' : Fin N), p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l) →
      PEqualNP.TopForm.IsAO2 (N + N) C → C.output < N + N + C.size →
      PEqualNP.GenericRejection.RightOnIncidentPairs S C →
      (∀ (X Y : Finset (Fin N)), Y.card ≤ q → PEqualNP.GenericRejection.IsFalseInput S X Y →
        C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = Bool.false) →
      U ⊆ Finset.range C.size →
      (∀ (j : ℕ), j < C.size → j ∉ U →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ P L : Finset (Fin N) → Bool, ∀ (X Y : Finset (Fin N)),
          PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) (N + N + j) = (P X && L Y)) →
      (100 : ℕ) * U.card < N * q →
      N * q ≤ (100 : ℕ) * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 hq hN hline huniq hAO hOut hRight hSound
  classical
  set U : Finset ℕ := (Finset.range x4.size).filter (fun j => ∃ g, x4.gates[j]? = some g ∧
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ((∀ w ∈ g.inputs, ∃ x : Fin x2 → Bool,
          (x4.wires (List.ofFn x ++ List.replicate x2 false)).getD w false ≠
            (x4.wires (List.ofFn x ++ List.replicate x2 true)).getD w false) ∨
       ∀ w ∈ g.inputs, ∃ x : Fin x2 → Bool,
          (x4.wires (List.replicate x2 false ++ List.ofFn x)).getD w false ≠
            (x4.wires (List.replicate x2 true ++ List.ofFn x)).getD w false))) with hUdef
  have hUsub : U ⊆ Finset.range x4.size := by
    rw [hUdef]
    exact Finset.filter_subset _ _
  have hUcard : U.card ≤ x4.size := by
    calc U.card ≤ (Finset.range x4.size).card := Finset.card_le_card hUsub
    _ = x4.size := Finset.card_range _
  have hrect : ∀ (j : ℕ), j < x4.size → j ∉ U →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∃ P L : Finset (Fin x2) → Bool, ∀ (X Y : Finset (Fin x2)),
        PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput X Y) (x2 + x2 + j) = (P X && L Y) := by
    intro j hj hjU hop
    refine h1 x2 x4 U hAO ?_ j hj hjU hop
    intro jj g hget hover
    rw [hUdef, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hget).1, g, hget, hover⟩
  by_cases hsmall : (100 : ℕ) * U.card < x2 * x1
  · exact h2 x1 x2 x3 x4 U hq hN hline huniq hAO hOut hRight hSound hUsub hrect hsmall
  · have hle : x2 * x1 ≤ (100 : ℕ) * U.card := by omega
    calc x2 * x1 ≤ (100 : ℕ) * U.card := hle
    _ ≤ (100 : ℕ) * x4.size := Nat.mul_le_mul_left 100 hUcard
