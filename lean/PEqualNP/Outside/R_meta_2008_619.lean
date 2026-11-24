import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

-- Derive the dual incidence counts and orient each unmarked AND gate by its pure operands.
-- It suffices to test rejection on all points missed by each small set of lines.

theorem PEqualNP.Outside.R_meta_2008_619
    (hPlane :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)),
        0 < q → n = q ^ 2 + q + 1 →
        (∀ l, (S l).card = q + 1) →
        (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
        (∀ p, Fintype.card {l : Fin n // p ∈ S l} = q + 1) ∧
        (∀ l m, l ≠ m → (S l ∩ S m).card = 1))
    (hSplit :
      ∀ (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate),
        Monotone2 C →
        (∀ k h, C.gates[k]? = some h →
          ∃ a b, h.inputs = [a,b] ∧ a < b ∧ b < n + n + k) →
        C.gates[j]? = some g → g.op = GateOp.and →
        ¬ ((∀ i ∈ g.inputs, ∃ x : Fin n → Bool,
              (C.wires (List.ofFn x ++ List.replicate n false)).getD i false ≠
              (C.wires (List.ofFn x ++ List.replicate n true)).getD i false) ∨
           ∀ i ∈ g.inputs, ∃ y : Fin n → Bool,
              (C.wires (List.replicate n false ++ List.ofFn y)).getD i false ≠
              (C.wires (List.replicate n true ++ List.ofFn y)).getD i false) →
        ∃ a b, (g.inputs = [a,b] ∨ g.inputs = [b,a]) ∧
          ∀ x y : Fin n → Bool,
            (C.wires (List.ofFn x ++ List.ofFn y)).getD a false =
              (C.wires (List.ofFn x ++ List.replicate n false)).getD a false ∧
            (C.wires (List.ofFn x ++ List.ofFn y)).getD b false =
              (C.wires (List.replicate n false ++ List.ofFn y)).getD b false)
    (hBound :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (X : Finset ℕ),
        100 < q → n = q ^ 2 + q + 1 →
        (∀ l, (S l).card = q + 1) →
        (∀ p, Fintype.card {l : Fin n // p ∈ S l} = q + 1) →
        (∀ l m, l ≠ m → (S l ∩ S m).card = 1) →
        Monotone2 C → C.output < n + n + C.size →
        (∀ j g, C.gates[j]? = some g →
          ∃ a b, g.inputs = [a,b] ∧ a < b ∧ b < n + n + j) →
        RightOnIncidentPairs S C →
        (∀ Y : Finset (Fin n), Y.card ≤ q →
          C.eval (incidenceInput (zeroSet S Y) Y) = false) →
        (∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∉ X →
          ∃ a b, (g.inputs = [a,b] ∨ g.inputs = [b,a]) ∧
            ∀ x y : Fin n → Bool,
              (C.wires (List.ofFn x ++ List.ofFn y)).getD a false =
                (C.wires (List.ofFn x ++ List.replicate n false)).getD a false ∧
              (C.wires (List.ofFn x ++ List.ofFn y)).getD b false =
                (C.wires (List.replicate n false ++ List.ofFn y)).getD b false) →
        100 * X.card < n * q → n * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n R inst C hq hn hDegree hUnique hMono hOut hSorted hAccept hReject X hMarked hBudget
  let S : Fin n → Finset (Fin n) := fun l => Finset.univ.filter (fun p => R p l)
  have memS (p l : Fin n) : p ∈ S l ↔ R p l := by simp [S]
  have degree (l : Fin n) : (S l).card = q + 1 := by
    simpa [S, Fintype.card_subtype] using hDegree l
  have pairs (p r : Fin n) (hne : p ≠ r) : ∃! l, p ∈ S l ∧ r ∈ S l := by
    simpa only [memS] using hUnique p r hne
  obtain ⟨pointDegree, lineMeet⟩ := hPlane q n S (by omega) hn degree pairs
  have encode (A B : Finset (Fin n)) :
      List.ofFn (Fin.append (fun p => decide (p ∈ A)) (fun l => decide (l ∈ B))) =
        incidenceInput A B :=
    List.ofFn_fin_append _ _
  have positive : RightOnIncidentPairs S C := by
    intro l p hp
    have hPair :
        Fin.append (fun r : Fin n => decide (r ∈ ({p} : Finset (Fin n))))
          (fun m : Fin n => decide (m ∈ ({l} : Finset (Fin n)))) =
        (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) := by
      funext i
      refine Fin.addCases (fun r => ?_) (fun m => ?_) i
      · rw [Fin.append_left]
        have unequal : Fin.castAdd n r ≠ Fin.natAdd n l := by
          intro eq
          have hv := congrArg Fin.val eq
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        simp only [Finset.mem_singleton, unequal, or_false, Fin.ext_iff, Fin.val_castAdd]
      · rw [Fin.append_right]
        have unequal : Fin.natAdd n m ≠ Fin.castAdd n p := by
          intro eq
          have hv := congrArg Fin.val eq
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        simp only [Finset.mem_singleton, unequal, false_or, Fin.ext_iff, Fin.val_natAdd, Nat.add_left_cancel_iff]
    rw [← encode, hPair]
    exact hAccept p l ((memS p l).1 hp)
  have negative (Y : Finset (Fin n)) (hy : Y.card ≤ q) :
      C.eval (incidenceInput (zeroSet S Y) Y) = false := by
    let z := Fin.append (fun p : Fin n => decide (p ∈ zeroSet S Y))
      (fun l : Fin n => decide (l ∈ Y))
    have pointMask (p : Fin n) : z (Fin.castAdd n p) = decide (p ∈ zeroSet S Y) :=
      Fin.append_left _ _ _
    have lineMask (l : Fin n) : z (Fin.natAdd n l) = decide (l ∈ Y) :=
      Fin.append_right _ _ _
    have lineSupport : Finset.univ.filter (fun l => z (Fin.natAdd n l) = true) = Y := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, lineMask, decide_eq_true_eq]
    have bound : Fintype.card { l : Fin n // z (Fin.natAdd n l) = true } ≤ q := by
      rwa [Fintype.card_subtype, lineSupport]
    have noEdge : ¬ ∃ p l, R p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true := by
      rintro ⟨p, l, hR, hp, hl⟩
      have hp' : p ∈ zeroSet S Y := by simpa only [pointMask, decide_eq_true_eq] using hp
      have hl' : l ∈ Y := by simpa only [lineMask, decide_eq_true_eq] using hl
      have none := (Finset.mem_filter.mp hp').2
      exact none l hl' ((memS p l).2 hR)
    rw [← encode]
    exact hReject z bound noEdge
  refine hBound q n S C X hq hn degree pointDegree lineMeet hMono hOut hSorted positive negative ?_ hBudget
  intro j g hg hand hOutside
  exact hSplit n C j g hMono hSorted hg hand (hMarked j g hg hand hOutside)
