import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- A second cut of the order-three bound: the flat case plus a nesting-count decrease.
theorem PEqualNP.Outside.R_meta_1692_2
  (hflat : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C → x2 C → ¬ x3 C → (64 : ℕ) ≤ C.size)
  (hstep : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C → x2 C → C.size < (64 : ℕ) → x3 C → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) D ∧ x2 D ∧ D.size ≤ C.size ∧ (by classical exact (D.gates.filter (fun g => g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ w ∈ g.inputs, ∃ j : ℕ, w = (26 : ℕ) + j ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and)).length) < (by classical exact (C.gates.filter (fun g => g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ w ∈ g.inputs, ∃ j : ℕ, w = (26 : ℕ) + j ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and)).length)) :
  ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  intro gates out hops hreads hpos hneg
  let diff : Finset (Fin 13) := {0, 1, 3, 9}
  let correct : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun E =>
    (∀ p l : Fin 13, p - l ∈ diff → E.eval
      (List.ofFn (fun p' : Fin 13 => decide (p' = p)) ++
        List.ofFn (fun l' : Fin 13 => decide (l' = l))) = true) ∧
    ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2) → E.eval
      (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ diff))) = false
  let nested : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun E =>
    ∃ i j : ℕ, (gateAt E i).op = GateOp.and ∧ (gateAt E j).op = GateOp.and ∧
      InCone 26 E i j
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, out⟩
  have hmon : PEqualNP.MetaComplexity.Monotone2 C := by
    change ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hops
  have hback : PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C := by
    intro j hj w hw
    have hj' : j < gates.length := hj
    change w ∈ (gates.getD j ⟨GateOp.or, []⟩).inputs at hw
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at hw
    exact hreads ⟨j, hj'⟩ w hw
  have hcorrect : correct C := by
    constructor
    · intro p l hpl
      exact hpos p l hpl
    · intro Q hQ hseg
      exact hneg Q hQ hseg
  let m : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun E =>
(by classical exact (E.gates.filter (fun g => g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ w ∈ g.inputs, ∃ j : ℕ, w = (26 : ℕ) + j ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt E j).op = PEqualNP.CircuitLowerBounds.GateOp.and)).length)
  have lower : ∀ n : ℕ, ∀ E : PEqualNP.CircuitLowerBounds.Circuit,
      m E = n → PEqualNP.MetaComplexity.Monotone2 E →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) E →
      correct E → (64 : ℕ) ≤ E.size := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro E hmE hmEmon hbE hcE
      by_cases hbig : (64 : ℕ) ≤ E.size
      · exact hbig
      · have hsmall : E.size < (64 : ℕ) := by omega
        by_cases hnestedE : nested E
        · obtain ⟨D, hmD, hbD, hcD, hle, hlt⟩ := hstep E hmEmon hbE hcE hsmall hnestedE
          have hltm : m D < n := by rw [← hmE]; exact hlt
          have hDlower : (64 : ℕ) ≤ D.size := ih (m D) hltm D rfl hmD hbD hcD
          omega
        · exact hflat E hmEmon hbE hcE hnestedE
  exact lower (m C) C rfl hmon hback hcorrect
