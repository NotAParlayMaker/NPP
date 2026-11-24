import Mathlib
import PEqualNP.Defs

-- A minimum passing circuit can be made binary with all inputs earlier than their gate.
-- The pair tests rule out a minimum circuit whose AND gates all pass those tests.
-- Only the case with an AND gate that accepts a rejected pair remains.
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2718_417
    (normalize : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠
        PEqualNP.MetaComplexity.circuitFun n C y) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
        PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ C.size ∧
        Monotone (PEqualNP.MetaComplexity.circuitFun n D) ∧
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C)
    (pairTests : let D : Finset (Fin 13) := {0,1,3,9};
let I : Fin 13 → Fin 13 → Prop := fun p l => ∃ d ∈ D, p = l+d;
∀ f : (Fin 26 → Bool) → Bool, Monotone f →
      (∀ p l, I p l → f (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
      (∀ P : Finset (Fin 13), (∀ p ∉ P, ∃ l, (∀ r ∈ P, ¬ I r l) ∧ I p l) →
        ((∃ l, ∀ p ∈ P, I p l) ∨ ∃ p, ∀ l, (∀ r ∈ P, ¬ I r l) → I p l) →
        f (fun i => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
          ∃ l, i = Fin.natAdd 13 l ∧ ∀ p ∈ P, ¬ I p l)) = false) →
      ∀ u v : Fin 26, f (fun i => decide (i = u ∨ i = v)) = true ↔
        ∃ p l, I p l ∧ (Fin.castAdd 13 p = u ∨ Fin.castAdd 13 p = v) ∧
          (Fin.natAdd 13 l = u ∨ Fin.natAdd 13 l = v))
    (floor : let shifts : Finset (Fin 13) := {0,1,3,9};
∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 26 C →
      (∀ u v : Fin 26, PEqualNP.MetaComplexity.circuitFun 26 C (fun i => decide (i = u ∨ i = v)) = true ↔
        ∃ p l : Fin 13, (∃ d ∈ shifts, p = l+d) ∧
          (Fin.castAdd 13 p = u ∨ Fin.castAdd 13 p = v) ∧
          (Fin.natAdd 13 l = u ∨ Fin.natAdd 13 l = v)) →
      (∀ j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ u v : Fin 26, (C.wires (List.ofFn fun i : Fin 26 => decide (i = u ∨ i = v))).getD (26+j) false = true →
          PEqualNP.MetaComplexity.circuitFun 26 C (fun i => decide (i = u ∨ i = v)) = true) →
      64 ≤ C.size)
    (core : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∨ ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → PEqualNP.TopForm.IsAO2 26 x3 → (∀ E : PEqualNP.CircuitLowerBounds.Circuit, x2 E → x3.size ≤ E.size) → (¬ (∀ j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 j).op =
      PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u v : Fin 26,
      (x3.wires (List.ofFn fun i : Fin 26 => decide (i = u ∨ i = v))).getD (26+j) false = true →
      PEqualNP.MetaComplexity.circuitFun 26 x3 (fun i => decide (i = u ∨ i = v)) = true)) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 ∧ (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x5 (1 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x5 (1 : ℕ)))
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∨ ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 ∧ (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x5 (1 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x5 (1 : ℕ)) := by
  intro shifts passing C passC
  classical
  have available : ∃ k, ∃ E : PEqualNP.CircuitLowerBounds.Circuit, passing E ∧ E.size = k :=
    ⟨C.size,C,passC,rfl⟩
  obtain ⟨least,pass,eq⟩ := Nat.find_spec available
  have minimum (E : PEqualNP.CircuitLowerBounds.Circuit) (h : passing E) : least.size ≤ E.size :=
    eq.symm ▸ Nat.find_min' available ⟨E,h,rfl⟩
  have accepts := pass.2.2.1 0 0 ⟨0,by simp [shifts],by decide⟩
  have maximal : ∀ p ∉ (∅ : Finset (Fin 13)), ∃ l : Fin 13,
      (∀ r ∈ (∅ : Finset (Fin 13)), ¬ ∃ d ∈ shifts, r = l+d) ∧ ∃ d ∈ shifts, p = l+d := by
    intro p _
    exact ⟨p,by simp,⟨0,by simp [shifts],by simp⟩⟩
  have rejects := pass.2.2.2 ∅ maximal (Or.inl ⟨0,by simp⟩)
  have someOn : ∃ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 least x = true := ⟨_,accepts⟩
  have someOff : ∃ y : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 least y = false := ⟨_,rejects⟩
  have nonconstant : ∃ x y : Fin 26 → Bool,
      PEqualNP.MetaComplexity.circuitFun 26 least x ≠ PEqualNP.MetaComplexity.circuitFun 26 least y := by
    obtain ⟨x,hx⟩ := someOn
    obtain ⟨y,hy⟩ := someOff
    exact ⟨x,y,by simp [hx,hy]⟩
  obtain ⟨clean,earlier,binary,budget,monotone,same⟩ := normalize 26 least pass.1 nonconstant
  have cleanPass : passing clean := by
    refine ⟨binary,budget.trans pass.2.1,?_,?_⟩
    · intro p l edge
      exact (congrFun same _).trans (pass.2.2.1 p l edge)
    · intro P max degenerate
      exact (congrFun same _).trans (pass.2.2.2 P max degenerate)
  have dirty : ¬ (∀ j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt clean j).op =
      PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u v : Fin 26,
      (clean.wires (List.ofFn fun i : Fin 26 => decide (i = u ∨ i = v))).getD (26+j) false = true →
      PEqualNP.MetaComplexity.circuitFun 26 clean (fun i => decide (i = u ∨ i = v)) = true) := by
    intro sound
    have pairs := pairTests _ monotone cleanPass.2.2.1 cleanPass.2.2.2
    have exceeds := floor clean earlier pairs sound
    have limit := cleanPass.2.1
    omega
  exact core clean cleanPass earlier (fun E h => budget.trans (minimum E h)) dirty
