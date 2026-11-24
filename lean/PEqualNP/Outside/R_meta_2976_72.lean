import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2976_72
    (flatten : ∀ (n m : ℕ) (R : Fin n → Fin m → Prop) [DecidableRel R] (C : Circuit),
      (∀ a a' b b', a ≠ a' → b ≠ b' → ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b')) →
      IsAO2 (n+m) C →
      (∀ x, circuitFun (n+m) C x = decide (∃ a b, R a b ∧
         x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true)) →
      ∃ D : Circuit, IsAO2 (n+m) D ∧ D.size ≤ C.size ∧ circuitFun (n+m) D = circuitFun (n+m) C ∧
        SingleLevel.IsSingleLevel (n+m) D)
    (colour : ∀ (n m : ℕ) (D : Circuit), IsAO2 (n+m) D →
      SingleLevel.IsSingleLevel (n+m) D →
      (∀ b : Bool, circuitFun (n+m) D (fun i => decide (n ≤ i.val) == b) = false) →
      ∃ (T : Circuit) (S : Bool → Finset ℕ), IsAO2 (n+m) T ∧ T.size ≤ D.size ∧
        circuitFun (n+m) T = circuitFun (n+m) D ∧
        (∀ t w, w ∈ S t → (w < n+m ∧ decide (n ≤ w) = t) ∨
          ∃ i < T.size, w = n+m+i ∧ (gateAt T i).op = GateOp.or ∧
            ∀ u ∈ (gateAt T i).inputs, u ∈ S t) ∧
        ∀ i < T.size, (gateAt T i).op = GateOp.and →
          ∃ a b, (gateAt T i).inputs = [a,b] ∧ a ∈ S false ∧ b ∈ S true) :
∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x10 ∧ x16 ∈ x11 := by
  intro n m R _ C hsq hC heval
  obtain ⟨D, hD, hsize, hd, hlevel⟩ := flatten n m R C hsq hC heval
  have corners (b : Bool) :
      circuitFun (n+m) D (fun i => decide (n ≤ i.val) == b) = false := by
    rw [hd, heval]
    apply decide_eq_false
    rintro ⟨a, l, _, ha, hl⟩
    have h₁ : ¬ n ≤ (Fin.castAdd m a).val := by simp
    have h₂ : n ≤ (Fin.natAdd n l).val := by simp
    cases b <;> simp_all <;> omega
  obtain ⟨T, S, hT, hs, ht, closed, ordered⟩ := colour n m D hD hlevel corners
  refine ⟨T, S false, S true, hT, ?_, hs.trans hsize, ?_, ?_, ordered⟩
  · intro x
    rw [ht, hd, heval]
  · intro w hw
    rcases closed false w hw with ⟨_, h⟩ | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr h
  · intro w hw
    rcases closed true w hw with ⟨hw', h⟩ | h
    · exact Or.inl ⟨by simpa using h, hw'⟩
    · exact Or.inr h
