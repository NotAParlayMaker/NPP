import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2648_1 :
    (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
        D.size ≤ C.size ∧
        ∀ E : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 E →
          (∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x)) →
          D.size ≤ E.size) →
    (∀ (n : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 D →
      (∀ E : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 E →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x)) →
        D.size ≤ E.size) →
      (∃ x y : Fin n → Bool, D.eval (List.ofFn x) ≠ D.eval (List.ofFn y)) →
      ∃ (op : PEqualNP.CircuitLowerBounds.GateOp)
        (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ),
        D.gates = { op := op, inputs := [a, b] : PEqualNP.CircuitLowerBounds.Gate } :: gs ∧
        a < n ∧ b < n ∧ a ≠ b) →
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x5 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x5) = Bool.true ↔ x2 x5) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin (14 : ℕ) → Bool), x6.eval (List.ofFn x7) = Bool.true ↔ x2 x7) ∧ x6.size ≤ x3.size ∧ ∃ (x7 : PEqualNP.CircuitLowerBounds.GateOp) (x8 : List PEqualNP.CircuitLowerBounds.Gate) (x9 : ℕ) (x10 : ℕ), x6.gates = { op := x7, inputs := [x9, x10] : PEqualNP.CircuitLowerBounds.Gate } :: x8 ∧ x9 < (14 : ℕ) ∧ x10 < (14 : ℕ) ∧ x9 ≠ x10 := by
  intro minimal firstGate
  dsimp only
  intro C hC hfun
  obtain ⟨D, hD, hsame, hsize, hleast⟩ := minimal 14 C hC
  have hcorrect : ∀ x : Fin 14 → Bool,
      D.eval (List.ofFn x) = true ↔
        ∃ a b : Fin 14, (a.val, b.val) ∈
          ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
            (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
            (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧
          x a = true ∧ x b = true := by
    intro x
    rw [hsame x]
    exact hfun x
  have hzero : D.eval (List.ofFn (fun _ : Fin 14 => false)) = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hx := (hcorrect (fun _ => false)).mp htrue
    obtain ⟨a, b, _, ha, _⟩ := hx
    simp at ha
  let edgeInput : Fin 14 → Bool := fun i => decide (i = 0 ∨ i = 7)
  have hedge : D.eval (List.ofFn edgeInput) = true := by
    apply (hcorrect edgeInput).mpr
    refine ⟨0, 7, by decide, ?_, ?_⟩
    · simp [edgeInput]
    · simp [edgeInput]
  have hnonconstant :
      ∃ x y : Fin 14 → Bool, D.eval (List.ofFn x) ≠ D.eval (List.ofFn y) := by
    refine ⟨fun _ => false, edgeInput, ?_⟩
    rw [hzero, hedge]
    decide
  obtain ⟨op, gs, a, b, hfirst, ha, hb, hab⟩ :=
    firstGate 14 D hD hleast hnonconstant
  exact ⟨D, hD, hcorrect, hsize, op, gs, a, b, hfirst, ha, hb, hab⟩
