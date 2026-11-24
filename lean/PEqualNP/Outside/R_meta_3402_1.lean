import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3402_1
    (c0 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → PEqualNP.NotBracket.notCount x1 = (0 : ℕ) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x7 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x7.1 && x6 x7.2) → x1.gates = [] → (14 : ℕ) ≤ x1.size)
    (cAnd : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → PEqualNP.NotBracket.notCount x1 = (0 : ℕ) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x7 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x7.1 && x6 x7.2) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = g :: gs ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (14 : ℕ) ≤ x1.size)
    (cOr : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → PEqualNP.NotBracket.notCount x1 = (0 : ℕ) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x7 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x7.1 && x6 x7.2) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = g :: gs ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (14 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → PEqualNP.NotBracket.notCount x1 = (0 : ℕ) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x7 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x7.1 && x6 x7.2) → (14 : ℕ) ≤ x1.size := by
  intro x1 x2 hfan hcard hnot hcomp
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  rcases x1 with ⟨gs, out⟩
  cases gs with
  | nil => exact c0 ⟨[], out⟩ x2 hfan hcard hnot hcomp rfl
  | cons g gs =>
    have hmem : g ∈ (⟨g :: gs, out⟩ : PEqualNP.CircuitLowerBounds.Circuit).gates := List.mem_cons_self
    obtain ⟨hop, _⟩ := hfan g hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have hno : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro hcon
      have h0 : ((g :: gs).filter (fun gg => decide (gg.op = PEqualNP.CircuitLowerBounds.GateOp.not))).length = 0 := hnot
      have h1 : (g :: gs).filter (fun gg => decide (gg.op = PEqualNP.CircuitLowerBounds.GateOp.not)) = [] :=
        List.length_eq_zero_iff.mp h0
      have h2 : g ∈ (g :: gs).filter (fun gg => decide (gg.op = PEqualNP.CircuitLowerBounds.GateOp.not)) := by
        rw [List.mem_filter]
        exact ⟨List.mem_cons_self, decide_eq_true_eq.mpr hcon⟩
      rw [h1] at h2
      simp at h2
    rcases hop with h | h | h
    · exact cAnd ⟨g :: gs, out⟩ x2 hfan hcard hnot hcomp ⟨g, gs, rfl, h⟩
    · exact cOr ⟨g :: gs, out⟩ x2 hfan hcard hnot hcomp ⟨g, gs, rfl, h⟩
    · exact (hno h).elim
