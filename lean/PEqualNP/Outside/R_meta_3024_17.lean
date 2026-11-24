import Mathlib
import PEqualNP.Defs

-- Cut on whether the circuit uses the extra NOT wire (wire 10). If it does not, the
-- circuit is a 13 gate circuit on x and x0 or x2, so unused follows from L_meta_2012.
theorem PEqualNP.Outside.R_meta_3024_17
    (unused : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ 13 → D.output ≠ 10 → (∀ g ∈ D.gates, 10 ∉ g.inputs) →
      ∀ y : (Fin 9 → Bool) → Bool, ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 2, y x]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
            (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
            (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (used : ∀ i : Fin 11, ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      (D.output = 10 ∨ ∃ g ∈ D.gates, 10 ∈ g.inputs) → ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 2, !((List.ofFn x ++ [x 0 || x 2]).getD i.val false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
            (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
            (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : List (Fin (11 : ℕ))), x1.length ≤ (2 : ℕ) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];
          x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval
            (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠
            (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
             x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
             x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
             x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
             x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
             x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
             x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
             x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
             x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
             x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
             x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
             x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins _ C fan size
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 2]
  have notHead (x : Fin 9 → Bool) : PEqualNP.CircuitLowerBounds.GateOp.not.eval
      (pins.map fun i => (seed x).getD i.val false) =
      !((seed x).getD (pins.headD 10).val false) := by
    cases pins with
    | nil =>
      change true = !((seed x).getD 10 false)
      rw [List.getD_eq_default _ _ (by simp [seed])]
      rfl
    | cons i rest => rfl
  by_cases h : C.output = 10 ∨ ∃ g ∈ C.gates, 10 ∈ g.inputs
  · obtain ⟨x, hx⟩ := used (pins.headD 10) C fan size h
    refine ⟨x, ?_⟩
    have e := notHead x
    simp only [seed] at e
    simpa only [List.append_assoc, List.cons_append, List.nil_append, e, Bool.or_assoc] using hx
  · push_neg at h
    obtain ⟨x, hx⟩ := unused C fan size h.1 (fun g hg => h.2 g hg)
      (fun x => PEqualNP.CircuitLowerBounds.GateOp.not.eval
        (pins.map fun i => (seed x).getD i.val false))
    refine ⟨x, ?_⟩
    simpa only [seed, List.append_assoc, List.cons_append, List.nil_append, Bool.or_assoc] using hx
