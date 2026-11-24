import PEqualNP.Defs

-- Reduction for L-meta-2498: split on the operation of the second gate.
-- If the second gate is an AND gate, an OR gate, or a NOT gate, the bound follows;
-- those are the only operations a fan-in-two circuit can use, and circuits with
-- fewer than two gates are ruled out directly by the first-gate condition and
-- the edge function.
theorem PEqualNP.Outside.R_meta_2498_1
    (h_and : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x1.gates[1]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (16 : ℕ) ≤ x1.size)
    (h_or : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x1.gates[1]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (16 : ℕ) ≤ x1.size)
    (h_not : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x1.gates[1]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → (16 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (16 : ℕ) ≤ x1.size := by
  intro x1 hfan hfirst hfun hinv
  have hcf : ∀ x : Fin 9 → Bool, (x1.wires (List.ofFn x)).getD x1.output false =
      [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any (fun x5 => x x5.1 && x x5.2) := fun x => congrFun hfun x
  cases hg : x1.gates with
  | nil =>
    exfalso
    have h := hfirst (fun j : Fin 9 => decide (j.val = 0))
    have hw : x1.wires (List.ofFn (fun j : Fin 9 => decide (j.val = 0))) =
        List.ofFn (fun j : Fin 9 => decide (j.val = 0)) := by
      simp [PEqualNP.CircuitLowerBounds.Circuit.wires, hg]
    rw [hw] at h
    exact (by decide : ¬ ((List.ofFn (fun j : Fin 9 => decide (j.val = 0))).getD 9 false =
      ((fun j : Fin 9 => decide (j.val = 0)) 0 || (fun j : Fin 9 => decide (j.val = 0)) 1))) h
  | cons g0 gs =>
    cases hg' : gs with
    | nil =>
      exfalso
      have hw : ∀ x : Fin 9 → Bool, x1.wires (List.ofFn x) =
          List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)] := by
        intro x
        simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, hg, hg', List.foldl_cons,
          List.foldl_nil]
      by_cases ho9 : x1.output = 9
      · have h1 := hcf (fun j : Fin 9 => decide (j.val = 2 ∨ j.val = 3))
        rw [ho9] at h1
        have h9 := hfirst (fun j : Fin 9 => decide (j.val = 2 ∨ j.val = 3))
        rw [h9] at h1
        exact (by decide : ¬ (((fun j : Fin 9 => decide (j.val = 2 ∨ j.val = 3)) 0 ||
          (fun j : Fin 9 => decide (j.val = 2 ∨ j.val = 3)) 1) =
          [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any (fun x5 => (fun j : Fin 9 => decide (j.val = 2 ∨ j.val = 3)) x5.1 &&
            (fun j : Fin 9 => decide (j.val = 2 ∨ j.val = 3)) x5.2))) h1
      · by_cases holt : x1.output < 9
        · have key : ∀ ex : Fin 9 → Bool,
            (x1.wires (List.ofFn ex)).getD x1.output false = ex ⟨x1.output, holt⟩ := by
            intro ex
            rw [hw ex, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by simpa using holt), List.getElem?_ofFn]
            simp [holt]
          by_cases h2 : x1.output = 2
          · have h1 := hcf (fun j : Fin 9 => decide (j.val = 0 ∨ j.val = 1))
            rw [key] at h1
            have hL : decide ((⟨x1.output, holt⟩ : Fin 9).val = 0 ∨
                (⟨x1.output, holt⟩ : Fin 9).val = 1) = false := by
              show decide (x1.output = 0 ∨ x1.output = 1) = false
              rw [decide_eq_false_iff_not]
              rintro (r | r) <;> omega
            have hR : [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any (fun x5 => decide (x5.1.val = 0 ∨ x5.1.val = 1) &&
                decide (x5.2.val = 0 ∨ x5.2.val = 1)) = true := by
              decide
            rw [hL, hR] at h1
            exact Bool.false_ne_true h1
          · by_cases h3 : x1.output = 3
            · have h1 := hcf (fun j : Fin 9 => decide (j.val = 0 ∨ j.val = 1))
              rw [key] at h1
              have hL : decide ((⟨x1.output, holt⟩ : Fin 9).val = 0 ∨
                  (⟨x1.output, holt⟩ : Fin 9).val = 1) = false := by
                show decide (x1.output = 0 ∨ x1.output = 1) = false
                rw [decide_eq_false_iff_not]
                rintro (r | r) <;> omega
              have hR : [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any (fun x5 => decide (x5.1.val = 0 ∨ x5.1.val = 1) &&
                  decide (x5.2.val = 0 ∨ x5.2.val = 1)) = true := by
                decide
              rw [hL, hR] at h1
              exact Bool.false_ne_true h1
            · have h1 := hcf (fun j : Fin 9 => decide (j.val = 2 ∨ j.val = 3))
              rw [key] at h1
              have hL : decide ((⟨x1.output, holt⟩ : Fin 9).val = 2 ∨
                  (⟨x1.output, holt⟩ : Fin 9).val = 3) = false := by
                show decide (x1.output = 2 ∨ x1.output = 3) = false
                rw [decide_eq_false_iff_not]
                rintro (r | r)
                · exact h2 r
                · exact h3 r
              have hR : [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any (fun x5 => decide (x5.1.val = 2 ∨ x5.1.val = 3) &&
                  decide (x5.2.val = 2 ∨ x5.2.val = 3)) = true := by
                decide
              rw [hL, hR] at h1
              exact Bool.false_ne_true h1
        · have hgt : 9 < x1.output := by omega
          have h1 := hcf (fun j : Fin 9 => decide (j.val = 0 ∨ j.val = 1))
          have hL : (x1.wires (List.ofFn (fun j : Fin 9 => decide (j.val = 0 ∨ j.val = 1)))).getD
              x1.output false = false := by
            have hlen : (x1.wires (List.ofFn (fun j : Fin 9 => decide (j.val = 0 ∨ j.val = 1)))).length
                = 10 := by
              rw [hw]
              simp
            have hn : (x1.wires (List.ofFn (fun j : Fin 9 => decide (j.val = 0 ∨ j.val = 1))))[x1.output]?
                = none :=
              List.getElem?_eq_none_iff.mpr (by omega)
            simp only [List.getD_eq_getElem?_getD, hn, Option.getD_none]
          have hR : [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any (fun x5 => decide (x5.1.val = 0 ∨ x5.1.val = 1) &&
              decide (x5.2.val = 0 ∨ x5.2.val = 1)) = true := by
            decide
          rw [hL, hR] at h1
          exact Bool.false_ne_true h1
    | cons g1 gs' =>
      have hg1 : x1.gates[1]? = some g1 := by
        rw [hg, hg']; rfl
      have hmem : g1 ∈ x1.gates := by
        rw [hg, hg']
        exact List.mem_cons_of_mem g0 List.mem_cons_self
      obtain ⟨hop, _⟩ := hfan g1 hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h | h
      · exact h_and x1 hfan hfirst hfun hinv ⟨g1, hg1, h⟩
      · exact h_or x1 hfan hfirst hfun hinv ⟨g1, hg1, h⟩
      · exact h_not x1 hfan hfirst hfun hinv ⟨g1, hg1, h⟩
