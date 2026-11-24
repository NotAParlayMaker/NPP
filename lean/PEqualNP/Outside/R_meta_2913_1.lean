import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_2913_1
    (binaryBound :
      let f := fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      ∀ C : Circuit, FanInTwo C → (∀ x, C.eval (List.ofFn x) = f x) →
        13 ≤ C.size - notCount C)
    (monotoneBound :
      let f := fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      ∀ (C : Circuit) (mode : Fin 3), Monotone2 C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++
          [!x 0, if mode = 0 then true else if mode = 1 then !x 0 else x 0]) ≠ f x) :
∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     x1 = [] ∨ x1.headD (10 : ℕ) = (0 : ℕ) ∨ (9 : ℕ) ≤ x1.headD (10 : ℕ) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro ins lengthIns allowed C legal limit
  by_contra! computes
  simp only [not_not] at computes
  let first : Gate := ⟨.not, [0]⟩
  let second : Gate := ⟨.not, ins⟩
  let D : Circuit := ⟨first :: second :: C.gates, C.output⟩
  let row := fun x : Fin 9 → Bool => List.ofFn x ++ [!x 0]
  have legalD : FanInTwo D := by
    intro g hg
    change g ∈ first :: second :: C.gates at hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp [first]
    · exact ⟨by simp [second], lengthIns⟩
    · exact legal g hg
  have correctD (x : Fin 9 → Bool) :
      D.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 ||
        x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 ||
        x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have firstValue : step (List.ofFn x) first = row x := by
      simp [step, first, row, GateOp.eval, List.getD_eq_getElem?_getD]
    change (C.gates.foldl step (step (step (List.ofFn x) first) second)).getD C.output false = _
    rw [firstValue]
    exact computes x
  have cost := binaryBound D legalD correctD
  have count : notCount D = notCount C + 2 := by simp [notCount, D, first, second]
  have size : D.size = C.size + 2 := by simp [D, Circuit.size]
  have zero : notCount C = 0 := by
    rw [size, count] at cost
    omega
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨op, n⟩ := legal g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
    rcases op with h | h | h
    · exact ⟨by simp [h], n⟩
    · exact ⟨by simp [h], n⟩
    · have member : g ∈ C.gates.filter (fun v : Gate =>
          @decide (v.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) :=
        List.mem_filter.mpr ⟨hg, by simp [h]⟩
      have none : C.gates.filter (fun v : Gate =>
          @decide (v.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) = [] :=
        List.eq_nil_of_length_eq_zero zero
      rw [none] at member
      exact (List.not_mem_nil member).elim
  have casesOfSeed : ∃ mode : Fin 3, ∀ x : Fin 9 → Bool,
      GateOp.not.eval (ins.map fun i => (row x).getD i false) =
        (if mode = 0 then true else if mode = 1 then !x 0 else x 0) := by
    cases ins with
    | nil => exact ⟨0, fun _ => rfl⟩
    | cons a more =>
      have atZeroOrAbove : a = 0 ∨ 9 ≤ a := by simpa using allowed
      rcases atZeroOrAbove with rfl | above
      · refine ⟨1, ?_⟩
        intro x
        simp [row, GateOp.eval, List.getD_eq_getElem?_getD]
      · by_cases atNine : a = 9
        · subst a
          refine ⟨2, ?_⟩
          intro x
          have ap : (row x).getD 9 false = !x 0 := by
            change (List.ofFn x ++ [!x 0]).getD 9 false = _
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
            simp
          change (!((row x).getD 9 false)) = x 0
          rw [ap]
          simp
        · refine ⟨0, ?_⟩
          intro x
          have beyond : (row x).length ≤ a := by simp [row]; omega
          have ap : (row x).getD a false = false := List.getD_eq_default _ _ beyond
          change (!((row x).getD a false)) = true
          rw [ap]
          rfl
  obtain ⟨mode, modeEq⟩ := casesOfSeed
  obtain ⟨x, mismatch⟩ := monotoneBound C mode mono limit
  have eq := computes x
  change C.eval (row x ++ [GateOp.not.eval (ins.map fun i => (row x).getD i false)]) = _ at eq
  rw [modeEq] at eq
  exact mismatch (by simpa only [row, List.append_assoc, List.singleton_append] using eq)
