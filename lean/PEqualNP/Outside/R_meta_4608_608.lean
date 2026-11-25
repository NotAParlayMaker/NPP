import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

-- Ordinary pairs use the two-element support bound. For a pin reading wire 9,
-- split on the number of NOTs: test rows, the one/two-NOT bound, or the
-- binary-gate bound after restoring the two ORs (as in R-meta-2843-631).
theorem PEqualNP.Outside.R_meta_4608_608
    (rawPair : ∀ (C : Circuit) (S : Finset (Fin 9)), FanInTwo C → S.card ≤ 2 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ v ∈ S, x v = true)]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → 14 ≤ C.size)
    (monotoneRows : ∀ (v : Fin 9) (D : Circuit), Monotone2 D →
      (∀ r ∈ ([3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402] : List ℕ),
        let x : Fin 9 → Bool := fun i => r.testBit i.val
        D.eval (List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x v]) =
          decide (r ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ))) →
      14 ≤ D.size)
    (signedBound : ∀ (C : Circuit) (a : Fin 9), FanInTwo C →
      1 ≤ notCount C → notCount C ≤ 2 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x a]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      14 ≤ C.size)
    (binaryBound : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      13 ≤ C.size - notCount C) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2 < x3 →       ¬(x2 = (0 : Fin (10 : ℕ)) ∧ x3 = (4 : Fin (10 : ℕ))) →         ¬((x2 = (0 : Fin (10 : ℕ)) ∨ x2 = (4 : Fin (10 : ℕ))) ∧ x3 = (9 : Fin (10 : ℕ))) →           ¬(x2 = (4 : Fin (10 : ℕ)) ∧ x3 ∈ [(6 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))] ∨ x3 = (4 : Fin (10 : ℕ)) ∧ x2 ∈ [(2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))]) →             (∀ (x9 : Fin (9 : ℕ) → Bool),                 have x10 : List Bool := List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ))];                 x1.eval (x10 ++ [x10.getD (↑x2) Bool.false || x10.getD (↑x3) Bool.false]) = (fun (x11 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x12 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x11 x12.1 && x11 x12.2) x9) →               (14 : ℕ) ≤ x1.size := by
  intro C i j legal lt _ _ _ computes
  let f : (Fin 9 → Bool) → Bool := fun x => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  have readRaw (x : Fin 9 → Bool) (a : Fin 9) : (base x).getD a.val false = x a := by
    have h : a.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using a.isLt
    rw [show base x = List.ofFn x ++ [x 0 || x 4] from rfl, List.getD_append _ _ _ _ h,
      List.getD_eq_getElem _ _ h, List.getElem_ofFn]
  have hi : i.val < 9 := by have := j.isLt; change i.val < j.val at lt; omega
  let a : Fin 9 := ⟨i.val, hi⟩
  by_cases hj : j.val < 9
  · let b : Fin 9 := ⟨j.val, hj⟩
    apply rawPair C {a,b} legal Finset.card_le_two
    intro x
    have h := computes x
    change C.eval (base x ++ [(base x).getD a.val false || (base x).getD b.val false]) = f x at h
    rw [readRaw, readRaw] at h
    have e : decide (∃ v ∈ ({a,b} : Finset (Fin 9)), x v = true) = (x a || x b) := by
      simp
    rw [e]
    simpa only [base, List.append_assoc, List.singleton_append] using h
  have j9 : j.val = 9 := by have := j.isLt; omega
  have correct (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x a]) = f x := by
    have h := computes x
    change C.eval (base x ++ [(base x).getD a.val false || (base x).getD j.val false]) = f x at h
    have last : (base x).getD 9 false = (x 0 || x 4) := by simp [base, List.getD]
    rw [j9, last, readRaw, Bool.or_comm (x a)] at h
    simpa only [base, List.append_assoc, List.singleton_append] using h
  by_cases zero : notCount C = 0
  · have mono : Monotone2 C := by
      intro g hg
      have no : g.op ≠ GateOp.not := by
        intro e
        have mem : g ∈ C.gates.filter (fun t : Gate =>
            @decide (t.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) :=
          List.mem_filter.mpr ⟨hg, by simp [e]⟩
        have nil := List.eq_nil_of_length_eq_zero zero
        rw [nil] at mem
        exact List.not_mem_nil mem
      have hf := legal g hg
      rcases hf.1 with ha | ho | hn
      · exact ⟨Or.inl ha, hf.2⟩
      · exact ⟨Or.inr ho, hf.2⟩
      · exact (no hn).elim
    apply monotoneRows a C mono
    intro r hr
    dsimp only
    rw [correct]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  by_cases low : notCount C ≤ 2
  · exact signedBound C a legal (by omega) low correct
  let first : Gate := ⟨.or, [0, 4]⟩
  let second : Gate := ⟨.or, [9, a.val]⟩
  let D : Circuit := ⟨first :: second :: C.gates, C.output⟩
  have legalD : FanInTwo D := by
    intro g hg
    change g ∈ first :: second :: C.gates at hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp [first]
    · simp [second]
    · exact legal g hg
  have value (x : Fin 9 → Bool) :
      D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x a]) := by
    let evalGate (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have firstValue : evalGate (List.ofFn x) first = List.ofFn x ++ [x 0 || x 4] := by
      let w := List.ofFn x
      change w ++ [([w.getD 0 false, w.getD 4 false].any id)] = _
      simp [w, List.getD_eq_getElem?_getD]
    have anchor : (List.ofFn x ++ [x 0 || x 4]).getD 9 false = (x 0 || x 4) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
    have input : (List.ofFn x ++ [x 0 || x 4]).getD a.val false = x a := by
      have within : a.val < (List.ofFn x).length := by simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left within]
      rw [List.getElem?_eq_getElem within, List.getElem_ofFn]
      rfl
    have secondValue : evalGate (List.ofFn x ++ [x 0 || x 4]) second =
        List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x a] := by
      let w := List.ofFn x ++ [x 0 || x 4]
      change w ++ [([w.getD 9 false, w.getD a.val false].any id)] = _
      rw [show w.getD 9 false = (x 0 || x 4) from anchor,
          show w.getD a.val false = x a from input]
      simp only [w, List.any_cons, List.any_nil, id_eq, Bool.or_false,
        List.append_assoc, List.singleton_append]
    change (C.gates.foldl evalGate (evalGate (evalGate (List.ofFn x) first) second)).getD
      C.output false = (C.gates.foldl evalGate _).getD C.output false
    rw [firstValue, secondValue]
  have count := binaryBound D legalD (fun x => (value x).trans (correct x))
  have size : D.size = C.size + 2 := by
    change (first :: second :: C.gates).length = C.gates.length + 2
    simp
  have nots : notCount D = notCount C := by
    change (List.filter (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _))
      (first :: second :: C.gates)).length = _
    change _ = (List.filter (fun g : Gate =>
      @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) C.gates).length
    simp [first, second]
  rw [size, nots] at count
  omega
