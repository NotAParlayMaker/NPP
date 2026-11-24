import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

-- The binary-gate bound charges the two supplied gates and leaves room for
-- at most one further negation. The two search problems fix that count.
theorem PEqualNP.Outside.R_meta_3863_1
    (binaryBudget : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      13 ≤ C.size - notCount C)
    (noNot : ∀ (p : Fin 9), p ∈ ([2,3,6] : List (Fin 9)) →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → notCount C = 0 →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 0 || x p]) ≠
          ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
            List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
    (oneNot : ∀ (p : Fin 9), p ∈ ([2,3,6] : List (Fin 9)) →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → notCount C = 1 →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 0 || x p]) ≠
          ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
            List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) :
  ∀ (x1 : List ℕ),   x1 = [(0 : ℕ), (2 : ℕ)] ∨ x1 = [(0 : ℕ), (3 : ℕ)] ∨ x1 = [(0 : ℕ), (6 : ℕ)] →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins allowed C fan size
  let target (x : Fin 9 → Bool) : Bool :=
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let initial (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  have originalInput (x : Fin 9 → Bool) (i : Fin 9) :
      (List.ofFn x).getD i.val false = x i := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  have initialInput (x : Fin 9 → Bool) (i : Fin 9) :
      (initial x).getD i.val false = x i := by
    have hi : i.val < (List.ofFn x).length := by simp
    simpa only [initial, List.getD_eq_getElem?_getD, List.getElem?_append_left hi] using originalInput x i
  have extra (x : Fin 9 → Bool) (p : Fin 9) :
      GateOp.or.eval ([0, p.val].map (fun i => (initial x).getD i false)) = (x 0 || x p) := by
    simp only [List.map_cons, List.map_nil]
    rw [show (initial x).getD 0 false = x 0 from initialInput x 0, initialInput x p]
    cases x 0 <;> cases x p <;> rfl
  have pinCase (p : Fin 9) (hp : p ∈ ([2,3,6] : List (Fin 9))) :
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 0 || x p]) ≠ target x := by
    by_contra! correct
    let negation : Gate := ⟨GateOp.not, [0]⟩
    let disjunction : Gate := ⟨GateOp.or, [0, p.val]⟩
    let D : Circuit := ⟨negation :: disjunction :: C.gates, C.output⟩
    have negEval (x : Fin 9 → Bool) :
        negation.op.eval (negation.inputs.map (fun i => (List.ofFn x).getD i false)) = !x 0 := by
      change (!((List.ofFn x).getD 0 false)) = !x 0
      rw [show (List.ofFn x).getD 0 false = x 0 from originalInput x 0]
    have computes (x : Fin 9 → Bool) : D.eval (List.ofFn x) = target x := by
      let w := List.ofFn x ++
        [negation.op.eval (negation.inputs.map fun i => (List.ofFn x).getD i false)]
      change C.eval (w ++ [disjunction.op.eval (disjunction.inputs.map fun i => w.getD i false)]) = target x
      dsimp only [w]
      rw [negEval x]
      change C.eval (initial x ++
        [GateOp.or.eval ([0, p.val].map (fun i => (initial x).getD i false))]) = target x
      rw [extra x p]
      exact correct x
    have fanD : FanInTwo D := by
      intro g hg
      change g ∈ negation :: disjunction :: C.gates at hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · simp [negation]
      · simp [disjunction]
      · exact fan g hg
    have sizeD : D.size = C.size + 2 := rfl
    have countD : notCount D = notCount C + 1 := by
      letI : DecidableEq GateOp := lineDegreeGateOpDecEq
      change ((negation :: disjunction :: C.gates).filter
        (fun g => decide (g.op = GateOp.not))).length =
          (C.gates.filter (fun g => decide (g.op = GateOp.not))).length + 1
      rw [List.filter_cons, List.filter_cons]
      rfl
    have lower := binaryBudget D fanD computes
    rw [sizeD, countD] at lower
    have few : notCount C ≤ 1 := by omega
    by_cases hzero : notCount C = 0
    · obtain ⟨x, hx⟩ := noNot p hp C fan size hzero
      exact hx (correct x)
    · have hone : notCount C = 1 := by omega
      obtain ⟨x, hx⟩ := oneNot p hp C fan size hone
      exact hx (correct x)
  have finish (p : Fin 9) (hp : p ∈ ([2,3,6] : List (Fin 9))) :
      ∃ x : Fin 9 → Bool,
        C.eval (initial x ++ [GateOp.or.eval ([0, p.val].map (fun i => (initial x).getD i false))])
          ≠ target x := by
    obtain ⟨x, hx⟩ := pinCase p hp
    refine ⟨x, ?_⟩
    rw [extra x p]
    exact hx
  have targetFormula (x : Fin 9 → Bool) : target x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) := by
    simp only [target, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  rcases allowed with rfl | rfl | rfl
  · obtain ⟨x, hx⟩ := finish 2 (by simp)
    refine ⟨x, ?_⟩
    dsimp only
    rw [← targetFormula x]
    exact hx
  · obtain ⟨x, hx⟩ := finish 3 (by simp)
    refine ⟨x, ?_⟩
    dsimp only
    rw [← targetFormula x]
    exact hx
  · obtain ⟨x, hx⟩ := finish 6 (by simp)
    refine ⟨x, ?_⟩
    dsimp only
    rw [← targetFormula x]
    exact hx
