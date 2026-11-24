import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3392_1
    (base : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [Bool.false]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (15 : ℕ) ≤ x1.size)
    (near : ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [x6 (4 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (far : ∀ x1 ∈ [(3 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [x6 (4 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [x6 (4 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro v hv C hC hsmall
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact near _ (List.mem_cons_self ..) C hC hsmall
  · exact near _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) C hC hsmall
  · exact far _ (List.mem_cons_self ..) C hC hsmall
  · by_contra h
    have he := fun x => not_ne_iff.mp (not_exists.mp h x)
    let reindex (i : ℕ) : ℕ := if i = 9 then 10 else if i = 10 then 4 else i
    let translate (g : Gate) : Gate := ⟨g.op, g.inputs.map reindex⟩
    let first : Gate := ⟨.not, [0]⟩
    let D : Circuit := ⟨first :: C.gates.map translate, reindex C.output⟩
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have readAppend (w : List Bool) (a : Bool) (i : ℕ) :
        (w ++ [a]).getD i false =
          if i < w.length then w.getD i false else if i = w.length then a else false := by
      by_cases hlt : i < w.length
      · rw [if_pos hlt, List.getD_append _ _ _ _ hlt]
      · by_cases heq : i = w.length
        · subst i
          rw [if_neg (Nat.lt_irrefl _), if_pos rfl, List.getD_eq_getElem _ _ (by simp)]
          rw [List.getElem_append_right le_rfl]
          simp
        · rw [if_neg hlt, if_neg heq, List.getD_eq_default _ _ (by simp; omega)]
    have simulate (gs : List Gate) (a b : List Bool) (hl : a.length = b.length)
        (h11 : 11 ≤ b.length) (eq : ∀ i, a.getD i false = b.getD (reindex i) false) :
        ∀ i, (gs.foldl step a).getD i false =
          ((gs.map translate).foldl step b).getD (reindex i) false := by
      induction gs generalizing a b with
      | nil => exact eq
      | cons g gs ih =>
        apply ih (step a g) (step b (translate g)) (by simp [step, hl]) (by simp [step]; omega)
        intro i
        have value : g.op.eval (g.inputs.map fun j => a.getD j false) =
            (translate g).op.eval ((translate g).inputs.map fun j => b.getD j false) := by
          simp only [translate, List.map_map, eq]
          rfl
        have hi : i < a.length ↔ reindex i < b.length := by
          by_cases h9 : i = 9
          · subst i
            simp [reindex, (show 9 < a.length by omega), (show 10 < b.length by omega)]
          by_cases h10 : i = 10
          · subst i
            simp [reindex, (show 10 < a.length by omega), (show 4 < b.length by omega)]
          simp [reindex, h9, h10, hl]
        have hj : i = a.length ↔ reindex i = b.length := by
          by_cases h9 : i = 9
          · subst i
            simp [reindex, (show 9 ≠ a.length by omega), (show 10 ≠ b.length by omega)]
          by_cases h10 : i = 10
          · subst i
            simp [reindex, (show 10 ≠ a.length by omega), (show 4 ≠ b.length by omega)]
          simp [reindex, h9, h10, hl]
        simp only [step, readAppend]
        simp only [← hi, ← hj]
        rw [value, eq i]
    have inputs (x : Fin 9 → Bool) (i : ℕ) :
        (List.ofFn x ++ [!x 0] ++ [x 4 || x 4]).getD i false =
          (step (List.ofFn x ++ [false]) first).getD (reindex i) false := by
      have zeroRead : (List.ofFn x ++ [false]).getD 0 false = x 0 := by
        rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        rfl
      have firstValue : step (List.ofFn x ++ [false]) first =
          List.ofFn x ++ [false] ++ [!x 0] := by
        change List.ofFn x ++ [false] ++ [!((List.ofFn x ++ [false]).getD 0 false)] = _
        rw [zeroRead]
      rw [firstValue]
      by_cases h9 : i = 9
      · subst i
        simp only [reindex, if_pos rfl]
        rw [readAppend, readAppend]
        simp [List.length_ofFn, readAppend]
      by_cases h10 : i = 10
      · subst i
        simp only [reindex, if_neg h9, if_pos rfl]
        rw [readAppend, readAppend]
        simp [List.length_ofFn, readAppend, List.getD_eq_getElem]
      by_cases hi : i < 9
      · simp only [reindex, if_neg h9, if_neg h10]
        rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
          List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
      · simp only [reindex, if_neg h9, if_neg h10]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hD : FanInTwo D := by
      intro g hg
      change g ∈ first :: C.gates.map translate at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · change GateOp.not ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ [0].length ≤ 2
        simp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
        simpa only [translate, List.length_map] using hC q hq
    have hEval (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [false]) =
          C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x 4]) := by
      exact (simulate C.gates _ _ (by simp [step]) (by simp [step]) (inputs x) C.output).symm
    have hl := base D hD (fun x => (hEval x).trans (he x))
    have hs : D.size = C.size + 1 := by
      change (first :: C.gates.map translate).length = C.gates.length + 1
      rw [List.length_cons, List.length_map]
    omega
  · exact far _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) C hC hsmall
