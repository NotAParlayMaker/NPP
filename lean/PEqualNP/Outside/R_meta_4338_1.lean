import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4338_1
    (case_4 :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 4]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (many_nots :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
        13 ≤ C.size - PEqualNP.NotBracket.notCount C)
    (case_0_not0 :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
        PEqualNP.NotBracket.notCount C = 0 →
        (∀ g ∈ C.gates, (∀ j ∈ g.inputs, j < 9) → g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (case_0_not1 :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
        PEqualNP.NotBracket.notCount C = 1 →
        (∀ g ∈ C.gates, (∀ j ∈ g.inputs, j < 9) → g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ x1 ∈ [(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x7 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x7 ++ [!x7 x1]) ≠ (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7 := by
  classical
  intro a ha C hfan hsz hnoand
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · by_cases h0 : PEqualNP.NotBracket.notCount C = 0
    · exact case_0_not0 C hfan hsz h0 hnoand
    · by_cases h1 : PEqualNP.NotBracket.notCount C = 1
      · exact case_0_not1 C hfan hsz h1 hnoand
      · by_contra hno
        have heq : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) =
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
          intro x; by_contra hne; exact hno ⟨x, hne⟩
        let g0 : Gate := ⟨.not, [0]⟩
        let full : Circuit := ⟨g0 :: C.gates, C.output⟩
        have hfull_fan : FanInTwo full := by
          intro g hg
          rcases List.mem_cons.mp hg with rfl | hg'
          · exact ⟨Or.inr (Or.inr rfl), by decide⟩
          · exact hfan g hg'
        have hfull_eval : ∀ x : Fin 9 → Bool, full.eval (List.ofFn x) =
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
          intro x
          let step (w : List Bool) (g : Gate) : List Bool :=
            w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
          have hs0 : step (List.ofFn x) g0 = List.ofFn x ++ [!x 0] := by
            change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = List.ofFn x ++ [!x 0]
            have hget0 : (List.ofFn x).getD 0 false = x 0 := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
              simp only [Nat.zero_lt_succ, ↓reduceDIte, Option.getD_some]; rfl
            rw [hget0]
          change ((g0 :: C.gates).foldl step (List.ofFn x)).getD C.output false = _
          rw [List.foldl_cons, hs0]
          exact heq x
        have h13 := many_nots full hfull_fan hfull_eval
        have hfsz : full.size = 1 + C.size := by
          change (g0 :: C.gates).length = 1 + C.gates.length
          simp only [List.length_cons]; omega
        have hfnot : PEqualNP.NotBracket.notCount full = 1 + PEqualNP.NotBracket.notCount C := by
          unfold PEqualNP.NotBracket.notCount
          dsimp only [full, g0]
          rw [List.filter_cons_of_pos (by decide), List.length_cons]
          omega
        rw [hfsz, hfnot] at h13
        omega
  · exact case_4 C hfan hsz
