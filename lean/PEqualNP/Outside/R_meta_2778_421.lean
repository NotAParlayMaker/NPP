import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The independent lower-bound proof for the boundary rows is L-meta-1922, accepted in PR #5566.
-- The masks denote the 24 boundary evaluations of these same ten input wires.
theorem PEqualNP.Outside.R_meta_2778_421
    (compile : ∀ (n : ℕ) (A S : List (BitVec n)) (goal : BitVec n),
      let base := (0 : BitVec n) :: BitVec.allOnes n :: A
      goal ≠ 0 → goal ≠ BitVec.allOnes n →
      (∀ (j : ℕ) (hj : j < S.length),
        S[j] ∉ base ++ S.take j ∧
        ∃ a ∈ base ++ S.take j, ∃ b ∈ base ++ S.take j,
          S[j] = a &&& b ∨ S[j] = a ||| b) →
      goal ∈ base ++ S →
      ∃ C : Circuit, C.size = S.length ∧ Monotone2 C ∧
        ∀ k : ℕ, C.eval (A.map (fun u => u.getLsbD k)) = goal.getLsbD k)
    (bound : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (15 : ℕ) ≤ x1.size) :
    have x1 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))]; ∀ (x2 : List (BitVec (24 : ℕ))), x2.length ≤ (14 : ℕ) → (∀ (x4 : ℕ) (x5 : x4 < x2.length), x2[x4] ∉ x1 ++ List.take x4 x2 ∧ ∃ x6 ∈ x1 ++ List.take x4 x2, ∃ x7 ∈ x1 ++ List.take x4 x2, x2[x4] = x6 &&& x7 ∨ x2[x4] = x6 ||| x7) → (3428671 : BitVec (24 : ℕ)) ∉ x1 ++ x2 := by
  let A : List (BitVec 24) := [4358697,8397251,662022,304212,8980632,1068256,
    2199296,12709888,16646144,13339321]
  let rows : List ℕ := [3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,
    208,261,264,276,288,320,385,402]
  let pos : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320]
  have rowData : ∀ k : Fin 24,
      let r := rows.getD k.val 0
      let x : Fin 9 → Bool := fun i => r.testBit i.val
      A.map (fun u => u.getLsbD k.val) = List.ofFn x ++ [x 0 || x 4] ∧
      (3428671 : BitVec 24).getLsbD k.val = decide (r ∈ pos) := by
    dsimp only [A, rows, pos]
    decide +kernel
  intro _ S small valid seen
  obtain ⟨C,hSize,hMono,hEval⟩ :=
    compile 24 A S (3428671 : BitVec 24) (by decide) (by decide) valid seen
  have rowBound : ∀ r ∈ rows,
      let x : Fin 9 → Bool := fun i => r.testBit i.val
      C.eval (List.ofFn x ++ [x 0 || x 4]) = decide (r ∈ pos) := by
    intro r hr
    obtain ⟨k,hk,hget⟩ := List.mem_iff_getElem.mp hr
    let j : Fin 24 := ⟨k, by simpa [rows] using hk⟩
    have atRow : rows.getD j.val 0 = r := (List.getD_eq_getElem _ _ hk).trans hget
    have pair := rowData j
    dsimp only at pair ⊢
    rw [atRow] at pair
    rw [← pair.1, hEval j.val, pair.2]
  have h := bound C hMono rowBound
  omega
