import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4994_421
    (lower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (15 : ℕ) ≤ x1.size)
    (replayLift : ∀ (n : ℕ) (cols : List (BitVec n)) (i j out : ℕ) (ps : List (Bool × ℕ × ℕ))
      (t : BitVec n), t ≠ 0 → t ≠ BitVec.allOnes n →
      (ps.foldl (fun ws p => ws ++ [if p.1 = Bool.true then ws.getD p.2.1 0 ||| ws.getD p.2.2 0
        else ws.getD p.2.1 0 &&& ws.getD p.2.2 0])
        (0 :: BitVec.allOnes n :: cols ++ [cols.getD i 0 ||| cols.getD j 0])).getD out 0 = t →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ ps.length + 1 ∧
        ∀ r : Fin n, C.eval (cols.map fun w => w.getLsbD r.val) = t.getLsbD r.val) :
    ∀ (x1 : Fin (9 : ℕ)) (x2 : List (Bool × ℕ × ℕ)) (x3 : ℕ),   have x4 : List (BitVec (24 : ℕ)) := [(4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ))];   have x5 : BitVec (24 : ℕ) := x4.getD (0 : ℕ) (0 : BitVec (24 : ℕ)) ||| x4.getD (4 : ℕ) (0 : BitVec (24 : ℕ));   have x6 : List (BitVec (24 : ℕ)) := x4 ++ [x5, x5 ||| x4.getD ↑x1 (0 : BitVec (24 : ℕ))];   (List.foldl (fun (x7 : List (BitVec (24 : ℕ))) (x8 : Bool × ℕ × ℕ) => x7 ++ [if x8.1 = Bool.true then x7.getD x8.2.1 (0 : BitVec (24 : ℕ)) ||| x7.getD x8.2.2 (0 : BitVec (24 : ℕ)) else x7.getD x8.2.1 (0 : BitVec (24 : ℕ)) &&& x7.getD x8.2.2 (0 : BitVec (24 : ℕ))]) ((0 : BitVec (24 : ℕ)) :: BitVec.allOnes (24 : ℕ) :: x6) x2).getD x3 (0 : BitVec (24 : ℕ)) = (3428671 : BitVec (24 : ℕ)) → (14 : ℕ) ≤ x2.length := by
  let W := BitVec 24

  let columns : List W :=
    [4358697,8397251,662022,304212,8980632,1068256,2199296,12709888,16646144]

  let seed : W := columns.getD 0 0 ||| columns.getD 4 0

  let inputCols : List W := columns ++ [seed]

  let masks : List ℕ :=
    [3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402]

  let positives : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320]

  let inputBits (r : ℕ) : List Bool :=
    let f := fun i : Fin 9 => r.testBit i.val
    List.ofFn f ++ [f 0 || f 4]

  have rows : ∀ k : Fin 24,
      (inputCols.map fun w => w.getLsbD k.val) = inputBits (masks.getD k.val 0) ∧
        (3428671 : W).getLsbD k.val = decide (masks.getD k.val 0 ∈ positives) := by decide

  intro j ps out cols z seeds success
  have raw : inputCols.getD j.val 0 = columns.getD j.val 0 := by
    exact List.getD_append _ _ _ _ (by simpa [columns] using j.isLt)
  have stored : inputCols.getD 9 0 = seed := by
    dsimp only [inputCols, columns, seed]
    decide
  have hbase : 0 :: BitVec.allOnes 24 :: inputCols ++ [inputCols.getD 9 0 ||| inputCols.getD j.val 0]
      = 0 :: BitVec.allOnes 24 :: seeds := by
    rw [raw,stored]
    rfl
  obtain ⟨C,hC,sizeC,evalC⟩ := replayLift 24 inputCols 9 j.val out ps 3428671
    (by decide) (by decide) (by rw [hbase]; exact success)
  have known := lower C hC (by
    intro r hr
    change r ∈ masks at hr
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hr
    let f : Fin 24 := ⟨i,by simpa [masks] using hi⟩
    have e : masks.getD f.val 0 = r := by
      rw [List.getD_eq_getElem _ _ hi]
      exact he
    obtain ⟨input, bit⟩ := rows f
    change C.eval (inputBits r) = decide (r ∈ positives)
    rw [← e, ← input, evalC f, bit])
  omega
