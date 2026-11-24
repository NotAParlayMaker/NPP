import PEqualNP.Defs

-- The prefix uses the shared ORs and the explicit three-point branch from R-meta-3531-1.
-- The remaining branch sees thirteen wires and has fourteen gates.
theorem PEqualNP.Outside.R_meta_4602_1
    (four :
      let seed : List (BitVec 59) :=
        [256463372304, 8521482511360, 14003410187716736, 55389823206179104,
         155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864,
         270286071508729856, 288160007409369088, 192860064594267704, 288166778660192704,
         283797140973809664]
      ∃ gs : List (Bool × Fin 40 × Fin 40), gs.length = 14 ∧
        (∀ (j : ℕ) (g : Bool × Fin 40 × Fin 40), gs[j]? = some g →
          g.2.1.val < 13 + j ∧ g.2.2.val < 13 + j) ∧
        (gs.foldl (fun (w : List (BitVec 59)) (g : Bool × Fin 40 × Fin 40) =>
          w ++ [if g.1 then w.getD g.2.1.val 0 ||| w.getD g.2.2.val 0
            else w.getD g.2.1.val 0 &&& w.getD g.2.2.val 0]) seed).getD 26 0 = 1764784)
    (compile :
      let step := fun (w : List (BitVec 59)) (g : Bool × Fin 40 × Fin 40) =>
        w ++ [if g.1 then w.getD g.2.1.val 0 ||| w.getD g.2.2.val 0
          else w.getD g.2.1.val 0 &&& w.getD g.2.2.val 0]
      ∀ (W : List (BitVec 59)) (I : List (Fin 40)) (gs : List (Bool × Fin 40 × Fin 40)),
        W.length + gs.length ≤ 39 →
        (∀ i ∈ I, i.val < W.length) →
        (∀ (j : ℕ) (g : Bool × Fin 40 × Fin 40), gs[j]? = some g →
          g.2.1.val < I.length + j ∧ g.2.2.val < I.length + j) →
        ∃ hs : List (Bool × Fin 40 × Fin 40), hs.length = gs.length ∧
          ∀ j < gs.length, (hs.foldl step W).getD (W.length + j) 0 =
            (gs.foldl step (I.map fun i => W.getD i.val 0)).getD (I.length + j) 0) :
    have x1 : List (BitVec (59 : ℕ)) := [(95229015649944073 : BitVec (59 : ℕ)), (63038587928642 : BitVec (59 : ℕ)), (256463372304 : BitVec (59 : ℕ)), (4292497062825988 : BitVec (59 : ℕ)), (8521482511360 : BitVec (59 : ℕ)), (14003410187716736 : BitVec (59 : ℕ)), (55389823206179104 : BitVec (59 : ℕ)), (189297016294080519 : BitVec (59 : ℕ)), (155696362464215096 : BitVec (59 : ℕ)), (218994303131713984 : BitVec (59 : ℕ)), (183565875465424384 : BitVec (59 : ℕ)), (229736628136996864 : BitVec (59 : ℕ)), (270286071508729856 : BitVec (59 : ℕ)), (288160007409369088 : BitVec (59 : ℕ))]; have x2 : List ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)]; ∃ (x3 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))) (x4 : Fin (39 : ℕ)) (x5 : Fin (39 : ℕ)) (x6 : Fin (16 : ℕ)),   x3.length = (25 : ℕ) ∧     (14 : ℕ) ≤ ↑x4 ∧       x4 < x5 ∧         have x7 : ℕ := x2.getD ↑x6 (0 : ℕ);         have x8 : ℕ := x7 % (64 : ℕ);         have x9 : ℕ := x7 / (64 : ℕ);         have x10 : List (BitVec (59 : ℕ)) := List.foldl (fun (x10 : List (BitVec (59 : ℕ))) (x11 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x10 ++ [if x11.1 = Bool.true then x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) ||| x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ)) else x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) &&& x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ))]) x1 x3;         have x11 : BitVec (59 : ℕ) := x10.getD ↑x4 (0 : BitVec (59 : ℕ));         have x12 : BitVec (59 : ℕ) := x10.getD ↑x5 (0 : BitVec (59 : ℕ));         (if x8 < (21 : ℕ) then x11 ||| x12 else x11 &&& x12) = (2097151 : BitVec (59 : ℕ)) ∧ x11.getLsbD x8 ≠ x12.getLsbD x8 ∧ x11.getLsbD x8 = x12.getLsbD x9 ∧ x12.getLsbD x8 = x11.getLsbD x9 := by
  let initial : List (BitVec 59) :=
    [95229015649944073, 63038587928642, 256463372304, 4292497062825988,
      8521482511360, 14003410187716736, 55389823206179104, 189297016294080519,
      155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864,
      270286071508729856, 288160007409369088]
  let step := fun (w : List (BitVec 59)) (g : Bool × Fin 40 × Fin 40) =>
    w ++ [if g.1 then w.getD g.2.1.val 0 ||| w.getD g.2.2.val 0
      else w.getD g.2.1.val 0 &&& w.getD g.2.2.val 0]
  let pre : List (Bool × Fin 40 × Fin 40) :=
    [(true, 8, 10), (true, 9, 13), (true, 11, 12),
     (true, 7, 14), (false, 0, 17), (true, 7, 15), (false, 1, 19),
     (true, 7, 16), (false, 3, 21), (true, 18, 20), (true, 23, 22)]
  let W := pre.foldl step initial
  let I : List (Fin 40) := [2, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  let seed : List (BitVec 59) :=
    [256463372304, 8521482511360, 14003410187716736, 55389823206179104,
     155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864,
     270286071508729856, 288160007409369088, 192860064594267704, 288166778660192704,
     283797140973809664]
  have lengthW : W.length = 25 := by decide +kernel
  have leftOut : W.getD 24 0 = 332367 := by decide +kernel
  have inputList : I.map (fun i => W.getD i.val 0) = seed := by decide +kernel
  have safe : ∀ i ∈ I, i.val < W.length := by
    intro i hi
    simp only [I, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  obtain ⟨gs, gsLen, edges, output⟩ := four
  have valid : ∀ (j : ℕ) (g : Bool × Fin 40 × Fin 40), gs[j]? = some g →
      g.2.1.val < I.length + j ∧ g.2.2.val < I.length + j := edges
  obtain ⟨hs, hsLen, sim⟩ := compile W I gs (by omega) safe valid
  have rightOut : (hs.foldl step W).getD 38 0 = 1764784 := by
    have eq := sim 13 (by omega)
    rw [lengthW, inputList] at eq
    exact eq.trans output
  have preserved (prg : List (Bool × Fin 40 × Fin 40)) (w : List (BitVec 59))
      (i : ℕ) (lt : i < w.length) : (prg.foldl step w).getD i 0 = w.getD i 0 := by
    induction prg generalizing w with
    | nil => rfl
    | cons g prg ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ lt
  let final := hs.foldl step W
  have leftFinal : final.getD 24 0 = 332367 :=
    (preserved hs W 24 (by omega)).trans leftOut
  refine ⟨pre ++ hs, 24, 38, 1, ?_, by decide, by decide, ?_⟩
  · rw [List.length_append, hsLen, gsLen]
    decide
  · have finalEq : (pre ++ hs).foldl step initial = final := List.foldl_append
    change (((pre ++ hs).foldl step initial).getD 24 0 |||
      ((pre ++ hs).foldl step initial).getD 38 0) = (2097151 : BitVec 59) ∧
      (((pre ++ hs).foldl step initial).getD 24 0).getLsbD 0 ≠
        (((pre ++ hs).foldl step initial).getD 38 0).getLsbD 0 ∧
      (((pre ++ hs).foldl step initial).getD 24 0).getLsbD 0 =
        (((pre ++ hs).foldl step initial).getD 38 0).getLsbD 4 ∧
      (((pre ++ hs).foldl step initial).getD 38 0).getLsbD 0 =
        (((pre ++ hs).foldl step initial).getD 24 0).getLsbD 4
    rw [finalEq, leftFinal]
    change (332367 ||| final.getD 38 0) = (2097151 : BitVec 59) ∧ _
    have v : final.getD 38 0 = (1764784 : BitVec 59) := rightOut
    rw [v]
    decide +kernel
