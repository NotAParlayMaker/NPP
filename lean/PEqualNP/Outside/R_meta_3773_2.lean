import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3773_2
    (affineCore :
      let pt := fun i : ℕ => if i < 5 then i else if i < 8 then i + 1 else 11
      let ln := fun j : ℕ => if j < 4 then j else j + 1
      let aff := fun y : Fin 21 → Bool =>
        ∃ (i : Fin 9) (j : Fin 12), (pt i.val + ln j.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
          y (Fin.castAdd 12 i) = true ∧ y (Fin.natAdd 9 j) = true
      ∃ (D : Circuit) (w0 w1 w2 w3 : ℕ), Monotone2 D ∧ D.size ≤ 51 ∧
        (∃ g : Gate, D.gates.head? = some g ∧
          (g.op = .and ∧ g.inputs = [0, 9] ∨
           g.op = .or ∧ g.inputs ∈ [[0, 1], [0, 9], [2, 9]])) ∧
        D.output < 21 + D.size ∧ w0 < 21 + D.size ∧ w1 < 21 + D.size ∧
        w2 < 21 + D.size ∧ w3 < 21 + D.size ∧
        (∀ y : Fin 21 → Bool, D.eval (List.ofFn y) = true ↔ aff y) ∧
        ∀ y : Fin 21 → Bool, D.eval (List.ofFn y) = false →
          (D.wires (List.ofFn y)).getD w0 false = (y 16 || y 17 || y 19) ∧
          (D.wires (List.ofFn y)).getD w1 false = (y 9 || y 13 || y 15) ∧
          (D.wires (List.ofFn y)).getD w2 false = (y 12 || y 14 || y 20) ∧
          (D.wires (List.ofFn y)).getD w3 false = (y 10 || y 11 || y 18))
    (liftAffine :
      let rename := fun i : ℕ =>
        if i < 5 then i
        else if i < 8 then i + 1
        else if i = 8 then 11
        else if i < 13 then i + 4
        else i + 5
      ∀ D : Circuit, Monotone2 D →
        (∃ g : Gate, D.gates.head? = some g ∧
          (g.op = .and ∧ g.inputs = [0, 9] ∨
           g.op = .or ∧ g.inputs ∈ [[0, 1], [0, 9], [2, 9]])) →
        ∃ E : Circuit, Monotone2 E ∧ E.size = D.size ∧
          (∃ g : Gate, E.gates.head? = some g ∧
            (g.op = .and ∧ g.inputs = [0, 13] ∨
             g.op = .or ∧ g.inputs ∈ [[0, 1], [0, 13], [2, 13]])) ∧
          ∀ (x : Fin 26 → Bool) (i : ℕ),
            let y := fun j : Fin 21 => x (Fin.ofNat 26 (rename j.val))
            (E.wires (List.ofFn x)).getD (rename i) false = (D.wires (List.ofFn y)).getD i false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∃ (x3 : PEqualNP.CircuitLowerBounds.Gate), x2.gates.head? = Option.some x3 ∧ (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 + x4 ∈ x1 → x2.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x3) (Fin.natAdd (13 : ℕ) x4))) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card ≤ (3 : ℕ) → x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 + x6 ∉ x1)) x5) = Bool.false ∧ x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x6 + x7 ∉ x1)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) x5) = Bool.false := by
  let offs : Finset (Fin 13) := {0, 1, 3, 9}
  let pt := fun i : ℕ => if i < 5 then i else if i < 8 then i + 1 else 11
  let ln := fun j : ℕ => if j < 4 then j else j + 1
  let rename := fun i : ℕ =>
    if i < 5 then i
    else if i < 8 then i + 1
    else if i = 8 then 11
    else if i < 13 then i + 4
    else i + 5
  let restrict := fun (x : Fin 26 → Bool) (j : Fin 21) => x (Fin.ofNat 26 (rename j.val))
  obtain ⟨D, w0, w1, w2, w3, okD, sizeD, headD, outD, bw0, bw1, bw2, bw3, evD, resD⟩ := affineCore
  obtain ⟨E, okE, sizeE, headE, transfer⟩ := liftAffine D okD headD
  let n := 26 + E.size
  let suffix : List Gate :=
    [⟨.or, [17, rename w0]⟩, ⟨.and, [5, n]⟩,
     ⟨.or, [17, rename w1]⟩, ⟨.and, [9, n + 2]⟩,
     ⟨.or, [17, rename w2]⟩, ⟨.and, [10, n + 4]⟩,
     ⟨.or, [17, rename w3]⟩, ⟨.and, [12, n + 6]⟩,
     ⟨.or, [rename D.output, n + 1]⟩,
     ⟨.or, [n + 8, n + 3]⟩,
     ⟨.or, [n + 9, n + 5]⟩,
     ⟨.or, [n + 10, n + 7]⟩]
  let C : Circuit := ⟨E.gates ++ suffix, n + 11⟩
  have okC : Monotone2 C := by
    intro g hg
    change g ∈ E.gates ++ suffix at hg
    rcases List.mem_append.mp hg with hE | hS
    · exact okE g hE
    · simp only [suffix, List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have sizeC : C.size ≤ 63 := by
    have hElen : E.gates.length = D.gates.length := sizeE
    have hDlen : D.gates.length ≤ 51 := sizeD
    change (E.gates ++ suffix).length ≤ 63
    rw [List.length_append]
    simp only [suffix, List.length_cons, List.length_nil]
    omega
  have headC : ∃ g : Gate, C.gates.head? = some g ∧
      (g.op = .and ∧ g.inputs = [0, 13] ∨
       g.op = .or ∧ g.inputs ∈ [[0, 1], [0, 13], [2, 13]]) := by
    obtain ⟨g, hg, hspec⟩ := headE
    refine ⟨g, ?_, hspec⟩
    change (E.gates ++ suffix).head? = some g
    cases h : E.gates with
    | nil => simp only [h, List.head?_nil, reduceCtorEq] at hg
    | cons a as =>
      rw [h] at hg
      exact hg
  let run : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List Gate) (w : List Bool) : (gs.foldl run w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [run, List.length_append, List.length_cons, List.length_nil]
      omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl run w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (run w g) (by simp only [run, List.length_append, List.length_cons, List.length_nil]; omega)]
      exact List.getD_append _ _ _ _ hi
  have runOr (w : List Bool) (i j : ℕ) :
      run w ⟨.or, [i, j]⟩ = w ++ [w.getD i false || w.getD j false] := by
    change w ++ [w.getD i false || (w.getD j false || false)] = _
    simp only [Bool.or_false]
  have runAnd (w : List Bool) (i j : ℕ) :
      run w ⟨.and, [i, j]⟩ = w ++ [w.getD i false && w.getD j false] := by
    change w ++ [w.getD i false && (w.getD j false && true)] = _
    simp only [Bool.and_true]
  have mappedBound (i : ℕ) (hi : i < 21 + D.size) : rename i < n := by
    have hElen : E.size = D.size := sizeE
    dsimp only [rename, n]
    rw [hElen]
    split
    · omega
    · split
      · omega
      · split
        · omega
        · split <;> omega
  have evC (x : Fin 26 → Bool) :
      let y := restrict x
      let v := D.wires (List.ofFn y)
      C.eval (List.ofFn x) =
        ((((D.eval (List.ofFn y) || (x 5 && (x 17 || v.getD w0 false))) ||
          (x 9 && (x 17 || v.getD w1 false))) ||
          (x 10 && (x 17 || v.getD w2 false))) ||
          (x 12 && (x 17 || v.getD w3 false))) := by
    let w := E.wires (List.ofFn x)
    let y := restrict x
    have wlen : w.length = n := by
      exact (len E.gates (List.ofFn x)).trans (by simp only [List.length_ofFn, n]; rfl)
    have old (extra : List Bool) (i : ℕ) (hi : i < n) :
        (w ++ extra).getD i false = w.getD i false :=
      List.getD_append _ _ _ _ (by omega)
    have new (extra : List Bool) (k : ℕ) :
        (w ++ extra).getD (n + k) false = extra.getD k false := by
      rw [List.getD_append_right _ _ _ _ (by omega), wlen, Nat.add_sub_cancel_left]
    have firstNew (extra : List Bool) :
        (w ++ extra).getD n false = extra.getD 0 false := by
      simpa only [Nat.add_zero] using new extra 0
    have raw (i : Fin 26) : w.getD i.val false = x i := by
      rw [show w.getD i.val false = (List.ofFn x).getD i.val false from
        keep E.gates (List.ofFn x) i.val (by simpa only [List.length_ofFn] using i.isLt)]
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn _
    have bOut : rename D.output < n := mappedBound D.output outD
    have b0 : rename w0 < n := mappedBound w0 bw0
    have b1 : rename w1 < n := mappedBound w1 bw1
    have b2 : rename w2 < n := mappedBound w2 bw2
    have b3 : rename w3 < n := mappedBound w3 bw3
    have r5 : w.getD 5 false = x 5 := raw 5
    have r9 : w.getD 9 false = x 9 := raw 9
    have r10 : w.getD 10 false = x 10 := raw 10
    have r12 : w.getD 12 false = x 12 := raw 12
    have r17 : w.getD 17 false = x 17 := raw 17
    have h17 : 17 < n := by dsimp only [n]; omega
    have h5 : 5 < n := by dsimp only [n]; omega
    have h9 : 9 < n := by dsimp only [n]; omega
    have h10 : 10 < n := by dsimp only [n]; omega
    have h12 : 12 < n := by dsimp only [n]; omega
    have cWires : C.wires (List.ofFn x) = suffix.foldl run w := by
      change (E.gates ++ suffix).foldl run (List.ofFn x) = suffix.foldl run w
      rw [List.foldl_append]
      rfl
    change (C.wires (List.ofFn x)).getD (n + 11) false = _
    rw [cWires]
    dsimp only [suffix]
    let g0 := w.getD 17 false || w.getD (rename w0) false
    let g1 := w.getD 5 false && g0
    let g2 := w.getD 17 false || w.getD (rename w1) false
    let g3 := w.getD 9 false && g2
    let g4 := w.getD 17 false || w.getD (rename w2) false
    let g5 := w.getD 10 false && g4
    let g6 := w.getD 17 false || w.getD (rename w3) false
    let g7 := w.getD 12 false && g6
    let g8 := w.getD (rename D.output) false || g1
    let g9 := g8 || g3
    let g10 := g9 || g5
    let g11 := g10 || g7
    have s0 : run w ⟨.or, [17, rename w0]⟩ = w ++ [g0] := runOr w 17 (rename w0)
    have s1 : run (w ++ [g0]) ⟨.and, [5, n]⟩ = w ++ [g0, g1] := by
      rw [runAnd, old [g0] 5 h5, firstNew [g0], List.append_assoc]; rfl
    have s2 : run (w ++ [g0, g1]) ⟨.or, [17, rename w1]⟩ = w ++ [g0, g1, g2] := by
      rw [runOr, old _ 17 h17, old _ (rename w1) b1, List.append_assoc]; rfl
    have s3 : run (w ++ [g0, g1, g2]) ⟨.and, [9, n + 2]⟩ = w ++ [g0, g1, g2, g3] := by
      rw [runAnd, old _ 9 h9, new _ 2, List.append_assoc]; rfl
    have s4 : run (w ++ [g0, g1, g2, g3]) ⟨.or, [17, rename w2]⟩ = w ++ [g0, g1, g2, g3, g4] := by
      rw [runOr, old _ 17 h17, old _ (rename w2) b2, List.append_assoc]; rfl
    have s5 : run (w ++ [g0, g1, g2, g3, g4]) ⟨.and, [10, n + 4]⟩ = w ++ [g0, g1, g2, g3, g4, g5] := by
      rw [runAnd, old _ 10 h10, new _ 4, List.append_assoc]; rfl
    have s6 : run (w ++ [g0, g1, g2, g3, g4, g5]) ⟨.or, [17, rename w3]⟩ = w ++ [g0, g1, g2, g3, g4, g5, g6] := by
      rw [runOr, old _ 17 h17, old _ (rename w3) b3, List.append_assoc]; rfl
    have s7 : run (w ++ [g0, g1, g2, g3, g4, g5, g6]) ⟨.and, [12, n + 6]⟩ = w ++ [g0, g1, g2, g3, g4, g5, g6, g7] := by
      rw [runAnd, old _ 12 h12, new _ 6, List.append_assoc]; rfl
    have s8 : run (w ++ [g0, g1, g2, g3, g4, g5, g6, g7]) ⟨.or, [rename D.output, n + 1]⟩ = w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8] := by
      rw [runOr, old _ (rename D.output) bOut, new _ 1, List.append_assoc]; rfl
    have s9 : run (w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8]) ⟨.or, [n + 8, n + 3]⟩ = w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] := by
      rw [runOr, new _ 8, new _ 3, List.append_assoc]; rfl
    have s10 : run (w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9]) ⟨.or, [n + 9, n + 5]⟩ = w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10] := by
      rw [runOr, new _ 9, new _ 5, List.append_assoc]; rfl
    have s11 : run (w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10]) ⟨.or, [n + 10, n + 7]⟩ = w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] := by
      rw [runOr, new _ 10, new _ 7, List.append_assoc]; rfl
    rw [List.foldl_cons, s0, List.foldl_cons, s1, List.foldl_cons, s2, List.foldl_cons, s3,
        List.foldl_cons, s4, List.foldl_cons, s5, List.foldl_cons, s6, List.foldl_cons, s7,
        List.foldl_cons, s8, List.foldl_cons, s9, List.foldl_cons, s10, List.foldl_cons, s11,
        List.foldl_nil, new _ 11]
    change g11 = _
    dsimp only [g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, g0]
    rw [r5, r9, r10, r12, r17]
    have tOut : w.getD (rename D.output) false = D.eval (List.ofFn y) := transfer x D.output
    have t0 : w.getD (rename w0) false = (D.wires (List.ofFn y)).getD w0 false := transfer x w0
    have t1 : w.getD (rename w1) false = (D.wires (List.ofFn y)).getD w1 false := transfer x w1
    have t2 : w.getD (rename w2) false = (D.wires (List.ofFn y)).getD w2 false := transfer x w2
    have t3 : w.getD (rename w3) false = (D.wires (List.ofFn y)).getD w3 false := transfer x w3
    rw [tOut, t0, t1, t2, t3]
  have ptAddr : ∀ i : Fin 9, Fin.ofNat 26 (rename (Fin.castAdd 12 i).val) = Fin.castAdd 13 (Fin.ofNat 13 (pt i.val)) := by decide +kernel
  have lnAddr : ∀ j : Fin 12, Fin.ofNat 26 (rename (Fin.natAdd 9 j).val) = Fin.natAdd 13 (Fin.ofNat 13 (ln j.val)) := by decide +kernel
  have incAff : ∀ (i : Fin 9) (j : Fin 12),
      (pt i.val + ln j.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ↔
        Fin.ofNat 13 (pt i.val) + Fin.ofNat 13 (ln j.val) ∈ offs := by decide +kernel
  have coverPG : ∀ p l : Fin 13, p + l ∈ offs →
      (∃ (i : Fin 9) (j : Fin 12), (pt i.val + ln j.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        Fin.ofNat 13 (pt i.val) = p ∧ Fin.ofNat 13 (ln j.val) = l) ∨
      (p = 5 ∧ (l = 4 ∨ l = 8 ∨ l = 9 ∨ l = 11)) ∨
      (p = 9 ∧ (l = 4 ∨ l = 0 ∨ l = 5 ∨ l = 7)) ∨
      (p = 10 ∧ (l = 4 ∨ l = 3 ∨ l = 6 ∨ l = 12)) ∨
      (p = 12 ∧ (l = 4 ∨ l = 1 ∨ l = 2 ∨ l = 10)) := by decide +kernel
  have soundInf :
      (∀ l : Fin 13, (l = 4 ∨ l = 8 ∨ l = 9 ∨ l = 11) → (5 : Fin 13) + l ∈ offs) ∧
      (∀ l : Fin 13, (l = 4 ∨ l = 0 ∨ l = 5 ∨ l = 7) → (9 : Fin 13) + l ∈ offs) ∧
      (∀ l : Fin 13, (l = 4 ∨ l = 3 ∨ l = 6 ∨ l = 12) → (10 : Fin 13) + l ∈ offs) ∧
      (∀ l : Fin 13, (l = 4 ∨ l = 1 ∨ l = 2 ∨ l = 10) → (12 : Fin 13) + l ∈ offs) := by decide +kernel
  have evalExact (x : Fin 26 → Bool) :
      C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p + l ∈ offs ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    have hE := evC x
    dsimp only at hE
    rw [hE]
    cases hd : D.eval (List.ofFn (restrict x)) with
    | true =>
      simp only [Bool.true_or, true_iff]
      obtain ⟨i, j, hij, hi, hj⟩ := (evD (restrict x)).mp hd
      refine ⟨Fin.ofNat 13 (pt i.val), Fin.ofNat 13 (ln j.val), (incAff i j).mp hij, ?_, ?_⟩
      · simpa only [restrict, ptAddr i] using hi
      · simpa only [restrict, lnAddr j] using hj
    | false =>
      obtain ⟨hw0, hw1, hw2, hw3⟩ := resD (restrict x) hd
      rw [hw0, hw1, hw2, hw3]
      have hy9 : restrict x 9 = x 13 := rfl
      have hy10 : restrict x 10 = x 14 := rfl
      have hy11 : restrict x 11 = x 15 := rfl
      have hy12 : restrict x 12 = x 16 := rfl
      have hy13 : restrict x 13 = x 18 := rfl
      have hy14 : restrict x 14 = x 19 := rfl
      have hy15 : restrict x 15 = x 20 := rfl
      have hy16 : restrict x 16 = x 21 := rfl
      have hy17 : restrict x 17 = x 22 := rfl
      have hy18 : restrict x 18 = x 23 := rfl
      have hy19 : restrict x 19 = x 24 := rfl
      have hy20 : restrict x 20 = x 25 := rfl
      rw [hy9, hy10, hy11, hy12, hy13, hy14, hy15, hy16, hy17, hy18, hy19, hy20]
      simp only [Bool.false_or, Bool.or_eq_true, Bool.and_eq_true]
      constructor
      · intro h
        rcases h with (((⟨hp, hl⟩ | ⟨hp, hl⟩) | ⟨hp, hl⟩) | ⟨hp, hl⟩)
        · rcases hl with h17 | ((h21 | h22) | h24)
          · exact ⟨5, 4, soundInf.1 4 (Or.inl rfl), hp, h17⟩
          · exact ⟨5, 8, soundInf.1 8 (Or.inr (Or.inl rfl)), hp, h21⟩
          · exact ⟨5, 9, soundInf.1 9 (Or.inr (Or.inr (Or.inl rfl))), hp, h22⟩
          · exact ⟨5, 11, soundInf.1 11 (Or.inr (Or.inr (Or.inr rfl))), hp, h24⟩
        · rcases hl with h17 | ((h13 | h18) | h20)
          · exact ⟨9, 4, soundInf.2.1 4 (Or.inl rfl), hp, h17⟩
          · exact ⟨9, 0, soundInf.2.1 0 (Or.inr (Or.inl rfl)), hp, h13⟩
          · exact ⟨9, 5, soundInf.2.1 5 (Or.inr (Or.inr (Or.inl rfl))), hp, h18⟩
          · exact ⟨9, 7, soundInf.2.1 7 (Or.inr (Or.inr (Or.inr rfl))), hp, h20⟩
        · rcases hl with h17 | ((h16 | h19) | h25)
          · exact ⟨10, 4, soundInf.2.2.1 4 (Or.inl rfl), hp, h17⟩
          · exact ⟨10, 3, soundInf.2.2.1 3 (Or.inr (Or.inl rfl)), hp, h16⟩
          · exact ⟨10, 6, soundInf.2.2.1 6 (Or.inr (Or.inr (Or.inl rfl))), hp, h19⟩
          · exact ⟨10, 12, soundInf.2.2.1 12 (Or.inr (Or.inr (Or.inr rfl))), hp, h25⟩
        · rcases hl with h17 | ((h14 | h15) | h23)
          · exact ⟨12, 4, soundInf.2.2.2 4 (Or.inl rfl), hp, h17⟩
          · exact ⟨12, 1, soundInf.2.2.2 1 (Or.inr (Or.inl rfl)), hp, h14⟩
          · exact ⟨12, 2, soundInf.2.2.2 2 (Or.inr (Or.inr (Or.inl rfl))), hp, h15⟩
          · exact ⟨12, 10, soundInf.2.2.2 10 (Or.inr (Or.inr (Or.inr rfl))), hp, h23⟩
      · rintro ⟨p, l, hpl, hp, hl⟩
        rcases coverPG p l hpl with ⟨i, j, hij, rfl, rfl⟩ | ⟨rfl, hl'⟩ | ⟨rfl, hl'⟩ | ⟨rfl, hl'⟩ | ⟨rfl, hl'⟩
        · exfalso
          have htrue : D.eval (List.ofFn (restrict x)) = true :=
            (evD (restrict x)).mpr ⟨i, j, hij,
              by simpa only [restrict, ptAddr i] using hp,
              by simpa only [restrict, lnAddr j] using hl⟩
          rw [hd] at htrue
          exact Bool.false_ne_true htrue
        · left; left; left; refine ⟨hp, ?_⟩
          rcases hl' with rfl | rfl | rfl | rfl
          · exact Or.inl hl
          · exact Or.inr (Or.inl (Or.inl hl))
          · exact Or.inr (Or.inl (Or.inr hl))
          · exact Or.inr (Or.inr hl)
        · left; left; right; refine ⟨hp, ?_⟩
          rcases hl' with rfl | rfl | rfl | rfl
          · exact Or.inl hl
          · exact Or.inr (Or.inl (Or.inl hl))
          · exact Or.inr (Or.inl (Or.inr hl))
          · exact Or.inr (Or.inr hl)
        · left; right; refine ⟨hp, ?_⟩
          rcases hl' with rfl | rfl | rfl | rfl
          · exact Or.inl hl
          · exact Or.inr (Or.inl (Or.inl hl))
          · exact Or.inr (Or.inl (Or.inr hl))
          · exact Or.inr (Or.inr hl)
        · right; refine ⟨hp, ?_⟩
          rcases hl' with rfl | rfl | rfl | rfl
          · exact Or.inl hl
          · exact Or.inr (Or.inl (Or.inl hl))
          · exact Or.inr (Or.inl (Or.inr hl))
          · exact Or.inr (Or.inr hl)
  refine ⟨C, okC, sizeC, headC, ?_, ?_⟩
  · intro p l hpl
    exact (evalExact _).mpr ⟨p, l, hpl,
      (by change decide (Fin.castAdd 13 p = Fin.castAdd 13 p ∨ Fin.castAdd 13 p = Fin.natAdd 13 l) = true; exact decide_eq_true (Or.inl rfl)),
      (by change decide (Fin.natAdd 13 l = Fin.castAdd 13 p ∨ Fin.natAdd 13 l = Fin.natAdd 13 l) = true; exact decide_eq_true (Or.inr rfl))⟩
  · intro S _
    constructor
    · cases hc : C.eval (List.ofFn fun (x5 : Fin (13 + 13)) =>
          Fin.addCases (fun x6 : Fin 13 => decide (x6 ∈ S))
            (fun x6 : Fin 13 => decide (∀ x7 ∈ S, x7 + x6 ∉ offs)) x5) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨p, l, hpl, hp, hl⟩ := (evalExact _).mp hc
        simp only [Fin.addCases_left, decide_eq_true_eq] at hp
        simp only [Fin.addCases_right, decide_eq_true_eq] at hl
        exact hl p hp hpl
    · cases hc : C.eval (List.ofFn fun (x5 : Fin (13 + 13)) =>
          Fin.addCases (fun x6 : Fin 13 => decide (∀ x7 ∈ S, x6 + x7 ∉ offs))
            (fun x6 : Fin 13 => decide (x6 ∈ S)) x5) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨p, l, hpl, hp, hl⟩ := (evalExact _).mp hc
        simp only [Fin.addCases_left, decide_eq_true_eq] at hp
        simp only [Fin.addCases_right, decide_eq_true_eq] at hl
        exact hp l hl hpl
