import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2215_2
    (affineCore :
      let pt := fun i : ℕ => if i = 0 then 1 else if i < 6 then i + 2 else i + 3
      let aff := fun y : Fin 21 → Bool =>
        ∃ (i : Fin 9) (j : Fin 12), (pt i.val + j.val + 15) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
          y (Fin.castAdd 12 i) = true ∧ y (Fin.natAdd 9 j) = true
      ∃ (D : Circuit) (w0 w1 w2 w3 : ℕ), Monotone2 D ∧ D.size ≤ 51 ∧
        D.output < 21 + D.size ∧ w0 < 21 + D.size ∧ w1 < 21 + D.size ∧
        w2 < 21 + D.size ∧ w3 < 21 + D.size ∧
        (∀ y : Fin 21 → Bool, D.eval (List.ofFn y) = true ↔ aff y) ∧
        ∀ y : Fin 21 → Bool, D.eval (List.ofFn y) = false →
          (D.wires (List.ofFn y)).getD w0 false = (y 9 || y 11 || y 17) ∧
          (D.wires (List.ofFn y)).getD w1 false = (y 10 || y 16 || y 20) ∧
          (D.wires (List.ofFn y)).getD w2 false = (y 14 || y 18 || y 19) ∧
          (D.wires (List.ofFn y)).getD w3 false = (y 12 || y 13 || y 15))
    (liftAffine :
      let rename := fun i : ℕ =>
        if i = 0 then 1
        else if i < 6 then i + 2
        else if i < 9 then i + 3
        else i + 4
      ∀ D : Circuit, Monotone2 D →
        ∃ E : Circuit, Monotone2 E ∧ E.size = D.size ∧
          ∀ (x : Fin 25 → Bool) (i : ℕ),
            let y := fun j : Fin 21 => x (Fin.ofNat 25 (rename j.val))
            (E.wires (List.ofFn x)).getD (rename i) false = (D.wires (List.ofFn y)).getD i false) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  let pt := fun i : ℕ => if i = 0 then 1 else if i < 6 then i + 2 else i + 3
  let rename := fun i : ℕ =>
    if i = 0 then 1
    else if i < 6 then i + 2
    else if i < 9 then i + 3
    else i + 4
  let restrict := fun (x : Fin 25 → Bool) (j : Fin 21) => x (Fin.ofNat 25 (rename j.val))
  obtain ⟨D, w0, w1, w2, w3, okD, sizeD, outD, bw0, bw1, bw2, bw3, evD, resD⟩ := affineCore
  obtain ⟨E, okE, sizeE, transfer⟩ := liftAffine D okD
  let n := 25 + E.size
  let suffix : List Gate :=
    [⟨.or, [12, rename w0]⟩,
     ⟨.or, [12, rename w1]⟩, ⟨.and, [0, n + 1]⟩,
     ⟨.or, [12, rename w2]⟩, ⟨.and, [2, n + 3]⟩,
     ⟨.or, [12, rename w3]⟩, ⟨.and, [8, n + 5]⟩,
     ⟨.or, [rename D.output, n + 2]⟩,
     ⟨.or, [n + 7, n + 4]⟩,
     ⟨.or, [n + 8, n + 6]⟩]
  let C : Circuit := ⟨E.gates ++ suffix, n + 9⟩
  have okC : Monotone2 C := by
    intro g hg
    change g ∈ E.gates ++ suffix at hg
    rcases List.mem_append.mp hg with hE | hS
    · exact okE g hE
    · simp only [suffix, List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have sizeCeq : C.size = E.size + 10 := by
    change (E.gates ++ suffix).length = E.gates.length + 10
    rw [List.length_append]
    rfl
  have sizeC : C.size ≤ 61 := by
    have hElen : E.size = D.size := sizeE
    omega
  have outC : C.output < 25 + C.size := by
    change n + 9 < 25 + C.size
    dsimp only [n]
    omega
  have auxC : n < 25 + C.size := by
    dsimp only [n]
    omega
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
      · split <;> omega
  have wiresC (x : Fin 25 → Bool) :
      let y := restrict x
      let v := D.wires (List.ofFn y)
      C.eval (List.ofFn x) =
        (((D.eval (List.ofFn y) || (x 0 && (x 12 || v.getD w1 false))) ||
          (x 2 && (x 12 || v.getD w2 false))) ||
          (x 8 && (x 12 || v.getD w3 false))) ∧
      (C.wires (List.ofFn x)).getD n false = (x 12 || v.getD w0 false) := by
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
    have raw (i : Fin 25) : w.getD i.val false = x i := by
      rw [show w.getD i.val false = (List.ofFn x).getD i.val false from
        keep E.gates (List.ofFn x) i.val (by simpa only [List.length_ofFn] using i.isLt)]
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn _
    have bOut : rename D.output < n := mappedBound D.output outD
    have b0 : rename w0 < n := mappedBound w0 bw0
    have b1 : rename w1 < n := mappedBound w1 bw1
    have b2 : rename w2 < n := mappedBound w2 bw2
    have b3 : rename w3 < n := mappedBound w3 bw3
    have r0 : w.getD 0 false = x 0 := raw 0
    have r2 : w.getD 2 false = x 2 := raw 2
    have r8 : w.getD 8 false = x 8 := raw 8
    have r12 : w.getD 12 false = x 12 := raw 12
    have h0 : 0 < n := by dsimp only [n]; omega
    have h2 : 2 < n := by dsimp only [n]; omega
    have h8 : 8 < n := by dsimp only [n]; omega
    have h12 : 12 < n := by dsimp only [n]; omega
    let g0 := w.getD 12 false || w.getD (rename w0) false
    let g1 := w.getD 12 false || w.getD (rename w1) false
    let g2 := w.getD 0 false && g1
    let g3 := w.getD 12 false || w.getD (rename w2) false
    let g4 := w.getD 2 false && g3
    let g5 := w.getD 12 false || w.getD (rename w3) false
    let g6 := w.getD 8 false && g5
    let g7 := w.getD (rename D.output) false || g2
    let g8 := g7 || g4
    let g9 := g8 || g6
    have s0 : run w ⟨.or, [12, rename w0]⟩ = w ++ [g0] := runOr w 12 (rename w0)
    have s1 : run (w ++ [g0]) ⟨.or, [12, rename w1]⟩ = w ++ [g0, g1] := by
      rw [runOr, old _ 12 h12, old _ (rename w1) b1, List.append_assoc]; rfl
    have s2 : run (w ++ [g0, g1]) ⟨.and, [0, n + 1]⟩ = w ++ [g0, g1, g2] := by
      rw [runAnd, old _ 0 h0, new _ 1, List.append_assoc]; rfl
    have s3 : run (w ++ [g0, g1, g2]) ⟨.or, [12, rename w2]⟩ = w ++ [g0, g1, g2, g3] := by
      rw [runOr, old _ 12 h12, old _ (rename w2) b2, List.append_assoc]; rfl
    have s4 : run (w ++ [g0, g1, g2, g3]) ⟨.and, [2, n + 3]⟩ = w ++ [g0, g1, g2, g3, g4] := by
      rw [runAnd, old _ 2 h2, new _ 3, List.append_assoc]; rfl
    have s5 : run (w ++ [g0, g1, g2, g3, g4]) ⟨.or, [12, rename w3]⟩ = w ++ [g0, g1, g2, g3, g4, g5] := by
      rw [runOr, old _ 12 h12, old _ (rename w3) b3, List.append_assoc]; rfl
    have s6 : run (w ++ [g0, g1, g2, g3, g4, g5]) ⟨.and, [8, n + 5]⟩ = w ++ [g0, g1, g2, g3, g4, g5, g6] := by
      rw [runAnd, old _ 8 h8, new _ 5, List.append_assoc]; rfl
    have s7 : run (w ++ [g0, g1, g2, g3, g4, g5, g6]) ⟨.or, [rename D.output, n + 2]⟩ = w ++ [g0, g1, g2, g3, g4, g5, g6, g7] := by
      rw [runOr, old _ (rename D.output) bOut, new _ 2, List.append_assoc]; rfl
    have s8 : run (w ++ [g0, g1, g2, g3, g4, g5, g6, g7]) ⟨.or, [n + 7, n + 4]⟩ = w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8] := by
      rw [runOr, new _ 7, new _ 4, List.append_assoc]; rfl
    have s9 : run (w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8]) ⟨.or, [n + 8, n + 6]⟩ = w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] := by
      rw [runOr, new _ 8, new _ 6, List.append_assoc]; rfl
    have cWires : C.wires (List.ofFn x) = w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] := by
      change (E.gates ++ suffix).foldl run (List.ofFn x) = _
      rw [List.foldl_append]
      change suffix.foldl run w = _
      dsimp only [suffix]
      rw [List.foldl_cons, s0, List.foldl_cons, s1, List.foldl_cons, s2, List.foldl_cons, s3,
          List.foldl_cons, s4, List.foldl_cons, s5, List.foldl_cons, s6, List.foldl_cons, s7,
          List.foldl_cons, s8, List.foldl_cons, s9, List.foldl_nil]
    have tOut : w.getD (rename D.output) false = D.eval (List.ofFn y) := transfer x D.output
    have t0 : w.getD (rename w0) false = (D.wires (List.ofFn y)).getD w0 false := transfer x w0
    have t1 : w.getD (rename w1) false = (D.wires (List.ofFn y)).getD w1 false := transfer x w1
    have t2 : w.getD (rename w2) false = (D.wires (List.ofFn y)).getD w2 false := transfer x w2
    have t3 : w.getD (rename w3) false = (D.wires (List.ofFn y)).getD w3 false := transfer x w3
    constructor
    · change (C.wires (List.ofFn x)).getD (n + 9) false = _
      rw [cWires, new _ 9]
      change g9 = _
      dsimp only [g9, g8, g7, g6, g5, g4, g3, g2, g1]
      rw [r0, r2, r8, r12, tOut, t1, t2, t3]
    · rw [cWires, firstNew]
      change g0 = _
      dsimp only [g0]
      rw [r12, t0]
  have ptAddr : ∀ i : Fin 9, Fin.ofNat 25 (rename (Fin.castAdd 12 i).val) = Fin.ofNat 25 (pt i.val) := by decide +kernel
  have lnAddr : ∀ j : Fin 12, Fin.ofNat 25 (rename (Fin.natAdd 9 j).val) = Fin.ofNat 25 (j.val + 13) := by decide +kernel
  have affTo25 : ∀ (i : Fin 9) (j : Fin 12),
      (pt i.val + j.val + 15) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
        (Fin.ofNat 25 (pt i.val)).val < 12 ∧ 12 ≤ (Fin.ofNat 25 (j.val + 13)).val ∧
        ((Fin.ofNat 25 (pt i.val)).val + (Fin.ofNat 25 (j.val + 13)).val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by decide +kernel
  have cover25 : ∀ (a b : Fin 25),
      a.val < 12 ∧ 12 ≤ b.val ∧ (a.val + b.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
      (∃ (i : Fin 9) (j : Fin 12), (pt i.val + j.val + 15) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        Fin.ofNat 25 (pt i.val) = a ∧ Fin.ofNat 25 (j.val + 13) = b) ∨
      (a = 0 ∧ (b = 12 ∨ b = 14 ∨ b = 20 ∨ b = 24)) ∨
      (a = 2 ∧ (b = 12 ∨ b = 18 ∨ b = 22 ∨ b = 23)) ∨
      (a = 8 ∧ (b = 12 ∨ b = 16 ∨ b = 17 ∨ b = 19)) := by decide +kernel
  have soundInf :
      (∀ b : Fin 25, (b = 12 ∨ b = 14 ∨ b = 20 ∨ b = 24) →
        (0 : Fin 25).val < 12 ∧ 12 ≤ b.val ∧ ((0 : Fin 25).val + b.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∧
      (∀ b : Fin 25, (b = 12 ∨ b = 18 ∨ b = 22 ∨ b = 23) →
        (2 : Fin 25).val < 12 ∧ 12 ≤ b.val ∧ ((2 : Fin 25).val + b.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∧
      (∀ b : Fin 25, (b = 12 ∨ b = 16 ∨ b = 17 ∨ b = 19) →
        (8 : Fin 25).val < 12 ∧ 12 ≤ b.val ∧ ((8 : Fin 25).val + b.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) := by
    refine ⟨?_, ?_, ?_⟩ <;> (intro b hb; rcases hb with rfl | rfl | rfl | rfl <;> decide)
  refine ⟨C, n, okC, sizeC, outC, auxC, ?_⟩
  intro x
  obtain ⟨hEv, hAux⟩ := wiresC x
  dsimp only at hEv hAux ⊢
  constructor
  · rw [hEv]
    cases hd : D.eval (List.ofFn (restrict x)) with
    | true =>
      simp only [Bool.true_or, true_iff]
      obtain ⟨i, j, hij, hi, hj⟩ := (evD (restrict x)).mp hd
      refine ⟨Fin.ofNat 25 (pt i.val), Fin.ofNat 25 (j.val + 13), affTo25 i j hij, ?_, ?_⟩
      · simpa only [restrict, ptAddr i] using hi
      · simpa only [restrict, lnAddr j] using hj
    | false =>
      obtain ⟨_, hw1, hw2, hw3⟩ := resD (restrict x) hd
      rw [hw1, hw2, hw3]
      have hy10 : restrict x 10 = x 14 := rfl
      have hy12 : restrict x 12 = x 16 := rfl
      have hy13 : restrict x 13 = x 17 := rfl
      have hy14 : restrict x 14 = x 18 := rfl
      have hy15 : restrict x 15 = x 19 := rfl
      have hy16 : restrict x 16 = x 20 := rfl
      have hy18 : restrict x 18 = x 22 := rfl
      have hy19 : restrict x 19 = x 23 := rfl
      have hy20 : restrict x 20 = x 24 := rfl
      rw [hy10, hy12, hy13, hy14, hy15, hy16, hy18, hy19, hy20]
      simp only [Bool.false_or, Bool.or_eq_true, Bool.and_eq_true]
      constructor
      · intro h
        rcases h with ((⟨hp, hl⟩ | ⟨hp, hl⟩) | ⟨hp, hl⟩)
        · rcases hl with h12 | ((h14 | h20) | h24)
          · exact ⟨0, 12, soundInf.1 12 (Or.inl rfl), hp, h12⟩
          · exact ⟨0, 14, soundInf.1 14 (Or.inr (Or.inl rfl)), hp, h14⟩
          · exact ⟨0, 20, soundInf.1 20 (Or.inr (Or.inr (Or.inl rfl))), hp, h20⟩
          · exact ⟨0, 24, soundInf.1 24 (Or.inr (Or.inr (Or.inr rfl))), hp, h24⟩
        · rcases hl with h12 | ((h18 | h22) | h23)
          · exact ⟨2, 12, soundInf.2.1 12 (Or.inl rfl), hp, h12⟩
          · exact ⟨2, 18, soundInf.2.1 18 (Or.inr (Or.inl rfl)), hp, h18⟩
          · exact ⟨2, 22, soundInf.2.1 22 (Or.inr (Or.inr (Or.inl rfl))), hp, h22⟩
          · exact ⟨2, 23, soundInf.2.1 23 (Or.inr (Or.inr (Or.inr rfl))), hp, h23⟩
        · rcases hl with h12 | ((h16 | h17) | h19)
          · exact ⟨8, 12, soundInf.2.2 12 (Or.inl rfl), hp, h12⟩
          · exact ⟨8, 16, soundInf.2.2 16 (Or.inr (Or.inl rfl)), hp, h16⟩
          · exact ⟨8, 17, soundInf.2.2 17 (Or.inr (Or.inr (Or.inl rfl))), hp, h17⟩
          · exact ⟨8, 19, soundInf.2.2 19 (Or.inr (Or.inr (Or.inr rfl))), hp, h19⟩
      · rintro ⟨a, b, hab, ha, hb⟩
        rcases cover25 a b hab with ⟨i, j, hij, rfl, rfl⟩ | ⟨rfl, hb'⟩ | ⟨rfl, hb'⟩ | ⟨rfl, hb'⟩
        · exfalso
          have htrue : D.eval (List.ofFn (restrict x)) = true :=
            (evD (restrict x)).mpr ⟨i, j, hij,
              by simpa only [restrict, ptAddr i] using ha,
              by simpa only [restrict, lnAddr j] using hb⟩
          rw [hd] at htrue
          exact Bool.false_ne_true htrue
        · left; left; refine ⟨ha, ?_⟩
          rcases hb' with rfl | rfl | rfl | rfl
          · exact Or.inl hb
          · exact Or.inr (Or.inl (Or.inl hb))
          · exact Or.inr (Or.inl (Or.inr hb))
          · exact Or.inr (Or.inr hb)
        · left; right; refine ⟨ha, ?_⟩
          rcases hb' with rfl | rfl | rfl | rfl
          · exact Or.inl hb
          · exact Or.inr (Or.inl (Or.inl hb))
          · exact Or.inr (Or.inl (Or.inr hb))
          · exact Or.inr (Or.inr hb)
        · right; refine ⟨ha, ?_⟩
          rcases hb' with rfl | rfl | rfl | rfl
          · exact Or.inl hb
          · exact Or.inr (Or.inl (Or.inl hb))
          · exact Or.inr (Or.inl (Or.inr hb))
          · exact Or.inr (Or.inr hb)
  · intro hcFalse
    have hdFalse : D.eval (List.ofFn (restrict x)) = false := by
      cases hd : D.eval (List.ofFn (restrict x)) with
      | false => rfl
      | true =>
        rw [hEv, hd, Bool.true_or, Bool.true_or, Bool.true_or] at hcFalse
        exact (Bool.false_ne_true hcFalse.symm).elim
    obtain ⟨hw0, _, _, _⟩ := resD (restrict x) hdFalse
    rw [hAux, hw0]
    have hy9 : restrict x 9 = x 13 := rfl
    have hy11 : restrict x 11 = x 15 := rfl
    have hy17 : restrict x 17 = x 21 := rfl
    rw [hy9, hy11, hy17]
    simp only [Bool.or_assoc]
