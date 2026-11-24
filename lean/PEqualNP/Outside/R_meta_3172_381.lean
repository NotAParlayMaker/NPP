import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3172_381
    (adjacent :
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool,
          C.eval (List.ofFn x ++ [!x 0] ++ [x 2 || x 3]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
             x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
             x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (nonadjacent :
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool,
          C.eval (List.ofFn x ++ [!x 0] ++ [x 2 || x 8]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
             x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
             x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro pins hlen _ hpins C hfan hsize
  let target (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let raw (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  let input (x : Fin 9 → Bool) (v : Bool) := raw x ++ [v]
  let renameGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩
  let rename (r : ℕ → ℕ) (D : Circuit) : Circuit :=
    ⟨D.gates.map (renameGate r), r D.output⟩
  let extend (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have renameFan (r : ℕ → ℕ) : FanInTwo (rename r C) := by
    intro g hg
    change g ∈ C.gates.map (renameGate r) at hg
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hOp, hArity⟩ := hfan old hold
    exact ⟨hOp, by simpa [renameGate] using hArity⟩
  have renameSize (r : ℕ → ℕ) : (rename r C).size ≤ 13 := by
    change (C.gates.map (renameGate r)).length ≤ 13
    rw [List.length_map]
    exact hsize
  have evaluate (r : ℕ → ℕ) (hfront : ∀ i < 11, r i < 11)
      (hback : ∀ i, 11 ≤ i → r i = i) (old new : List Bool)
      (hinit : old.length = 11) (hnew : new.length = 11)
      (hag : ∀ i, old.getD i false = new.getD (r i) false) :
      C.eval old = (rename r C).eval new := by
    have run (gs : List Gate) (a b : List Bool) (hlen : a.length = b.length)
        (hmin : 11 ≤ a.length)
        (h : ∀ i, a.getD i false = b.getD (r i) false) :
        ∀ i, (gs.foldl extend a).getD i false =
          ((gs.map (renameGate r)).foldl extend b).getD (r i) false := by
      induction gs generalizing a b with
      | nil => exact h
      | cons g gs ih =>
        intro i
        change (gs.foldl extend (extend a g)).getD i false =
          ((gs.map (renameGate r)).foldl extend (extend b (renameGate r g))).getD (r i) false
        have hArgs : g.inputs.map (fun j => a.getD j false) =
            (g.inputs.map r).map (fun j => b.getD j false) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro j _
          exact h j
        let value := g.op.eval (g.inputs.map fun j => a.getD j false)
        have hValue : extend b (renameGate r g) = b ++ [value] := by
          change b ++ [g.op.eval ((g.inputs.map r).map fun j => b.getD j false)] = _
          rw [← hArgs]
        rw [hValue]
        change (gs.foldl extend (a ++ [value])).getD i false =
          ((gs.map (renameGate r)).foldl extend (b ++ [value])).getD (r i) false
        apply ih (a ++ [value]) (b ++ [value]) (by simpa using hlen) (by simp; omega)
        intro j
        by_cases hj : j < a.length
        · have hrj : r j < b.length := by
            by_cases h11 : j < 11
            · have := hfront j h11
              omega
            · rw [hback j (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hrj]
          exact h j
        · have hj' : 11 ≤ j := by omega
          rw [hback j hj']
          rw [List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), hlen]
    exact run C.gates old new (hinit.trans hnew.symm) (by omega) hag C.output
  have rawLen (x : Fin 9 → Bool) : (raw x).length = 10 := by simp [raw]
  have inputLen (x : Fin 9 → Bool) (v : Bool) : (input x v).length = 11 := by
    simp [input, rawLen]
  have rawValue (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
      (raw x).getD i false = x ⟨i, hi⟩ := by
    change (List.ofFn x ++ [!x 0]).getD i false = _
    rw [List.getD_append _ _ _ _ (by simpa using hi)]
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  have inputRaw (x : Fin 9 → Bool) (v : Bool) (i : ℕ) (hi : i < 9) :
      (input x v).getD i false = x ⟨i, hi⟩ := by
    change (raw x ++ [v]).getD i false = _
    rw [List.getD_append _ _ _ _ (by rw [rawLen]; omega)]
    exact rawValue x i hi
  have inputNeg (x : Fin 9 → Bool) (v : Bool) : (input x v).getD 9 false = !x 0 := by
    change (raw x ++ [v]).getD 9 false = _
    rw [List.getD_append _ _ _ _ (by rw [rawLen]; omega)]
    change (List.ofFn x ++ [!x 0]).getD 9 false = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have inputExtra (x : Fin 9 → Bool) (v : Bool) : (input x v).getD 10 false = v := by
    change (raw x ++ [v]).getD 10 false = _
    rw [List.getD_append_right _ _ _ _ (by rw [rawLen]), rawLen]
    rfl
  have inputOutside (x : Fin 9 → Bool) (v : Bool) (i : ℕ) (hi : 11 ≤ i) :
      (input x v).getD i false = false := by
    exact List.getD_eq_default _ _ (by rwa [inputLen])
  -- Redirect repeated-input gates to the original input before applying the fixed pair case.
  have copied (a : Fin 9) :
      ∃ x, C.eval (input x (x a || x a)) ≠ target x := by
    let r (i : ℕ) := if i = 10 then a.val else i
    have rfront : ∀ i < 11, r i < 11 := by
      intro i hi
      have h := a.isLt
      by_cases h10 : i = 10 <;> simp [r, h10] <;> omega
    have rback : ∀ i, 11 ≤ i → r i = i := by
      intro i hi
      simp [r, show i ≠ 10 by omega]
    obtain ⟨x, hx⟩ := adjacent (rename r C) (renameFan r) (renameSize r)
    change (rename r C).eval (input x (x 2 || x 3)) ≠ target x at hx
    refine ⟨x, ?_⟩
    have agree (i : ℕ) :
        (input x (x a || x a)).getD i false = (input x (x 2 || x 3)).getD (r i) false := by
      by_cases h10 : i = 10
      · subst i
        rw [show r 10 = a.val by simp [r], inputExtra, inputRaw _ _ _ a.isLt]
        exact Bool.or_self _
      rw [show r i = i by simp [r, h10]]
      by_cases h9 : i < 9
      · rw [inputRaw _ _ _ h9, inputRaw _ _ _ h9]
      by_cases heq9 : i = 9
      · subst i
        rw [inputNeg, inputNeg]
      rw [inputOutside _ _ _ (by omega), inputOutside _ _ _ (by omega)]
    exact (evaluate r rfront rback _ _ (inputLen _ _) (inputLen _ _) agree).symm ▸ hx
  -- The automorphism fixes the complemented input and exchanges the two adjacent pairs.
  let perm : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  have permTarget (x : Fin 9 → Bool) : target (fun i => x (perm i)) = target x := by
    have p0 : perm 0 = 0 := rfl
    have p1 : perm 1 = 5 := rfl
    have p2 : perm 2 = 8 := rfl
    have p3 : perm 3 = 3 := rfl
    have p4 : perm 4 = 4 := rfl
    have p5 : perm 5 = 1 := rfl
    have p6 : perm 6 = 7 := rfl
    have p7 : perm 7 = 6 := rfl
    have p8 : perm 8 = 2 := rfl
    simp only [target, p0, p1, p2, p3, p4, p5, p6, p7, p8]
    ac_rfl
  have exchanged : ∃ x, C.eval (input x (x 3 || x 8)) ≠ target x := by
    let r (i : ℕ) := if hi : i < 9 then (perm ⟨i, hi⟩).val else i
    have rfront : ∀ i < 11, r i < 11 := by
      intro i hi
      by_cases h : i < 9
      · have hp := (perm ⟨i, h⟩).isLt
        simp [r, h]
        omega
      · simp [r, h, hi]
    have rback : ∀ i, 11 ≤ i → r i = i := by
      intro i hi
      simp [r, show ¬ i < 9 by omega]
    obtain ⟨x, hx⟩ := adjacent (rename r C) (renameFan r) (renameSize r)
    change (rename r C).eval (input x (x 2 || x 3)) ≠ target x at hx
    let y (i : Fin 9) := x (perm i)
    refine ⟨y, ?_⟩
    have agree (i : ℕ) :
        (input y (y 3 || y 8)).getD i false = (input x (x 2 || x 3)).getD (r i) false := by
      by_cases h9 : i < 9
      · rw [show r i = (perm ⟨i, h9⟩).val by simp [r, h9],
          inputRaw _ _ _ h9, inputRaw _ _ _ (perm ⟨i, h9⟩).isLt]
      rw [show r i = i by simp [r, h9]]
      by_cases heq9 : i = 9
      · subst i
        rw [inputNeg, inputNeg]
        rfl
      by_cases heq10 : i = 10
      · subst i
        rw [inputExtra, inputExtra]
        change (x 3 || x 2) = (x 2 || x 3)
        exact Bool.or_comm _ _
      rw [inputOutside _ _ _ (by omega), inputOutside _ _ _ (by omega)]
    rw [evaluate r rfront rback _ _ (inputLen _ _) (inputLen _ _) agree, permTarget x]
    exact hx
  have adjacentHere : ∃ x, C.eval (input x (x 2 || x 3)) ≠ target x :=
    adjacent C hfan hsize
  have nonadjacentHere : ∃ x, C.eval (input x (x 2 || x 8)) ≠ target x :=
    nonadjacent C hfan hsize
  have swapped (u v : Fin 9) (h : ∃ x, C.eval (input x (x u || x v)) ≠ target x) :
      ∃ x, C.eval (input x (x v || x u)) ≠ target x := by
    obtain ⟨x, hx⟩ := h
    refine ⟨x, ?_⟩
    rw [Bool.or_comm (x v) (x u)]
    exact hx
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have ha := hpins a (by simp)
  have hb := hpins b (by simp)
  have ha9 : a < 9 := by omega
  have hb9 : b < 9 := by omega
  change ∃ x, C.eval (input x (GateOp.or.eval ([a, b].map fun i => (raw x).getD i false))) ≠ target x
  have convert (x : Fin 9 → Bool) :
      GateOp.or.eval ([a, b].map fun i => (raw x).getD i false) =
        (x ⟨a, ha9⟩ || x ⟨b, hb9⟩) := by
    change ((raw x).getD a false || ((raw x).getD b false || false)) = _
    rw [rawValue x a ha9, rawValue x b hb9, Bool.or_false]
  simp only [convert]
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact copied 2
  · exact adjacentHere
  · exact nonadjacentHere
  · exact swapped 2 3 adjacentHere
  · exact copied 3
  · exact exchanged
  · exact swapped 2 8 nonadjacentHere
  · exact swapped 3 8 exchanged
  · exact copied 8
