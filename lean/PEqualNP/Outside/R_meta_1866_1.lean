import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 15000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_1866_1
    (proveRaw : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2 ∈ ([[0,1],[0,2],[0,4],[0,6],[1,2],[1,4],[1,5],[1,6],[1,7],[1,8],[4,6],[6,7]] : List (List (Fin 11))) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size)
    (proveOther : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2 ∈ ([[],[0],[1],[4],[6],[9],[10],[1,9],[4,9],[6,9]] : List (List (Fin 11))) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2.length ≤ (2 : ℕ) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  let rename (p : Fin 9 → Fin 9) (i : Nat) : Nat :=
    if h : i < 9 then (p ⟨i,h⟩).val else i

  let renameGate (p : Fin 9 → Fin 9) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (rename p)⟩

  let renameCircuit (p : Fin 9 → Fin 9) (C : Circuit) : Circuit :=
    ⟨C.gates.map (renameGate p), rename p C.output⟩

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have rename_size (p : Fin 9 → Fin 9) (C : Circuit) :
      (renameCircuit p C).size = C.size := by
    simp [renameCircuit, Circuit.size]

  have rename_basis (p : Fin 9 → Fin 9) (C : Circuit)
      (basis : PEqualNP.MetaComplexity.FanInTwo C) :
      PEqualNP.MetaComplexity.FanInTwo (renameCircuit p C) := by
    intro g hg
    change g ∈ C.gates.map (renameGate p) at hg
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hg
    simpa [renameGate] using basis old ho

  have rename_eval (p : Fin 9 → Fin 9) (C : Circuit) (u v : List Bool)
      (hlen : u.length = v.length) (hmin : 9 ≤ v.length)
      (agree : ∀ i, u.getD (rename p i) false = v.getD i false) :
      (renameCircuit p C).eval u = C.eval v := by
    have preserve (gs : List Gate) (a b : List Bool)
        (lengths : a.length = b.length) (minimum : 9 ≤ b.length)
        (same : ∀ i, a.getD (rename p i) false = b.getD i false) :
        ∀ i, ((gs.map (renameGate p)).foldl step a).getD (rename p i) false =
          (gs.foldl step b).getD i false := by
      induction gs generalizing a b with
      | nil => exact same
      | cons g gs ih =>
        have equalValue :
            (renameGate p g).op.eval ((renameGate p g).inputs.map fun i => a.getD i false) =
              g.op.eval (g.inputs.map fun i => b.getD i false) := by
          congr 1
          simp only [renameGate, List.map_map]
          apply List.map_congr_left
          intro i _
          exact same i
        have lengths' : (step a (renameGate p g)).length = (step b g).length := by
          simp [step, lengths]
        have minimum' : 9 ≤ (step b g).length := by
          simp [step]
          omega
        have same' : ∀ i, (step a (renameGate p g)).getD (rename p i) false =
            (step b g).getD i false := by
          intro i
          by_cases small : i < 9
          · have lhs : rename p i < a.length := by
              simp only [rename, dite_eq_left small]
              have := (p ⟨i,small⟩).isLt
              omega
            have rhs : i < b.length := by omega
            simpa only [step, List.getD_append _ _ _ _ lhs, List.getD_append _ _ _ _ rhs] using same i
          · have sameIndex : rename p i = i := dite_eq_right small
            by_cases before : i < b.length
            · have before' : i < a.length := by omega
              have sameHere := same i
              rw [sameIndex] at sameHere ⊢
              simpa only [step, List.getD_append _ _ _ _ before', List.getD_append _ _ _ _ before] using sameHere
            · have tooLarge : a.length ≤ i := by omega
              rw [sameIndex]
              simp only [step, List.getD_append_right _ _ _ _ tooLarge,
                List.getD_append_right _ _ _ _ (by omega : b.length ≤ i)]
              rw [lengths, equalValue]
        simpa only [List.map_cons, List.foldl_cons] using ih _ _ lengths' minimum' same'
    exact preserve C.gates u v hlen hmin agree C.output

  let permutations : Fin 4 → Fin 9 → Fin 9 := ![
    ![0,1,2,3,4,5,6,7,8], ![0,5,8,3,4,1,7,6,2],
    ![3,2,1,0,4,8,7,6,5], ![3,8,5,0,4,2,6,7,1]]

  let raw : Fin 12 → List (Fin 11) := ![
    [0,1],[0,2],[0,4],[0,6],[1,2],[1,4],[1,5],[1,6],[1,7],[1,8],[4,6],[6,7]]

  let other : Fin 10 → List (Fin 11) := ![
    [],[0],[1],[4],[6],[9],[10],[1,9],[4,9],[6,9]]

  let pinSupport (p : Fin 9 → Fin 9) (i : Fin 11) : Finset (Fin 9) :=
    if hi : i.val < 9 then {p ⟨i.val, hi⟩}
    else if i.val = 9 then {p 0,p 3} else ∅

  let support (p : Fin 9 → Fin 9) (pins : List (Fin 11)) : Finset (Fin 9) :=
    pins.foldr (fun i S => pinSupport p i ∪ S) ∅

  let base (x : Fin 9 → Bool) : List Bool :=
    List.ofFn x ++ [x 0 && x 3]

  let signal (pins : List (Fin 11)) (x : Fin 9 → Bool) : Bool :=
    GateOp.and.eval (pins.map fun i => (base x).getD i.val false)

  let target (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5

  have pin_read (p : Fin 9 → Fin 9) (x : Fin 9 → Bool) (i : Fin 11) :
      (base (fun j => x (p j))).getD i.val false =
        (!decide (i = 10) && decide (∀ j ∈ pinSupport p i, x j = true)) := by
    by_cases small : i.val < 9
    · have ne : i ≠ 10 := by
        intro h; subst i; contradiction
      have hlen : i.val < (List.ofFn (fun j => x (p j))).length := by simpa using small
      change (List.ofFn (fun j => x (p j)) ++ [x (p 0) && x (p 3)]).getD i.val false = _
      rw [List.getD_append _ _ _ _ hlen]
      rw [show (List.ofFn (fun j => x (p j))).getD i.val false = x (p ⟨i.val,small⟩) by
        exact (List.getD_eq_getElem _ _ hlen).trans (List.getElem_ofFn hlen)]
      simp [pinSupport, small, ne]
    · have cases : i = 9 ∨ i = 10 := by
        have := i.isLt
        have hi : i.val = 9 ∨ i.val = 10 := by omega
        exact hi.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
      rcases cases with rfl | rfl
      · simp [base, pinSupport, List.getD_eq_getElem?_getD]
      · simp [base, List.getD_eq_getElem?_getD]

  have signal_eq (p : Fin 9 → Fin 9) (x : Fin 9 → Bool) (pins : List (Fin 11)) :
      signal pins (fun j => x (p j)) =
        (!pins.contains 10 && decide (∀ j ∈ support p pins, x j = true)) := by
    induction pins with
    | nil => simp [signal, GateOp.eval, support]
    | cons i is ih =>
      change ((base (fun j => x (p j))).getD i.val false &&
        signal is (fun j => x (p j))) = _
      rw [pin_read, ih]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        List.contains_eq_mem, List.mem_cons, decide_eq_false_iff_not,
        support, List.foldr_cons, Finset.mem_union, not_or]
      constructor
      · rintro ⟨⟨hne,ha⟩,hm,hb⟩
        exact ⟨⟨Ne.symm hne,hm⟩, fun j h => h.elim (ha j) (hb j)⟩
      · rintro ⟨⟨hne,hm⟩,hh⟩
        exact ⟨⟨Ne.symm hne, fun j hj => hh j (Or.inl hj)⟩, hm,
          fun j hj => hh j (Or.inr hj)⟩

  let sameTest (p : Fin 9 → Fin 9) (a b : List (Fin 11)) : Prop :=
    a.contains 10 = b.contains 10 ∧ (a.contains 10 = false → support p a = support id b)

  letI instSame (p : Fin 9 → Fin 9) (a b : List (Fin 11)) :
      Decidable (sameTest p a b) := inferInstanceAs (Decidable (_ ∧ _))

  let covered (pins : List (Fin 11)) : Prop :=
    ∃ q : Fin 4, (∃ i : Fin 12, sameTest (permutations q) pins (raw i)) ∨
      (∃ i : Fin 10, sameTest (permutations q) pins (other i))

  letI instCovered (pins : List (Fin 11)) : Decidable (covered pins) :=
    inferInstanceAs (Decidable (∃ q : Fin 4, (∃ i : Fin 12, sameTest (permutations q) pins (raw i)) ∨
      (∃ i : Fin 10, sameTest (permutations q) pins (other i))))

  have classified (pins : List (Fin 11)) (length : pins.length ≤ 2) : covered pins := by
    rcases pins with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
    · decide
    · have h : ∀ i : Fin 11, covered [i] := by decide
      exact h i
    · have h : ∀ i j : Fin 11, covered [i,j] := by decide
      exact h i j
    · simp at length

  have target_perm (q : Fin 4) (x : Fin 9 → Bool) :
      target (fun j => x (permutations q j)) = target x := by
    fin_cases q <;> simp [permutations, target] <;> ac_rfl

  have first_perm (q : Fin 4) (x : Fin 9 → Bool) :
      (x (permutations q 0) && x (permutations q 3)) = (x 0 && x 3) := by
    fin_cases q <;> simp [permutations, Bool.and_comm]

  let input (pins : List (Fin 11)) (x : Fin 9 → Bool) : List Bool :=
    base x ++ [signal pins x]

  have input_agree (q : Fin 4) (x : Fin 9 → Bool) (a b : List (Fin 11))
      (h : sameTest (permutations q) a b) :
      ∀ i, (input b x).getD (rename (permutations q) i) false =
        (input a (fun j => x (permutations q j))).getD i false := by
    have sig : signal a (fun j => x (permutations q j)) = signal b x := by
      conv_rhs => change signal b (fun j => x (id j))
      rw [signal_eq, signal_eq]
      change a.contains 10 = b.contains 10 ∧ _ at h
      rcases h with ⟨eqv, seteq⟩
      rw [← eqv]
      cases ha : a.contains 10
      · simp [seteq ha]
      · rfl
    have readRaw (pins : List (Fin 11)) (val : Fin 9 → Bool) (j : Nat) (hj : j < 9) :
        (input pins val).getD j false = val ⟨j,hj⟩ := by
      simp only [input, base, List.append_assoc]
      have hlen : j < (List.ofFn val).length := by simpa using hj
      rw [List.getD_append _ _ _ _ hlen]
      exact (List.getD_eq_getElem _ _ hlen).trans (List.getElem_ofFn hlen)
    intro i
    by_cases small : i < 9
    · rw [show rename (permutations q) i = (permutations q ⟨i,small⟩).val from
        dite_eq_left small, readRaw, readRaw a _ _ small]
    · have large : 9 ≤ i := by omega
      rw [show rename (permutations q) i = i from dite_eq_right small]
      simp only [input, base, List.append_assoc]
      have tails (f : Fin 9 → Bool) (tail : List Bool) :
          (List.ofFn f ++ tail).getD i false = tail.getD (i - 9) false := by
        simpa only [List.length_ofFn] using
          (List.getD_append_right (List.ofFn f) tail false i (by simpa using large))
      rw [tails x, tails (fun j => x (permutations q j)), first_perm, sig]
  have rawMem : ∀ k, raw k ∈ ([[0,1],[0,2],[0,4],[0,6],[1,2],[1,4],[1,5],[1,6],[1,7],[1,8],[4,6],[6,7]] : List (List (Fin 11))) := by decide
  have otherMem : ∀ k, other k ∈ ([[],[0],[1],[4],[6],[9],[10],[1,9],[4,9],[6,9]] : List (List (Fin 11))) := by decide
  intro C pins basis length calculates
  obtain ⟨q, cases⟩ := classified pins length
  let D := renameCircuit (permutations q) C
  have dBasis := rename_basis (permutations q) C basis
  have dSize : D.size = C.size := rename_size _ _
  have computes (b : List (Fin 11)) (h : sameTest (permutations q) pins b) :
      ∀ x, D.eval (input b x) = target x := by
    intro x
    rw [show D.eval (input b x) =
        C.eval (input pins (fun j => x (permutations q j))) from
      rename_eval _ _ _ _ (by simp [input, base]) (by simp [input, base])
        (input_agree q x pins b h)]
    rw [calculates]
    exact target_perm q x
  rw [← dSize]
  rcases cases with ⟨k, h⟩ | ⟨k,h⟩
  · exact proveRaw D (raw k) dBasis (rawMem k) (computes _ h)
  · exact proveOther D (other k) dBasis (otherMem k) (computes _ h)
