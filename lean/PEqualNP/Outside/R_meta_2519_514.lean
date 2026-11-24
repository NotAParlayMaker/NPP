import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_2519_514
    (compile : ∀ C : Circuit, FanInTwo C → ∃ (B : BinaryCircuit) (p : Bool),
      (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) ∧ B.size + notCount C ≤ C.size ∧
      ∀ w : List Bool, w.length = 17 → (B.eval (w ++ [false]) != p) = C.eval w)
    (signedBound : ∀ (P : Circuit) (B : BinaryCircuit) (p : Bool),
      Monotone2 P → P.size = 8 →
      (∀ x : Fin 9 → Bool, (P.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
      (∀ x : Fin 9 → Bool, (B.eval (P.wires (List.ofFn x) ++ [false]) != p) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 6 ≤ B.size) :∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ (8 : ℕ) ≤ ↑x3 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan indices first computes
  rcases indices with ⟨a,b,hab,late,ha,hb,only⟩
  let P : Circuit := ⟨C.gates.take 8,0⟩
  let D : Circuit := ⟨C.gates.drop 8,C.output⟩
  let pred : Gate → Bool := fun g =>
    @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)
  have ptrue (g : Gate) : pred g = true ↔ g.op = GateOp.not := by
    exact @decide_eq_true_iff (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)
  have hab' : a.val < b.val := hab
  have n8 : 8 ≤ C.gates.length := by have := a.isLt; omega
  have sizeP : P.size = 8 := by
    change (C.gates.take 8).length = 8
    simp [Nat.min_eq_left n8]
  have prefixNo (g : Gate) (hg : g ∈ P.gates) : g.op ≠ GateOp.not := by
    intro hn
    obtain ⟨i,hi,hg'⟩ := List.mem_iff_getElem.mp hg
    have hi8 : i < 8 := by
      have h : P.gates.length = 8 := sizeP
      omega
    have hiC : i < C.gates.length := by omega
    let j : Fin C.gates.length := ⟨i,hiC⟩
    have same : C.gates.get j = g := by
      change (C.gates.take 8)[i]'hi = g at hg'
      rw [List.getElem_take] at hg'
      exact hg'
    rcases only j (by rw [same]; exact hn) with h | h
    · have eq : i = a.val := congrArg Fin.val h
      omega
    · have eq : i = b.val := congrArg Fin.val h
      omega
  have monoP : Monotone2 P := by
    intro g hg
    have fg := fan g (List.mem_of_mem_take hg)
    rcases fg.1 with h | h | h
    · exact ⟨Or.inl h,fg.2⟩
    · exact ⟨Or.inr h,fg.2⟩
    · exact (prefixNo g hg h).elim
  have countP : P.gates.countP pred = 0 := by
    rw [List.countP_eq_length_filter]
    have hn : P.gates.filter pred = [] :=
      List.filter_eq_nil_iff.mpr (fun g hg ht => prefixNo g hg ((ptrue g).mp ht))
    rw [hn]
    rfl
  have leftPos : 0 < (C.gates.take b.val).countP pred := by
    apply List.countP_pos_iff.mpr
    have hi : a.val < (C.gates.take b.val).length := by
      simp only [List.length_take]
      have := b.isLt
      omega
    refine ⟨C.gates.get a, List.mem_iff_getElem.mpr ⟨a.val,hi,?_⟩,
      (ptrue _).mpr ha⟩
    rw [List.getElem_take]
    rfl
  have rightPos : 0 < (C.gates.drop b.val).countP pred := by
    apply List.countP_pos_iff.mpr
    have hi : 0 < (C.gates.drop b.val).length := by
      simp only [List.length_drop]
      have := b.isLt
      omega
    refine ⟨C.gates.get b, List.mem_iff_getElem.mpr ⟨0,hi,?_⟩,
      (ptrue _).mpr hb⟩
    rw [List.getElem_drop]
    simp only [Nat.add_zero, List.get_eq_getElem]
  have total : 2 ≤ C.gates.countP pred := by
    have sum : C.gates.countP pred =
        (C.gates.take b.val).countP pred + (C.gates.drop b.val).countP pred := by
      rw [← List.countP_append, List.take_append_drop]
    omega
  have charge : 2 ≤ notCount D := by
    have sum : C.gates.countP pred = P.gates.countP pred + D.gates.countP pred := by
      change C.gates.countP pred =
        (C.gates.take 8).countP pred + (C.gates.drop 8).countP pred
      rw [← List.countP_append, List.take_append_drop]
    have hd : D.gates.countP pred = notCount D := List.countP_eq_length_filter
    omega
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g rest ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g rest ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]
        omega
  have lengthP (x : Fin 9 → Bool) : (P.wires (List.ofFn x)).length = 17 := by
    change (P.gates.foldl step (List.ofFn x)).length = _
    rw [length]
    have hz : P.gates.length = 8 := sizeP
    simp [hz]
  have allWires (x : Fin 9 → Bool) :
      D.wires (P.wires (List.ofFn x)) = C.wires (List.ofFn x) := by
    change (C.gates.drop 8).foldl step ((C.gates.take 8).foldl step (List.ofFn x)) =
      C.gates.foldl step (List.ofFn x)
    rw [← List.foldl_append, List.take_append_drop]
  have prefixFront (x : Fin 9 → Bool) :
      (P.wires (List.ofFn x)).getD 9 false = (x 0 || x 2) := by
    have e := first x
    rw [← allWires x] at e
    change (D.gates.foldl step (P.wires (List.ofFn x))).getD 9 false = _ at e
    rw [keep _ _ _ (by rw [lengthP]; decide)] at e
    exact e
  have fanD : FanInTwo D := fun g hg => fan g (List.mem_of_mem_drop hg)
  obtain ⟨B,p,shape,cost,replay⟩ := compile D fanD
  have computeB (x : Fin 9 → Bool) :
      (B.eval (P.wires (List.ofFn x) ++ [false]) != p) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    rw [replay _ (lengthP x)]
    change (D.wires (P.wires (List.ofFn x))).getD C.output false = _
    rw [allWires x]
    exact congrFun computes x
  have bound := signedBound P B p monoP sizeP prefixFront shape computeB
  have hd : D.size = C.size - 8 := List.length_drop
  omega
