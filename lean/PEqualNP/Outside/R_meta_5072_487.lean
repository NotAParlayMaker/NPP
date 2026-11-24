import Mathlib
import PEqualNP.Defs

open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_5072_487
    (small :
      let f := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ C : Circuit, FanInTwo C → C.size ≤ 14 → ∃ x, C.eval (List.ofFn x) ≠ f x)
    (clean : ∀ (n : ℕ) (C : Circuit),
      let notGate := fun (g : Gate) => g.op.eval [false] && !g.op.eval [true]
      let D : Circuit := ⟨C.gates.map fun g => ⟨g.op,g.inputs.take (cond (notGate g) 1 2)⟩, C.output⟩
      IsMinimalCircuit n C → (∃ x y, circuitFun n C x ≠ circuitFun n C y) →
      circuitFun n D = circuitFun n C ∧ D.output < n+D.size ∧ ReadsBack n D ∧
        ∀ g ∈ D.gates, g.inputs.length = cond (notGate g) 1 2)
    (low :
      let f := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let nG := fun (g : Gate) => g.op.eval [false] && !g.op.eval [true]
      ∀ C : Circuit, let W := C.output :: C.gates.flatMap Gate.inputs
      let N := (C.gates.filter nG).length
      FanInTwo C → C.size = 14 → C.output = 23 → ReadsBack 10 C →
      (∀ g ∈ C.gates, g.inputs.length = cond (nG g) 1 2) → (∀ w < 24, w ∈ W) → 2 ≤ W.count 9 →
      (C.gates.countP fun g => g.inputs.contains 0) ≤ 2 → (C.gates.countP fun g => g.inputs.contains 3) ≤ 2 →
      (∀ i : Fin 9, ∃ x, C.eval (List.ofFn x ++ [x i]) ≠ f x) →
      1 ≤ N → N ≤ 2 → ∃ x, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x)
    (high :
      let f := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let nG := fun (g : Gate) => g.op.eval [false] && !g.op.eval [true]
      ∀ C : Circuit, let W := C.output :: C.gates.flatMap Gate.inputs
      let N := (C.gates.filter nG).length
      FanInTwo C → C.size = 14 → C.output = 23 → ReadsBack 10 C →
      (∀ g ∈ C.gates, g.inputs.length = cond (nG g) 1 2) → (∀ w < 24, w ∈ W) → 2 ≤ W.count 9 →
      (C.gates.countP fun g => g.inputs.contains 0) ≤ 2 → (C.gates.countP fun g => g.inputs.contains 3) ≤ 2 →
      (∀ i : Fin 9, ∃ x, C.eval (List.ofFn x ++ [x i]) ≠ f x) →
      3 ≤ N → N ≤ 4 → ∃ x, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => x2.op.eval [Bool.false] && !x2.op.eval [Bool.true]; have x3 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) (x4 : ℕ) => Decidable.decide (x3.inputs[(0 : ℕ)]? = Option.some x4) || !x2 x3 && x3.inputs.contains x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → (x4.output ≤ (24 : ℕ) ∧ ∀ x7 ∈ x4.gates, ∀ x9 ∈ x7.inputs, x9 ≤ (24 : ℕ)) → (∀ x8 < (24 : ℕ), x8 ∈ x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) → (9 : ℕ) + (List.filter x2 x4.gates).length + ∑ x9 ∈ Finset.range (24 : ℕ), (List.count x9 (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) - (1 : ℕ)) ≤ (14 : ℕ) → (1 : ℕ) ≤ (List.filter x2 x4.gates).length → (2 : ℕ) ≤ List.count (9 : ℕ) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) → (∀ (x12 : Fin (9 : ℕ)), ∃ (x13 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x13 ++ [x13 x12]) ≠ x1 x13) → List.countP (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x3 x13 (0 : ℕ)) x4.gates ≤ (2 : ℕ) → List.countP (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => x3 x14 (3 : ℕ)) x4.gates ≤ (2 : ℕ) → ∃ (x15 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x15 ++ [x15 (0 : Fin (9 : ℕ)) || x15 (3 : Fin (9 : ℕ))]) ≠ x1 x15 := by
  dsimp only
  intro C fan size _within used budget pos seedTwo copy r0 r3
  let f := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let notGate (g : Gate) := g.op.eval [false] && !g.op.eval [true]
  let trim (g : Gate) : Gate := ⟨g.op,g.inputs.take (cond (notGate g) 1 2)⟩
  let D : Circuit := ⟨C.gates.map trim,C.output⟩
  let W := C.output :: C.gates.flatMap Gate.inputs
  let W' := D.output :: D.gates.flatMap Gate.inputs
  let N := (C.gates.filter notGate).length
  let N' := (D.gates.filter notGate).length
  change 9 + N + ∑ w ∈ Finset.range 24, (W.count w-1) ≤ 14 at budget
  change 1 ≤ N at pos
  change 2 ≤ W.count 9 at seedTwo
  change (∀ w < 24, w ∈ W) at used
  change (∀ i : Fin 9, ∃ x, C.eval (List.ofFn x ++ [x i]) ≠ f x) at copy
  change ∃ x, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x
  by_contra! computes
  have appended (x : Fin 9 → Bool) (b : Bool) : List.ofFn (Fin.snoc x b : Fin 10 → Bool) = List.ofFn x ++ [b] := by
    rw [List.ofFn_succ']
    simp
    change (Fin.snoc x b : Fin 10 → Bool) (Fin.last 9) = b
    exact Fin.snoc_last _ _
  have f0 : f (fun _ => false) = false := rfl
  have f1 : f (fun _ => true) = true := rfl
  have nc : ∃ x y, circuitFun 10 C x ≠ circuitFun 10 C y := by
    refine ⟨Fin.snoc (fun _ => false) false,Fin.snoc (fun _ => true) true,?_⟩
    change C.eval (List.ofFn (Fin.snoc (fun _ : Fin 9 => false) false)) ≠
      C.eval (List.ofFn (Fin.snoc (fun _ : Fin 9 => true) true))
    have left := computes (fun _ => false)
    have right := computes (fun _ => true)
    change C.eval (List.ofFn (fun _ : Fin 9 => false) ++ [false]) = f (fun _ => false) at left
    change C.eval (List.ofFn (fun _ : Fin 9 => true) ++ [true]) = f (fun _ => true) at right
    rw [appended,appended,left,right,f0,f1]
    decide
  have minimum : IsMinimalCircuit 10 C := by
    refine ⟨fan,?_⟩
    intro E efan same
    by_contra! smaller
    let first : Gate := ⟨.or,[0,3]⟩
    let full : Circuit := ⟨first :: E.gates,E.output⟩
    have fullFan : FanInTwo full := by
      intro g hg
      change g ∈ first :: E.gates at hg
      rcases List.mem_cons.mp hg with rfl | mem
      · exact ⟨Or.inr (Or.inl rfl),by decide⟩
      · exact efan g mem
    have fullSize : full.size ≤ 14 := by
      change E.gates.length+1 ≤ 14
      change E.gates.length < C.size at smaller
      omega
    obtain ⟨x,differs⟩ := small full fullFan fullSize
    apply differs
    let xs : Fin 10 → Bool := Fin.snoc x (x 0 || x 3)
    have sameAt := congrFun same xs
    change E.eval (List.ofFn xs) = C.eval (List.ofFn xs) at sameAt
    have evalFull : full.eval (List.ofFn x) = E.eval (List.ofFn x ++ [x 0 || x 3]) := by
      have a : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD_eq_getElem?_getD]
      have b : (List.ofFn x).getD 3 false = x 3 := by simp [List.getD_eq_getElem?_getD]
      change E.eval (List.ofFn x ++ [(List.ofFn x).getD 0 false ||
        ((List.ofFn x).getD 3 false || false)]) = _
      simp only [a,b,Bool.or_false]
    rw [evalFull,← appended x (x 0 || x 3),sameAt,show List.ofFn xs = List.ofFn x ++ [x 0 || x 3] from appended _ _]
    exact computes x
  obtain ⟨same, outRange, earlier, arity⟩ := clean 10 C minimum nc
  have evalSame (x : Fin 9 → Bool) (b : Bool) : D.eval (List.ofFn x ++ [b]) = C.eval (List.ofFn x ++ [b]) := by
    have h := congrFun same (Fin.snoc x b : Fin 10 → Bool)
    change D.eval (List.ofFn (Fin.snoc x b : Fin 10 → Bool)) = C.eval (List.ofFn (Fin.snoc x b : Fin 10 → Bool)) at h
    rw [appended] at h
    exact h
  have dSize : D.size = 14 := by
    change (C.gates.map trim).length = 14
    rwa [List.length_map]
  have dLen : D.gates.length = 14 := dSize
  have dFan : FanInTwo D := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    change a.op ∈ _ ∧ (a.inputs.take (cond (notGate a) 1 2)).length ≤ 2
    exact ⟨(fan a ha).1,(List.length_take_le _ _).trans (by cases notGate a <;> decide)⟩
  have negEq : N' = N := by
    change ((C.gates.map trim).filter notGate).length = _
    rw [List.filter_map,List.length_map]
    rfl
  have under (i : ℕ) (g : Gate) (hg : g ∈ D.gates) (hi : i ∈ g.inputs) : i < 23 := by
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨jValid,_⟩ := List.getElem?_eq_some_iff.mp hj
    have eq : gateAt D j = g := by
      change (D.gates[j]?).getD ⟨.or,[]⟩ = g
      rw [hj]
      rfl
    have lt := earlier j jValid i (eq.symm ▸ hi)
    omega
  have allBelow (w : ℕ) (hw : w ∈ W') : w < 24 := by
    rcases List.mem_cons.mp hw with rfl | hw
    · change D.output < 10+D.size at outRange
      omega
    · obtain ⟨g,hg,hi⟩ := List.mem_flatMap.mp hw
      exact Nat.lt_trans (under w g hg hi) (by decide)
  have subsetAux (gs : List Gate) : List.Sublist ((gs.map trim).flatMap Gate.inputs) (gs.flatMap Gate.inputs) := by
    induction gs with
    | nil => exact List.Sublist.refl _
    | cons g gs ih =>
      simp only [List.map_cons,List.flatMap_cons]
      exact (List.take_sublist _ _).append ih
  have subset : List.Sublist W' W := (subsetAux C.gates).cons_cons _
  have noDrop (w : ℕ) : W'.count w ≤ W.count w := subset.count_le w
  have normSlots (l : List Gate) (h : ∀ g ∈ l, g.inputs.length = cond (notGate g) 1 2) :
      (l.flatMap Gate.inputs).length + (l.filter notGate).length = 2*l.length := by
    induction l with
    | nil => rfl
    | cons g l ih =>
      have tail := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      have head := h g List.mem_cons_self
      simp only [List.flatMap_cons,List.length_append,List.filter_cons,List.length_cons]
      cases flag : notGate g <;> simp [flag] at head tail ⊢ <;> omega
  have normLength : W'.length + N' = 29 := by
    have q := normSlots D.gates arity
    change (D.gates.flatMap Gate.inputs).length + 1 + N' = 29
    omega
  have sumRel (l : List ℕ) : (∑ w ∈ Finset.range 24, l.count w) = l.countP (fun w => decide (w < 24)) := by
    rw [← Finset.sum_filter_count_eq_countP (fun w : ℕ => w < 24) l]
    symm
    apply Finset.sum_subset
    · intro w hw
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hw).2
    · intro w h hw
      apply List.count_eq_zero_of_not_mem
      intro mem
      exact hw (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr mem,Finset.mem_range.mp h⟩)
  have normSum : (∑ w ∈ Finset.range 24, W'.count w) = W'.length := by
    rw [sumRel,List.countP_eq_length_filter]
    rw [List.filter_eq_self.mpr (fun w hw => decide_eq_true (allBelow w hw))]
  have budgetAdd : (∑ w ∈ Finset.range 24, (W.count w-1)) + 24 = ∑ w ∈ Finset.range 24, W.count w := by
    calc
      (∑ w ∈ Finset.range 24, (W.count w-1)) + 24 = ∑ w ∈ Finset.range 24, (W.count w-1+1) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = ∑ w ∈ Finset.range 24, W.count w := by
        apply Finset.sum_congr rfl
        intro w hw
        exact Nat.sub_add_cancel (List.count_pos_iff.mpr (used w (Finset.mem_range.mp hw)))
  have sums : (∑ w ∈ Finset.range 24, W'.count w) = ∑ w ∈ Finset.range 24, W.count w := by
    have less : (∑ w ∈ Finset.range 24, W'.count w) ≤ ∑ w ∈ Finset.range 24, W.count w :=
      Finset.sum_le_sum (fun w _ => noDrop w)
    omega
  have counts (w : ℕ) (hw : w < 24) : W'.count w = W.count w :=
    (Finset.sum_eq_sum_iff_of_le (fun w _ => noDrop w)).mp sums w (Finset.mem_range.mpr hw)
  have used' (w : ℕ) (hw : w < 24) : w ∈ W' := by
    apply List.count_pos_iff.mp
    rw [counts w hw]
    exact List.count_pos_iff.mpr (used w hw)
  have newest : D.output = 23 := by
    rcases List.mem_cons.mp (used' 23 (by decide)) with output | other
    · exact output.symm
    · obtain ⟨g,hg,hi⟩ := List.mem_flatMap.mp other
      exact (Nat.lt_irrefl _ (under _ g hg hi)).elim
  have seedTwo' : 2 ≤ W'.count 9 := by simpa only [counts 9 (by decide)] using seedTwo
  have seedRepeats : 1 ≤ ∑ w ∈ Finset.range 24, (W.count w-1) := by
    have h : W.count 9-1 ≤ ∑ w ∈ Finset.range 24, (W.count w-1) :=
      Finset.single_le_sum (f := fun w => W.count w-1) (fun _ _ => Nat.zero_le _) (by decide)
    omega
  have maximum : N' ≤ 4 := by omega
  have active (w : ℕ) : (D.gates.countP fun g => g.inputs.contains w) =
      C.gates.countP (fun g => decide (g.inputs[0]? = some w) || (!notGate g && g.inputs.contains w)) := by
    change ((C.gates.map trim).countP fun g => g.inputs.contains w) = _
    simp only [List.countP_eq_length_filter,List.filter_map,List.length_map]
    apply congrArg List.length
    apply List.filter_congr
    intro g hg
    have len := (fan g hg).2
    change (g.inputs.take (cond (notGate g) 1 2)).contains w =
      (decide (g.inputs[0]? = some w) || (!notGate g && g.inputs.contains w))
    cases flag : notGate g with
    | false =>
      simp only [Bool.cond_false,Bool.not_false,Bool.true_and,List.take_of_length_le len]
      cases g.inputs <;> simp [List.contains_cons,eq_comm]
    | true =>
      simp only [Bool.cond_true,Bool.not_true,Bool.false_and,Bool.or_false]
      cases g.inputs <;> simp [List.contains_cons,eq_comm]
  have read0' : (D.gates.countP fun g => g.inputs.contains 0) ≤ 2 := by rw [active]; exact r0
  have read3' : (D.gates.countP fun g => g.inputs.contains 3) ≤ 2 := by rw [active]; exact r3
  have noCopies (i : Fin 9) : ∃ x, D.eval (List.ofFn x ++ [x i]) ≠ f x := by
    obtain ⟨x,h⟩ := copy i
    exact ⟨x,by rwa [evalSame]⟩
  have minimumNot : 1 ≤ N' := negEq.symm ▸ pos
  have final : ∃ x, D.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x := by
    by_cases few : N' ≤ 2
    · exact low D dFan dSize newest earlier arity used' seedTwo' read0' read3' noCopies minimumNot few
    · have enough : 3 ≤ N' := by omega
      exact high D dFan dSize newest earlier arity used' seedTwo' read0' read3' noCopies enough maximum
  obtain ⟨x,contr⟩ := final
  exact contr ((evalSame x _).trans (computes x))
