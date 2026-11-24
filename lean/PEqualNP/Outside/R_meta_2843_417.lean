import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reattach the two fixed OR gates, then count the effective reads of input four.
-- Three or more reads: its false restriction is the checked eight-input minor.
-- What is left is the case where input four is read once after the first gate.
theorem PEqualNP.Outside.R_meta_2843_417 :
  (let readers := fun C : Circuit => C.gates.countP fun g =>
      (g.inputs.head? == some 4) || (g.op.eval [true, true] && g.inputs.contains 4)
    ∀ C : Circuit, FanInTwo C → 3 ≤ readers C →
      (∃ x : Fin 8 → Bool, circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 3 ≤ C.size ∧
        circuitFun 8 D = (fun x => circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x))) →
  (∀ (tail : Circuit) (j : Fin 9), FanInTwo tail →
      (∀ x : Fin 9 → Bool, tail.eval (List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x j]) =
        ([((0 : Fin 9), (1 : Fin 9)), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]).any fun e => x e.1 && x e.2) →
      ((if j = 4 then 1 else 0) + tail.gates.countP fun g =>
        (g.inputs.head? == some 4) || (g.op.eval [true, true] && g.inputs.contains 4)) ≤ 1 →
      14 ≤ tail.size) →
  (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12) →
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (9 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) || x4 x2]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (14 : ℕ) ≤ x1.size := by
  intro eliminate sparse minor tail j legal correct
  let readers := fun C : Circuit => C.gates.countP fun g =>
    (g.inputs.head? == some 4) || (g.op.eval [true, true] && g.inputs.contains 4)
  change (∀ C : Circuit, FanInTwo C → 3 ≤ readers C →
      (∃ x : Fin 8 → Bool, circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 3 ≤ C.size ∧
        circuitFun 8 D = (fun x => circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x))) at eliminate
  let C : Circuit := ⟨⟨GateOp.or, [0, 4]⟩ :: ⟨GateOp.or, [9, j.val]⟩ :: tail.gates, tail.output⟩
  let P : Gate → Bool := fun g =>
    (g.inputs.head? == some 4) || (g.op.eval [true, true] && g.inputs.contains 4)
  have key : ∀ i : Fin 9, ((([9, i.val] : List ℕ).head? == some 4) ||
      (GateOp.or.eval [true, true] && ([9, i.val] : List ℕ).contains 4)) = decide (i = 4) := by
    intro i
    fin_cases i <;> rfl
  have count : readers C = 1 + ((if j = 4 then 1 else 0) + tail.gates.countP P) := by
    have e0 : List.countP P ((⟨GateOp.or, [0, 4]⟩ : Gate) :: ⟨GateOp.or, [9, j.val]⟩ :: tail.gates) =
        List.countP P ((⟨GateOp.or, [9, j.val]⟩ : Gate) :: tail.gates) + 1 :=
      List.countP_cons_of_pos rfl
    change List.countP P ((⟨GateOp.or, [0, 4]⟩ : Gate) :: ⟨GateOp.or, [9, j.val]⟩ :: tail.gates) = _
    by_cases hj : j = 4
    · have e1 : List.countP P ((⟨GateOp.or, [9, j.val]⟩ : Gate) :: tail.gates) =
          List.countP P tail.gates + 1 :=
        List.countP_cons_of_pos ((key j).trans (decide_eq_true hj))
      rw [e0, e1, if_pos hj]
      omega
    · have e1 : List.countP P ((⟨GateOp.or, [9, j.val]⟩ : Gate) :: tail.gates) =
          List.countP P tail.gates :=
        List.countP_cons_of_neg (fun h => hj (of_decide_eq_true ((key j).symm.trans h)))
      rw [e0, e1, if_neg hj]
      omega
  by_cases many : 3 ≤ readers C
  · by_contra tooSmall
    have sizeC : C.size = tail.size + 2 := rfl
    have legalC : FanInTwo C := by
      change ∀ g ∈ (⟨GateOp.or, [0, 4]⟩ : Gate) ::
        ⟨GateOp.or, [9, j.val]⟩ :: tail.gates,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by decide⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), Nat.le_refl 2⟩
      · exact legal g hg
    let step (values : List Bool) (gate : Gate) :=
      values ++ [gate.op.eval (gate.inputs.map fun i => values.getD i false)]
    have readInput (x : Fin 9 → Bool) (i : Fin 9) :
        (List.ofFn x).getD i.val false = x i := by
      have bound : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
      simp only [Option.getD_some, List.getElem_ofFn]
    have firstStep (x : Fin 9 → Bool) :
        step (List.ofFn x) ⟨GateOp.or, [0, 4]⟩ = List.ofFn x ++ [x 0 || x 4] := by
      have input0 : (List.ofFn x).getD 0 false = x 0 := readInput x 0
      have input4 : (List.ofFn x).getD 4 false = x 4 := readInput x 4
      change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false,
        (List.ofFn x).getD 4 false]] = _
      rw [input0, input4]
      change List.ofFn x ++ [x 0 || (x 4 || false)] = _
      rw [Bool.or_false]
    have secondStep (x : Fin 9 → Bool) :
        step (List.ofFn x ++ [x 0 || x 4]) ⟨GateOp.or, [9, j.val]⟩ =
          List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x j] := by
      have len : (List.ofFn x).length = 9 := List.length_ofFn
      have input9 : (List.ofFn x ++ [x 0 || x 4]).getD 9 false = (x 0 || x 4) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp
      have inputj : (List.ofFn x ++ [x 0 || x 4]).getD j.val false = x j := by
        have bound : j.val < (List.ofFn x).length := by rw [len]; exact j.isLt
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left bound,
          ← List.getD_eq_getElem?_getD]
        exact readInput x j
      change (List.ofFn x ++ [x 0 || x 4]) ++ [GateOp.or.eval
        [(List.ofFn x ++ [x 0 || x 4]).getD 9 false,
          (List.ofFn x ++ [x 0 || x 4]).getD j.val false]] = _
      rw [input9, inputj]
      change (List.ofFn x ++ [x 0 || x 4]) ++ [x 0 || x 4 || (x j || false)] = _
      rw [Bool.or_false, List.append_assoc]
      rfl
    have correctC (x : Fin 9 → Bool) : circuitFun 9 C x =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
      have unfolded : circuitFun 9 C x = tail.eval (List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x j]) := by
        change (List.foldl step (List.ofFn x) ((⟨GateOp.or, [0, 4]⟩ : Gate) ::
          ⟨GateOp.or, [9, j.val]⟩ :: tail.gates)).getD tail.output false = _
        simp only [List.foldl_cons]
        rw [firstStep, secondStep]
        rfl
      rw [unfolded, correct x]
      simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    have restriction (x : Fin 8 → Bool) :
        circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) x := by
      let ins : Fin 9 → Bool := Fin.insertNth (4 : Fin 9) false x
      have hi (j : Fin 8) : ins ((4 : Fin 9).succAbove j) = x j :=
        Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) (4 : Fin 9) false x j
      have h0 : ins 0 = x 0 := hi 0
      have h1 : ins 1 = x 1 := hi 1
      have h2 : ins 2 = x 2 := hi 2
      have h3 : ins 3 = x 3 := hi 3
      have h4 : ins 4 = false :=
        Fin.insertNth_apply_same (α := fun _ : Fin 9 => Bool) (4 : Fin 9) false x
      have h5 : ins 5 = x 4 := hi 4
      have h6 : ins 6 = x 5 := hi 5
      have h7 : ins 7 = x 6 := hi 6
      have h8 : ins 8 = x 7 := hi 7
      calc
        _ = ((ins 0 && ins 1) || (ins 1 && ins 2) || (ins 2 && ins 3) || (ins 3 && ins 4) ||
          (ins 4 && ins 0) || (ins 0 && ins 5) || (ins 1 && ins 6) || (ins 2 && ins 7) ||
          (ins 3 && ins 8) || (ins 5 && ins 7) || (ins 6 && ins 8) || (ins 8 && ins 5)) := correctC ins
        _ = _ := by simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8,
          Bool.false_and, Bool.and_false, Bool.or_false]
    have notTrue : circuitFun 9 C (Fin.insertNth (4 : Fin 9) false (fun _ => false)) = false :=
      restriction (fun _ => false)
    obtain ⟨D, legalD, saving, evalD⟩ := eliminate C legalC many ⟨_, notTrue⟩
    apply minor
    refine ⟨D, legalD, by omega, ?_⟩
    intro x
    exact (congrFun evalD x).trans (restriction x)
  · have few : (if j = 4 then 1 else 0) + tail.gates.countP P ≤ 1 := by omega
    exact sparse tail j legal correct few
