import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotPremium

-- After padding the tail, zero and multiple NOT gates are covered by existing bounds.
-- A degenerate second OR can be discarded on the inputs where the first AND is false.
-- The remaining case has an essential NOT and an OR of two distinct raw inputs.
theorem PEqualNP.Outside.R_meta_2938_1
    (noNot : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (0 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))
    (multiple : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → (2 : ℕ) ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))
    (aliasBound : ∀ (j : Fin 10) (C : Circuit), FanInTwo C → C.size ≤ 13 →
      1 ≤ C.gates.countP (fun g => GateOp.rec false false true (fun _ => false) false g.op) →
      ∃ x : Fin 9 → Bool, (x 0 = false ∨ x 2 = false) ∧
        C.eval (List.ofFn x ++ [false] ++ [(List.ofFn x).getD j.val false]) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
        (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x)
    (essential : ∀ (C : Circuit), FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 2)) →
      (∃ i j : Fin 9, i ≠ j ∧ C.gates[1]? = some ⟨.or, [i.val, j.val]⟩) →
      C.size = 15 → EssentialOneNot 9 C.gates (fun _ : Fin 1 => C.output) →
      circuitFun 9 C ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
        (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
∀ (x1 : List (Fin (11 : ℕ))),   x1.length = (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  classical
  intro pins hPins C fan small
  by_contra h
  let F (x : Fin 9 → Bool) :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let firstInput (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 2]
  let secondValue (x : Fin 9 → Bool) :=
    GateOp.or.eval (pins.map fun i => (firstInput x).getD i.val false)
  have correct (x : Fin 9 → Bool) : C.eval (firstInput x ++ [secondValue x]) = F x := by
    by_contra hne
    exact h ⟨x, hne⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have lengthEval (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have preserve (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have hNext : i < (step w g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ih _ hNext]
      exact List.getD_append _ _ _ _ hi
  have realOutput : C.output < 11 + C.gates.length := by
    by_contra no
    let x := fun i : Fin 9 => i == 0 || i == 1
    have hTarget : F x = true := by rfl
    have hp := correct x
    change (C.gates.foldl step (firstInput x ++ [secondValue x])).getD C.output false = F x at hp
    rw [List.getD_eq_default _ _ (by
      rw [lengthEval]
      simpa only [firstInput, List.length_ofFn, List.length_append, List.length_cons,
        List.length_nil, Nat.reduceAdd] using Nat.le_of_not_gt no), hTarget] at hp
    contradiction
  let front : Gate := ⟨.and, [0, 2]⟩
  let next : Gate := ⟨.or, pins.map Fin.val⟩
  let dummy : Gate := ⟨.or, []⟩
  let padding := List.replicate (13 - C.size) dummy
  let D : Circuit := ⟨front :: next :: (C.gates ++ padding), C.output⟩
  have frontStep (x : Fin 9 → Bool) : step (List.ofFn x) front = firstInput x := by
    change List.ofFn x ++ [((List.ofFn x).getD 0 false && ((List.ofFn x).getD 2 false && true))]
      = firstInput x
    simp [firstInput, List.getD_eq_getElem?_getD]
  have validD : FanInTwo D := by
    intro g hg
    change g ∈ front :: next :: (C.gates ++ padding) at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [front]
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [next, hPins]
    rcases List.mem_append.mp hg with hg | hg
    · exact fan g hg
    · have hg' : g = dummy := List.eq_of_mem_replicate hg
      subst g
      simp [dummy]
  have sizeD : D.size = 15 := by
    change (front :: next :: (C.gates ++ List.replicate (13 - C.gates.length) dummy)).length = 15
    change C.gates.length ≤ 13 at small
    simp only [List.length_cons, List.length_append, List.length_replicate]
    omega
  have firstAt (x : Fin 9 → Bool) : (firstInput x).getD 9 false = (x 0 && x 2) := by
    change (List.ofFn x ++ [x 0 && x 2]).getD 9 false = _
    have lens : (List.ofFn x).length = 9 := List.length_ofFn
    rw [List.getD_append_right _ _ _ _ lens.le, lens]
    rfl
  have semanticFirst (x : Fin 9 → Bool) :
      (D.wires (List.ofFn x)).getD 9 false = (x 0 && x 2) := by
    change ((next :: (C.gates ++ padding)).foldl step (step (List.ofFn x) front)).getD 9 false = _
    rw [frontStep, preserve _ _ _ (by simp [firstInput]), firstAt]
  have computesD : circuitFun 9 D = F := by
    funext x
    change ((C.gates ++ padding).foldl step (step (step (List.ofFn x) front) next)).getD C.output false
      = F x
    rw [frontStep, List.foldl_append]
    have nextEq : step (firstInput x) next = firstInput x ++ [secondValue x] := by
      simp only [step, next, List.map_map, Function.comp_def, secondValue]
    rw [nextEq, preserve _ _ _ (by
      rw [lengthEval]
      simpa only [firstInput, List.length_ofFn, List.length_append, List.length_cons,
        List.length_nil, Nat.reduceAdd] using realOutput)]
    exact correct x
  let isNot (g : Gate) : Bool := GateOp.rec false false true (fun _ => false) false g.op
  let count := C.gates.countP isNot
  have countD : D.gates.countP isNot = count := by
    change (front :: next :: (C.gates ++ padding)).countP isNot = count
    have hPad : padding.countP isNot = 0 := by
      apply List.countP_eq_zero.mpr
      intro g hg
      have hg' : g = dummy := List.eq_of_mem_replicate hg
      subst g
      decide
    have hf : isNot front = false := rfl
    have hn : isNot next = false := rfl
    simp only [List.countP_cons, hf, hn, Bool.false_eq_true, ite_false, List.countP_append, hPad, Nat.add_zero]
    rfl
  by_cases none : count = 0
  · exact noNot D validD semanticFirst sizeD (countD.trans none) computesD
  by_cases many : 2 ≤ count
  · exact multiple D validD semanticFirst sizeD (countD ▸ many : 2 ≤ D.gates.countP isNot) computesD
  have one : count = 1 := by omega
  obtain ⟨a, b, hAB⟩ := List.length_eq_two.mp hPins
  have pinValue (x : Fin 9 → Bool) :
      secondValue x = ((firstInput x).getD a.val false || (firstInput x).getD b.val false) := by
    change GateOp.or.eval (pins.map fun i => (firstInput x).getD i.val false) = _
    rw [hAB]
    change ((firstInput x).getD a.val false || ((firstInput x).getD b.val false || false)) = _
    rw [Bool.or_false]
  have clamped (x : Fin 9 → Bool) (hx : x 0 = false ∨ x 2 = false) (i : Fin 11) :
      (firstInput x).getD i.val false = (List.ofFn x).getD i.val false := by
    have hAnd : (x 0 && x 2) = false := by rcases hx with hz | hz <;> simp [hz]
    change (List.ofFn x ++ [x 0 && x 2]).getD i.val false = _
    rw [hAnd]
    by_cases inside : i.val < 9
    · exact List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using inside)
    · have hOutside : (List.ofFn x).length ≤ i.val := by
        simpa only [List.length_ofFn] using Nat.le_of_not_gt inside
      have zero : (List.ofFn x).getD i.val false = false := List.getD_eq_default _ _ hOutside
      rw [List.getD_append_right _ _ _ _ hOutside, zero]
      cases i.val - (List.ofFn x).length <;> rfl
  have rejectAlias (j : Fin 10)
      (aliasEq : ∀ x : Fin 9 → Bool, x 0 = false ∨ x 2 = false →
        secondValue x = (List.ofFn x).getD j.val false) : False := by
    obtain ⟨x, hx, neq⟩ := aliasBound j C fan small (by omega : 1 ≤ count)
    have hAnd : (x 0 && x 2) = false := by rcases hx with hz | hz <;> simp [hz]
    have he := correct x
    change C.eval (List.ofFn x ++ [x 0 && x 2] ++ [secondValue x]) = F x at he
    rw [hAnd, aliasEq x hx] at he
    exact neq he
  let clip (i : Fin 11) : Fin 10 := ⟨min i.val 9, by omega⟩
  have clipEq (x : Fin 9 → Bool) (i : Fin 11) :
      (List.ofFn x).getD (clip i).val false = (List.ofFn x).getD i.val false := by
    change (List.ofFn x).getD (min i.val 9) false = _
    by_cases hi : i.val < 9
    · rw [Nat.min_eq_left hi.le]
    · rw [Nat.min_eq_right (Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simp),
        List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hi)]
  by_cases ha : a.val < 9
  swap
  · apply rejectAlias (clip b)
    intro x hx
    have ea : (List.ofFn x).getD a.val false = false :=
      List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt ha)
    rw [pinValue, clamped x hx a, clamped x hx b, clipEq, ea, Bool.false_or]
  by_cases hb : b.val < 9
  swap
  · apply rejectAlias (clip a)
    intro x hx
    have eb : (List.ofFn x).getD b.val false = false :=
      List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hb)
    rw [pinValue, clamped x hx a, clamped x hx b, clipEq, eb, Bool.or_false]
  by_cases hab : a = b
  · apply rejectAlias (clip a)
    intro x hx
    rw [pinValue, clamped x hx a, clamped x hx b, clipEq, hab, Bool.or_self]
  have genuine : ∃ i j : Fin 9, i ≠ j ∧ D.gates[1]? = some ⟨.or, [i.val, j.val]⟩ := by
    refine ⟨⟨a.val, ha⟩, ⟨b.val, hb⟩, fun eq => hab (Fin.ext (congrArg (fun i : Fin 9 => i.val) eq)), ?_⟩
    change some (⟨.or, pins.map Fin.val⟩ : Gate) = _
    rw [hAB]
    rfl
  have hUnique : D.gates.countP isNot = 1 := countD.trans one
  have isNot_spec (g : Gate) : isNot g = true ↔ g.op = .not := by
    obtain ⟨op, ins⟩ := g
    cases op <;> simp [isNot]
  obtain ⟨g, hg, hNot⟩ := List.countP_pos_iff.mp (show 0 < D.gates.countP isNot by omega)
  obtain ⟨index, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  let q : Fin D.gates.length := ⟨index, hi⟩
  have notq : (D.gates.get q).op = .not := (isNot_spec _).mp hNot
  have qAfter : index ≠ 0 := by
    intro hZero
    subst index
    change isNot front = true at hNot
    contradiction
  have noNotAfter (b : Bool) : (replaceByConst D.gates q.val b).countP isNot = 0 := by
    change (D.gates.set index (constGate b)).countP isNot = 0
    rw [List.countP_set hi, hUnique, hNot]
    cases b <;> rfl
  have onlyNot (i : Fin D.gates.length) (hi' : (D.gates.get i).op = .not) : i = q := by
    by_contra ne
    have neIndex : index ≠ i.val := fun he => ne (Fin.ext he.symm)
    have inBound : i.val < (D.gates.set index (constGate false)).length := by
      simpa only [List.length_set] using i.isLt
    have hit := List.getElem_mem inBound
    have hEq := List.getElem_set_ne neIndex inBound
    change (D.gates.set index (constGate false))[i.val] = D.gates.get i at hEq
    rw [hEq] at hit
    exact (List.countP_eq_zero.mp (noNotAfter false) _ hit) ((isNot_spec _).mpr hi')
  have changes (b : Bool) :
      ChangesSomeOutput 9 D.gates (replaceByConst D.gates q.val b) (fun _ : Fin 1 => D.output) := by
    let E : Circuit := ⟨replaceByConst D.gates q.val b, D.output⟩
    have fanE : FanInTwo E := by
      intro a ha
      rcases List.mem_or_eq_of_mem_set ha with ha | rfl
      · exact validD a ha
      · cases b with
        | false =>
          change GateOp.or ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ ([] : List ℕ).length ≤ 2
          simp
        | true =>
          change GateOp.and ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ ([] : List ℕ).length ≤ 2
          simp
    have sizeE : E.size = 15 := by
      change (D.gates.set index (constGate b)).length = 15
      rw [List.length_set]
      exact sizeD
    have firstE (x : Fin 9 → Bool) : (E.wires (List.ofFn x)).getD 9 false = (x 0 && x 2) := by
      cases index with
      | zero => exact (qAfter rfl).elim
      | succ i =>
        change (((next :: (C.gates ++ padding)).set i (constGate b)).foldl step
          (step (List.ofFn x) front)).getD 9 false = _
        rw [frontStep, preserve _ _ _ (by simp [firstInput]), firstAt]
    have neq : circuitFun 9 E ≠ circuitFun 9 D := by
      rw [computesD]
      exact noNot E fanE firstE sizeE (noNotAfter b)
    obtain ⟨x, hx⟩ := Function.ne_iff.mp neq
    exact ⟨0, x, hx⟩
  have hEssential : EssentialOneNot 9 D.gates (fun _ : Fin 1 => D.output) :=
    ⟨⟨fun _ => q, fun i hi => ⟨0, (onlyNot i hi).symm⟩⟩, q, notq, changes false, changes true⟩
  exact essential D validD semanticFirst genuine sizeD hEssential computesD
