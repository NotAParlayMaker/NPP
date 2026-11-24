import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3200_418
    (early : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : Fin C.gates.length),
      C.gates.length = 15 →
      PEqualNP.MetaComplexity.FanInTwo C →
      C.gates[0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ →
      (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      C.output < 24 →
      p.val = 6 → p < q → q.val ≤ 10 →
      (C.gates.get p).op = PEqualNP.CircuitLowerBounds.GateOp.not →
      (C.gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not →
      (∀ j : Fin C.gates.length, (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        j = p ∨ j = q) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (late : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : Fin C.gates.length),
      C.gates.length = 15 →
      PEqualNP.MetaComplexity.FanInTwo C →
      C.gates[0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ →
      (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      C.output < 24 →
      p.val = 6 → p < q → 11 ≤ q.val →
      (C.gates.get p).op = PEqualNP.CircuitLowerBounds.GateOp.not →
      (C.gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not →
      (∀ j : Fin C.gates.length, (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        j = p ∨ j = q) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (6 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan negations first computes
  by_contra tooSmall
  change ¬ 16 ≤ C.gates.length at tooSmall
  have budget : C.gates.length ≤ 15 := by omega
  obtain ⟨p, q, pq, pIndex, pNot, qNot, onlyNot⟩ := negations
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let clamp (g : Gate) : Gate := ⟨g.op, g.inputs.map (min 24)⟩
  let front : Gate := ⟨.or, [0, 2]⟩
  let zero : Gate := ⟨.or, []⟩
  have lengthRun (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_nil, List.length_cons]
      omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g)]
      · exact List.getD_append _ _ _ _ hi
      · simp [step]; omega
  have clampRun (gs : List Gate) (w : List Bool) (bound : w.length + gs.length ≤ 24) :
      (gs.map clamp).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have wl : w.length < 24 := by simp only [List.length_cons] at bound; omega
      have reads (i : ℕ) : w.getD (min 24 i) false = w.getD i false := by
        by_cases hi : i ≤ 24
        · rw [min_eq_right hi]
        · rw [min_eq_left (by omega : 24 ≤ i),
            List.getD_eq_default _ _ (by omega : w.length ≤ 24),
            List.getD_eq_default _ _ (by omega : w.length ≤ i)]
      have sameStep : step w (clamp g) = step w g := by
        simp only [step, clamp, List.map_map, Function.comp_def, reads]
      simp only [List.map_cons, List.foldl_cons, sameStep]
      apply ih
      simp only [step, List.length_append, List.length_nil, List.length_cons] at bound ⊢
      omega
  have padding (k : ℕ) (w : List Bool) (i : ℕ) :
      ((List.replicate k zero).foldl step w).getD i false = w.getD i false := by
    induction k generalizing w with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, List.foldl_cons, ih]
      change (w ++ [false]).getD i false = w.getD i false
      by_cases hi : i < w.length
      · exact List.getD_append _ _ _ _ hi
      · rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [List.getD_eq_default _ _ (by omega : w.length ≤ i)]
        cases i - w.length <;> rfl
  cases gatesEq : C.gates with
  | nil =>
    have hp := p.isLt
    simp [gatesEq] at hp
  | cons g tail =>
    have lengthC : C.gates.length = tail.length + 1 := by simp [gatesEq]
    let gates := front :: (tail.map clamp ++ List.replicate (15 - C.gates.length) zero)
    let D : Circuit := ⟨gates, C.output⟩
    have lengthD : D.gates.length = 15 := by
      simp only [D, gates, List.length_cons, List.length_append, List.length_map, List.length_replicate]
      omega
    have frontD : D.gates[0]? = some front := rfl
    have fanD : FanInTwo D := by
      intro a ha
      change a ∈ front :: (tail.map clamp ++ List.replicate (15 - C.gates.length) zero) at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [front]
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        have h := fan b (by rw [gatesEq]; exact List.mem_cons_of_mem _ hb)
        simpa [clamp] using h
      · obtain rfl := List.eq_of_mem_replicate ha
        simp [zero]
    have bounded : ∀ a ∈ D.gates, ∀ i ∈ a.inputs, i ≤ 24 := by
      intro a ha i hi
      change a ∈ front :: (tail.map clamp ++ List.replicate (15 - C.gates.length) zero) at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [front] at hi
        omega
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        exact min_le_left _ _
      · obtain rfl := List.eq_of_mem_replicate ha
        simp [zero] at hi
    have unchanged (x : Fin 9 → Bool) (i : ℕ) :
        (D.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false := by
      let w := List.ofFn x
      have wl : w.length = 9 := List.length_ofFn
      have firstValue :
          g.op.eval (g.inputs.map fun j => w.getD j false) = (x 0 || x 2) := by
        have h := first x
        unfold Circuit.wires at h
        rw [gatesEq, List.foldl_cons] at h
        change (tail.foldl step (step w g)).getD 9 false = _ at h
        have len : (step w g).length = 10 := by simp [step, wl]
        rw [keep _ _ _ (by omega)] at h
        have h' : (step w g).getD w.length false = (x 0 || x 2) := by
          simpa only [wl] using h
        change (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).getD
          w.length false = _ at h'
        rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self] at h'
        exact h'
      have getInput (j : Fin 9) : w.getD j.val false = x j := by
        rw [List.getD_eq_getElem _ _ (by simp [wl])]
        exact List.getElem_ofFn _
      have stepEq : step w front = step w g := by
        unfold step
        rw [firstValue]
        simp only [front, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
          List.any_nil, id_eq, Bool.or_false]
        change w ++ [w.getD (0 : Fin 9).val false || w.getD (2 : Fin 9).val false] = _
        rw [getInput, getInput]
      have len : (step w g).length = 10 := by simp [step, wl]
      change ((gates.foldl step w)).getD i false = (C.gates.foldl step w).getD i false
      rw [gatesEq]
      simp only [gates, List.foldl_cons, stepEq, List.foldl_append, padding]
      rw [clampRun tail (step w g) (by omega)]
    have outputBound : D.output < 24 := by
      by_contra! ho
      let x : Fin 9 → Bool := fun _ => true
      have hx := congrFun computes x
      change C.eval (List.ofFn x) = true at hx
      have hlen : (D.wires (List.ofFn x)).length = 24 := by
        unfold Circuit.wires
        change (D.gates.foldl step (List.ofFn x)).length = 24
        rw [lengthRun, List.length_ofFn, lengthD]
      have hf : D.eval (List.ofFn x) = false :=
        List.getD_eq_default _ _ (by omega)
      rw [show D.eval (List.ofFn x) = C.eval (List.ofFn x) from unchanged x C.output, hx] at hf
      contradiction
    let liftIndex (i : Fin C.gates.length) : Fin D.gates.length :=
      ⟨i.val, by have := i.isLt; omega⟩
    have gateOp (i : Fin D.gates.length) (hi : 0 < i.val) (hc : i.val < C.gates.length) :
        (D.gates.get i).op = (C.gates.get ⟨i.val, hc⟩).op := by
      have ht : i.val - 1 < tail.length := by omega
      cases i with
      | mk i ib =>
        cases i with
        | zero => simp at hi
        | succ j =>
          change (front :: (tail.map clamp ++ List.replicate (15 - C.gates.length) zero))[j + 1].op =
            (C.gates[j + 1]).op
          simp only [List.getElem_cons_succ]
          rw [List.getElem_append_left (by simpa using ht), List.getElem_map]
          have hright : C.gates[j+1] = tail[j]'(by simpa using ht) := by
            simp [gatesEq]
          rw [hright]
    have liftNot (i : Fin C.gates.length) (hi : 0 < i.val)
        (hn : (C.gates.get i).op = GateOp.not) :
        (D.gates.get (liftIndex i)).op = GateOp.not := by
      rw [gateOp (liftIndex i) hi i.isLt]
      exact hn
    have pPositive : 0 < p.val := by omega
    have qPositive : 0 < q.val := by
      have : p.val < q.val := pq
      omega
    have onlyNotD (i : Fin D.gates.length) (hi : (D.gates.get i).op = GateOp.not) :
        i = liftIndex p ∨ i = liftIndex q := by
      have ip : 0 < i.val := by
        by_contra! hz
        have he : i = ⟨0, by omega⟩ := Fin.ext (by change i.val = 0; omega)
        rw [he] at hi
        change GateOp.or = GateOp.not at hi
        contradiction
      have hc : i.val < C.gates.length := by
        by_contra! h
        have hz : (D.gates.get i).op = GateOp.or := by
          cases i with
          | mk i ib =>
            cases i with
            | zero => simp at ip
            | succ j =>
              change (front :: (tail.map clamp ++ List.replicate (15 - C.gates.length) zero))[j + 1].op = _
              simp only [List.getElem_cons_succ]
              change C.gates.length ≤ j + 1 at h
              have htail : (tail.map clamp).length ≤ j := by simp; omega
              rw [List.getElem_append_right htail]
              simp [zero]
        rw [hz] at hi
        contradiction
      have hn := (gateOp i ip hc).symm.trans hi
      rcases onlyNot ⟨i.val, hc⟩ hn with h | h
      · exact Or.inl (Fin.ext (congrArg (fun a : Fin C.gates.length => a.val) h))
      · exact Or.inr (Fin.ext (congrArg (fun a : Fin C.gates.length => a.val) h))
    have mismatch : ∃ x : Fin 9 → Bool, D.eval (List.ofFn x) ≠
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) := by
      by_cases hq : q.val ≤ 10
      · exact early D (liftIndex p) (liftIndex q) lengthD fanD frontD bounded outputBound pIndex pq hq (liftNot p pPositive pNot) (liftNot q qPositive qNot) onlyNotD
      · exact late D (liftIndex p) (liftIndex q) lengthD fanD frontD bounded outputBound pIndex pq
          (by change 11 ≤ q.val; omega) (liftNot p pPositive pNot)
          (liftNot q qPositive qNot) onlyNotD
    obtain ⟨x, hx⟩ := mismatch
    apply hx
    rw [show D.eval (List.ofFn x) = circuitFun 9 C x from unchanged x C.output, computes]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
