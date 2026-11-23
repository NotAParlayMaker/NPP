import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1322_aux

open PEqualNP.CircuitLowerBounds

private def Allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

-- Invalid reads are false before complementation. Constants are the empty AND and OR.
private def dualGate (m : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if ∀ i ∈ g.inputs, i < m then ⟨.or, g.inputs⟩ else ⟨.and, []⟩
  | .or => ⟨.and, g.inputs.filter fun i => decide (i < m)⟩
  | .not =>
      match g.inputs with
      | [] => ⟨.or, []⟩
      | i :: _ => if i < m then ⟨.not, [i]⟩ else ⟨.or, []⟩
  | _ => ⟨.or, []⟩

private def dualList (m : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => dualGate m g :: dualList (m + 1) gs

private theorem dualGate_allowed (m : ℕ) (g : Gate) (hg : Allowed g) :
    Allowed (dualGate m g) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
      have hf : inputs.length ≤ 2 := hg.2
      by_cases h : ∀ i ∈ inputs, i < m
      · simp only [dualGate, ite_eq_left h]; simp [Allowed, hf]
      · simp only [dualGate, ite_eq_right h]; simp [Allowed]
  | or =>
      have h : (inputs.filter fun i => decide (i < m)).length ≤ 2 :=
        (List.length_filter_le _ _).trans hg.2
      simp [dualGate, Allowed, h]
  | not =>
      cases inputs with
      | nil => simp [dualGate, Allowed]
      | cons i is =>
          by_cases hi : i < m <;> simp [dualGate, hi, Allowed]
  | mod r => simp [dualGate, Allowed]
  | maj => simp [dualGate, Allowed]

private theorem dualGate_not (m : ℕ) (g : Gate) (h : (dualGate m g).op = .not) :
    g.op = .not := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
      by_cases h' : ∀ i ∈ inputs, i < m
      · simp only [dualGate, ite_eq_left h'] at h
        cases h
      · simp only [dualGate, ite_eq_right h'] at h
        cases h
  | or => simp [dualGate] at h
  | not => rfl
  | mod r => simp [dualGate] at h
  | maj => simp [dualGate] at h

private theorem dualList_length (m : ℕ) (gs : List Gate) :
    (dualList m gs).length = gs.length := by
  induction gs generalizing m with
  | nil => rfl
  | cons g gs ih => simp [dualList, ih]

private theorem dualList_allowed (m : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, Allowed g) :
    ∀ g ∈ dualList m gs, Allowed g := by
  induction gs generalizing m with
  | nil => simp [dualList]
  | cons g gs ih =>
      intro g' hg'
      simp only [dualList, List.mem_cons] at hg'
      obtain rfl | hg' := hg'
      · exact dualGate_allowed m g (h _ (by simp))
      · exact ih (m + 1) (fun g₀ hg₀ => h g₀ (by simp [hg₀])) g' hg'

private theorem dualList_not (m : ℕ) (gs : List Gate) (i : ℕ) (g' : Gate)
    (hGet : (dualList m gs)[i]? = some g') (hNot : g'.op = .not) :
    ∃ g, gs[i]? = some g ∧ g.op = .not := by
  induction gs generalizing m i with
  | nil => simp [dualList] at hGet
  | cons g gs ih =>
      cases i with
      | zero =>
          have hEq : dualGate m g = g' := Option.some.inj hGet
          exact ⟨g, rfl, dualGate_not m g (hEq.symm ▸ hNot)⟩
      | succ i =>
          exact ih (m + 1) i hGet

private theorem dualRead (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (w.map (!·)).getD i false = !(w.getD i false) := by
  have hi' : i < (w.map (!·)).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi, List.getElem_map]

private theorem dualOr (w : List Bool) (is : List ℕ) :
    ((is.filter fun i => decide (i < w.length)).map fun i =>
      (w.map (!·)).getD i false).all id =
      !((is.map fun i => w.getD i false).any id) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      by_cases hi : i < w.length
      · simp only [List.filter_cons, hi, decide_true, ite_true, List.map_cons, List.all_cons,
          List.any_cons, id_eq, Bool.not_or, dualRead w i hi, ih]
      · have h0 := List.getD_eq_default w false (Nat.le_of_not_lt hi)
        simp only [List.filter_cons, hi, decide_false, List.map_cons, List.any_cons,
          id_eq, h0, Bool.false_or]
        exact ih

private theorem dualAndValid (w : List Bool) (is : List ℕ)
    (hv : ∀ i ∈ is, i < w.length) :
    (is.map fun i => (w.map (!·)).getD i false).any id =
      !((is.map fun i => w.getD i false).all id) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      have hi : i < w.length := hv i (by simp)
      have ht : ∀ j ∈ is, j < w.length := fun j hj => hv j (by simp [hj])
      simp only [List.map_cons, List.any_cons, List.all_cons, id_eq, dualRead w i hi,
        ih ht, Bool.not_and]

private theorem origAndInvalid (w : List Bool) (is : List ℕ)
    (hv : ¬ ∀ i ∈ is, i < w.length) :
    (is.map fun i => w.getD i false).all id = false := by
  push Not at hv
  obtain ⟨i, hi, hInvalid⟩ := hv
  apply List.all_eq_false.mpr
  refine ⟨w.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
  rw [List.getD_eq_default w false hInvalid]
  decide

private def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem dualValue (w : List Bool) (g : Gate) (hg : Allowed g) :
    gateValue (w.map (!·)) (dualGate w.length g) = !(gateValue w g) := by
  obtain ⟨op, is⟩ := g
  cases op with
  | and =>
      by_cases hv : ∀ i ∈ is, i < w.length
      · simp only [dualGate, ite_eq_left hv, gateValue, GateOp.eval]
        exact dualAndValid w is hv
      · simp only [dualGate, ite_eq_right hv, gateValue, GateOp.eval, origAndInvalid w is hv]
        rfl
  | or => simpa [dualGate, gateValue, GateOp.eval] using dualOr w is
  | not =>
      cases is with
      | nil => rfl
      | cons i is =>
          by_cases hi : i < w.length
          · simp [dualGate, hi, gateValue, GateOp.eval]
          · simp [dualGate, hi, gateValue, GateOp.eval]
  | mod r => simp [Allowed] at hg
  | maj => simp [Allowed] at hg

private def step (w : List Bool) (g : Gate) : List Bool := w ++ [gateValue w g]

private theorem step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      simp [ih, step_length, Nat.add_comm, Nat.add_left_comm]

private theorem fold_dual (gs : List Gate) (w : List Bool) (h : ∀ g ∈ gs, Allowed g) :
    (dualList w.length gs).foldl step (w.map (!·)) = (gs.foldl step w).map (!·) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      have hStep : step (w.map (!·)) (dualGate w.length g) = (step w g).map (!·) := by
        simp [step, dualValue w g (h g (by simp))]
      simp only [dualList, List.foldl_cons, hStep, ← step_length w g]
      exact ih (step w g) (fun g₀ hg₀ => h g₀ (by simp [hg₀]))

end PEqualNP.Outside.L_meta_1322_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1322_aux in
theorem PEqualNP.Outside.L_meta_1322 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.length = gates.length ∧ (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), gates'[i]? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ (w : ℕ) (x : Fin n → Bool), w < n + gates.length → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates', 0⟩ (List.ofFn x)).getD w false = !((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun p : Fin n => !x p))).getD w false) := by
  intro n gates h
  refine ⟨dualList n gates, dualList_length n gates, dualList_allowed n gates h,
    dualList_not n gates, ?_⟩
  intro i x hi
  let w := List.ofFn fun p : Fin n => !x p
  have hw : w.length = n := List.length_ofFn
  have hmap : w.map (!·) = List.ofFn x := by
    simp [w, List.map_ofFn, Function.comp_def]
  change ((dualList n gates).foldl step (List.ofFn x)).getD i false =
    !((gates.foldl step w).getD i false)
  rw [← hmap, ← hw, fold_dual gates w h]
  apply dualRead
  simpa [fold_length, hw] using hi
