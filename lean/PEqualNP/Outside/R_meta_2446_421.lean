import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2446_421
    (mandatory :
      let readGate := fun (g : PEqualNP.CircuitLowerBounds.Gate) (v : ℕ) =>
        (g.op = .not ∧ g.inputs.head? = some v) ∨ (g.op ≠ .not ∧ v ∈ g.inputs)
      let target := fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))
      ∀ p ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x p.1 || x p.2]) = target x) → ∀ v : Fin 9, ∃ g ∈ C.gates, readGate g v.val)
    (remaining :
      let readGate := fun (g : PEqualNP.CircuitLowerBounds.Gate) (v : ℕ) =>
        (g.op = .not ∧ g.inputs.head? = some v) ∨ (g.op ≠ .not ∧ v ∈ g.inputs)
      let target := fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))
      ∀ p ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x p.1 || x p.2]) = target x) → (∀ v : Fin 9, ∃ g ∈ C.gates, readGate g v.val) → False) :
    ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x5 : Fin (9 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 x1.1 || x5 x1.2)) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x3.size := by
  let target := fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))
  let advance := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserve : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : Nat),
      i < w.length → (gs.foldl advance w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i hi; rfl
    | cons g gs ih =>
      intro w i hi
      change (gs.foldl advance (advance w g)).getD i false = w.getD i false
      rw [ih (advance w g) i (by simp [advance]; omega)]
      exact List.getD_append _ _ _ _ hi
  change ∀ p ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))],
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x p.1 || x p.2)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = target → 16 ≤ C.size
  intro p hp C hFan hPref hOutput
  by_contra hLarge
  cases hg : C.gates with
  | nil =>
    let x : Fin 9 → Bool := fun _ => true
    have hz := hPref x
    change (C.gates.foldl advance (List.ofFn x)).getD 9 false = (x p.1 || x p.2) at hz
    rw [hg, List.foldl_nil] at hz
    rw [List.getD_eq_default _ _ (by simp)] at hz
    simp [x] at hz
  | cons first tail =>
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨tail, C.output⟩
    have hFanD : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g h
      exact hFan g (by rw [hg]; exact List.mem_cons_of_mem _ h)
    have hSizeD : D.size ≤ 14 := by
      change tail.length ≤ 14
      change ¬16 ≤ C.gates.length at hLarge
      rw [hg, List.length_cons] at hLarge
      omega
    have hCompute : ∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x p.1 || x p.2]) = target x := by
      intro x
      let w := List.ofFn x
      have hw : w.length = 9 := by simp [w]
      have unfolded : C.wires w = tail.foldl advance (advance w first) := by
        change C.gates.foldl advance w = tail.foldl advance (advance w first)
        exact congrArg (fun gs => gs.foldl advance w) hg
      have firstValue : (advance w first).getD 9 false = (x p.1 || x p.2) := by
        have h := hPref x
        change (C.wires w).getD 9 false = (x p.1 || x p.2) at h
        rw [unfolded, preserve _ _ _ (by simp [advance, hw])] at h
        exact h
      have appended : advance w first = w ++ [x p.1 || x p.2] := by
        have lookup : (advance w first).getD 9 false =
            first.op.eval (first.inputs.map fun i => w.getD i false) := by
          rw [← hw]
          simp [advance]
        change w ++ [first.op.eval (first.inputs.map fun i => w.getD i false)] =
          w ++ [x p.1 || x p.2]
        rw [← lookup, firstValue]
      have h := congrFun hOutput x
      change (C.wires w).getD C.output false = target x at h
      rw [unfolded, appended] at h
      exact h
    exact remaining p hp D hFanD hSizeD hCompute (mandatory p hp D hCompute)

