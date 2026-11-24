import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2022_511
    (normalize : ∀ (ins : List ℕ) (d : ℕ), ins.length ≤ 2 → 9 ∈ ins → 9 < d →
      (∀ i ∈ ins, i ≤ 24) → ∃ j : ℕ, j < d ∧ j ≤ 24 ∧
        ∀ w : List Bool, w.length = d →
          GateOp.or.eval (ins.map fun i => w.getD i false) =
            GateOp.or.eval ([9,j].map fun i => w.getD i false))
    (aliasCase : ∀ (pre post : List Gate) (o : ℕ),
      pre.length + post.length ≤ 13 → (∀ g ∈ pre, 9 ∉ g.inputs) →
      let C : Circuit := ⟨pre ++ ⟨GateOp.or,[9,9]⟩ :: post, o⟩
      FanInTwo C → o ≤ 24 → o ≠ 9 →
      (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 && x 6]) ≠ (x (0 : Fin 9) && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (liveCase : ∀ (pre post : List Gate) (o j : ℕ),
      pre.length + post.length ≤ 13 → (∀ g ∈ pre, 9 ∉ g.inputs) →
      j ≠ 9 → j < 10 + pre.length →
      let C : Circuit := ⟨pre ++ ⟨GateOp.or,[9,j]⟩ :: post, o⟩
      FanInTwo C → o ≤ 24 → o ≠ 9 →
      (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 && x 6]) ≠ (x (0 : Fin 9) && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :∀ (x1 x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 : List ℕ) (x4 : ℕ),   x1.length + x2.length ≤ (13 : ℕ) →     (∀ x6 ∈ x1, (9 : ℕ) ∉ x6.inputs) →       (9 : ℕ) ∈ x3 →         have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x3 : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := x4 : PEqualNP.CircuitLowerBounds.Circuit };         PEqualNP.MetaComplexity.FanInTwo x8 → x4 ≤ (24 : ℕ) → x4 ≠ (9 : ℕ) → (∀ x12 ∈ x8.gates, ∀ x14 ∈ x12.inputs, x14 ≤ (24 : ℕ)) → ∃ (x13 : Fin (9 : ℕ) → Bool), x8.eval (List.ofFn x13 ++ [x13 (4 : Fin (9 : ℕ)) && x13 (6 : Fin (9 : ℕ))]) ≠ (x13 (0 : Fin (9 : ℕ)) && x13 (1 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (2 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (3 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (4 : Fin (9 : ℕ)) || x13 (4 : Fin (9 : ℕ)) && x13 (0 : Fin (9 : ℕ)) || x13 (0 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (6 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (5 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (6 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (8 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ))) := by
  classical
  intro pre post ins o small first mem
  let g : Gate := ⟨GateOp.or,ins⟩
  let C : Circuit := ⟨pre ++ g :: post,o⟩
  change FanInTwo C → o ≤ 24 → o ≠ 9 →
    (∀ a ∈ C.gates, ∀ i ∈ a.inputs, i ≤ 24) → _
  intro fan out out9 wires
  have gin : g ∈ C.gates := List.mem_append_right _ (List.mem_cons_self)
  have arity : ins.length ≤ 2 := (fan g gin).2
  obtain ⟨j, earlier, j24, same⟩ :=
    normalize ins (10 + pre.length) arity mem (by omega) (wires g gin)
  let g' : Gate := ⟨GateOp.or,[9,j]⟩
  let D : Circuit := ⟨pre ++ g' :: post,o⟩
  have fan' : FanInTwo D := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact fan a (List.mem_append_left _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
      · exact fan a (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have wires' : ∀ a ∈ D.gates, ∀ i ∈ a.inputs, i ≤ 24 := by
    intro a ha i hi
    rcases List.mem_append.mp ha with h | h
    · exact wires a (List.mem_append_left _ h) i hi
    · rcases List.mem_cons.mp h with rfl | h
      · change i ∈ [9,j] at hi
        rcases List.mem_cons.mp hi with rfl | hi
        · decide
        · have e : i = j := List.mem_singleton.mp hi
          exact e.symm ▸ j24
      · exact wires a (List.mem_append_right _ (List.mem_cons_of_mem _ h)) i hi
  let step := fun (w : List Bool) (a : Gate) =>
    w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]
  have length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons a rest ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have eq (x : Fin 9 → Bool) :
      D.eval (List.ofFn x ++ [x 4 && x 6]) = C.eval (List.ofFn x ++ [x 4 && x 6]) := by
    let row := List.ofFn x ++ [x 4 && x 6]
    let w := pre.foldl step row
    have len : w.length = 10 + pre.length := by
      rw [length]
      simp [row]
    change ((pre ++ g' :: post).foldl step row).getD o false =
      ((pre ++ g :: post).foldl step row).getD o false
    simp only [List.foldl_append, List.foldl_cons]
    change (post.foldl step (w ++ [GateOp.or.eval ([9,j].map fun i => w.getD i false)])).getD o false =
      (post.foldl step (w ++ [GateOp.or.eval (ins.map fun i => w.getD i false)])).getD o false
    rw [same w len]
  have witness : ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 && x 6]) ≠ (x (0 : Fin 9) && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    by_cases h : j = 9
    · subst j
      exact aliasCase pre post o small first fan' out out9 wires'
    · exact liveCase pre post o j small first h earlier fan' out out9 wires'
  obtain ⟨x,hx⟩ := witness
  exact ⟨x,fun h => hx ((eq x).trans h)⟩
