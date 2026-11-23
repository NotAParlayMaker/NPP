import PEqualNP.Defs

private def wireStep (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wireStep_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (gs.foldl wireStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons,
      List.length_nil]
    omega

private lemma foldl_wireStep_getD_lt (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
    (i : ℕ) (hi : i < w.length) :
    (gs.foldl wireStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi1 : i < (wireStep w g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [ih (wireStep w g) hi1]
    simp only [wireStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma list_eq_take_cons_drop {α : Type*} (l : List α) (j : ℕ) (hj : j < l.length) :
    l = l.take j ++ l[j] :: l.drop (j + 1) := by
  induction j generalizing l with
  | zero =>
    cases l with
    | nil => simp at hj
    | cons a t => simp
  | succ k ih =>
    cases l with
    | nil => simp at hj
    | cons a t =>
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons, List.cons_append]
      congr 1
      exact ih t (by simpa using hj)

private lemma list_set_eq_take_cons_drop {α : Type*} (l : List α) (j : ℕ) (x : α)
    (hj : j < l.length) :
    l.set j x = l.take j ++ x :: l.drop (j + 1) := by
  induction j generalizing l with
  | zero =>
    cases l with
    | nil => simp at hj
    | cons a t => simp
  | succ k ih =>
    cases l with
    | nil => simp at hj
    | cons a t =>
      simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      congr 1
      exact ih t (by simpa using hj)

private lemma mem_set_or {α : Type*} {l : List α} {j : ℕ} {x y : α} (hy : y ∈ l.set j x) :
    y ∈ l ∨ y = x := by
  induction l generalizing j with
  | nil => simp at hy
  | cons a t ih =>
    cases j with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons] at hy
      rcases hy with rfl | h
      · exact Or.inr rfl
      · exact Or.inl (List.mem_cons_of_mem a h)
    | succ k =>
      simp only [List.set_cons_succ, List.mem_cons] at hy
      rcases hy with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases ih h with h1 | h2
        · exact Or.inl (List.mem_cons_of_mem a h1)
        · exact Or.inr h2

theorem PEqualNP.Outside.L_meta_202 :
    ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.FanInTwo { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } ∧ PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } = PEqualNP.MetaComplexity.circuitFun n C := by
  intro n j a h C hFan hgate hh himp
  constructor
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · rcases mem_set_or hg with hg | rfl
      · exact hFan g hg
      · simp
    · simp
  · funext x
    obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hgate
    let xs : List Bool := List.ofFn x
    let g0 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩
    let g1 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩
    let g2 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩
    let G0 : List PEqualNP.CircuitLowerBounds.Gate := C.gates.set j g1
    let Wj : List Bool := (C.gates.take j).foldl wireStep xs
    let W : List Bool := C.gates.foldl wireStep xs
    let W' : List Bool := G0.foldl wireStep xs
    have hxs : xs.length = n := List.length_ofFn
    have hWj_len : Wj.length = n + j := by
      change ((C.gates.take j).foldl wireStep xs).length = n + j
      rw [foldl_wireStep_length, hxs, List.length_take]
      omega
    have hW'_len : W'.length = n + C.size := by
      change (G0.foldl wireStep xs).length = n + C.gates.length
      rw [foldl_wireStep_length, hxs]
      simp [G0]
    have hCg : C.gates = C.gates.take j ++ g0 :: C.gates.drop (j + 1) := by
      have h1 := list_eq_take_cons_drop C.gates j hj
      rw [hgj] at h1
      exact h1
    have hG0 : G0 = C.gates.take j ++ g1 :: C.gates.drop (j + 1) :=
      list_set_eq_take_cons_drop C.gates j g1 hj
    have hW_eq : W = (g0 :: C.gates.drop (j + 1)).foldl wireStep Wj := by
      change C.gates.foldl wireStep xs = _
      conv_lhs => rw [hCg]
      rw [List.foldl_append]
    have hW'_eq : W' = (g1 :: C.gates.drop (j + 1)).foldl wireStep Wj := by
      change G0.foldl wireStep xs = _
      conv_lhs => rw [hG0]
      rw [List.foldl_append]
    have hhWj : h < Wj.length := by omega
    have hWh : W.getD h false = Wj.getD h false := by
      rw [hW_eq]
      exact foldl_wireStep_getD_lt _ Wj h hhWj
    have hW'h : W'.getD h false = Wj.getD h false := by
      rw [hW'_eq]
      exact foldl_wireStep_getD_lt _ Wj h hhWj
    have hLHS : PEqualNP.MetaComplexity.circuitFun n
        { gates := G0 ++ [g2], output := n + C.size } x =
        (W'.getD C.output false || W'.getD h false) := by
      change ((G0 ++ [g2]).foldl wireStep xs).getD (n + C.size) false = _
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (W' ++ [g2.op.eval (g2.inputs.map fun i => W'.getD i false)]).getD (n + C.size) false = _
      rw [← hW'_len, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
      simp [g2, PEqualNP.CircuitLowerBounds.GateOp.eval]
    have hRHS : PEqualNP.MetaComplexity.circuitFun n C x = W.getD C.output false := rfl
    rw [hLHS, hRHS]
    cases hval : Wj.getD h false
    · have hstep : wireStep Wj g1 = wireStep Wj g0 := by
        simp only [wireStep, g1, g0, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons,
          List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, hval]
      have hWW' : W' = W := by
        rw [hW'_eq, hW_eq, List.foldl_cons, List.foldl_cons, hstep]
      rw [hW'h, hval, hWW']
      simp
    · have hWhtrue : (C.wires (List.ofFn x)).getD h false = true := by
        change W.getD h false = true
        rw [hWh, hval]
      have hCout : W.getD C.output false = true := himp x hWhtrue
      rw [hW'h, hval, hCout]
      simp
