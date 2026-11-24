import PEqualNP.Defs

-- Symmetry cut: the graph automorphism 1-5, 2-8, 6-7 fixes 0 and 4, and the second wire is
-- symmetric in its two inputs, so the 13 non-adjacent pairs fall into 8 orbits. Each
-- hypothesis is the step for some orbit representatives.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 3500000 in
theorem PEqualNP.Outside.R_meta_3509_509
    (cubicA : let f : (Fin 9 → Bool) → Bool := fun x =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ i j : Fin 9, (i, j) ∈ ([(1,3), (1,5)] : List (Fin 9 × Fin 9)) →
        ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x i || x j]) = f x) →
          False)
    (cubicB : let f : (Fin 9 → Bool) → Bool := fun x =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ i j : Fin 9, (i, j) ∈ ([(1,8), (2,8)] : List (Fin 9 × Fin 9)) →
        ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x i || x j]) = f x) →
          False)
    (oneQuadratic : let f : (Fin 9 → Bool) → Bool := fun x =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ i j : Fin 9, (i, j) ∈ ([(1,7), (2,6), (3,6)] : List (Fin 9 × Fin 9)) →
        ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x i || x j]) = f x) →
          False)
    (bothQuadratic : let f : (Fin 9 → Bool) → Bool := fun x =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ i j : Fin 9, (i, j) ∈ ([(6,7)] : List (Fin 9 × Fin 9)) →
        ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x i || x j]) = f x) →
          False)
    :
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → ↑x1 * (10 : ℕ) + ↑x2 ∉ [(12 : ℕ), (21 : ℕ), (23 : ℕ), (32 : ℕ), (16 : ℕ), (61 : ℕ), (27 : ℕ), (72 : ℕ), (38 : ℕ), (83 : ℕ), (57 : ℕ), (75 : ℕ), (68 : ℕ), (86 : ℕ), (58 : ℕ), (85 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x12 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)), x12 x1 || x12 x2]) = (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))) → False := by
  intro a b C ha0 ha4 hb0 hb4 hab hnon fan size hC
  let f : (Fin 9 → Bool) → Bool := fun x =>
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  have edgeForm : ∀ x : Fin 9 → Bool,
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) = f x := by
    decide +kernel
  -- the automorphism of the graph fixing 0 and 4
  let p : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  have p0 : p 0 = 0 := by decide
  have p4 : p 4 = 4 := by decide
  have pp : ∀ i, p (p i) = i := by decide
  have symm : ∀ x : Fin 9 → Bool, f (x ∘ p) = f x := by
    decide +kernel
  let wire : ℕ → ℕ := fun i => if hi : i < 9 then (p ⟨i, hi⟩).val else i
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let move : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun g => ⟨g.op, g.inputs.map wire⟩
  let Rel : List Bool → List Bool → Prop := fun w v =>
    w.length = v.length ∧ 9 ≤ w.length ∧ ∀ i, v.getD (wire i) false = w.getD i false
  have foldMove : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w v : List Bool),
      Rel w v → Rel (gs.foldl step w) ((gs.map move).foldl step v) := by
    intro gs
    induction gs with
    | nil => exact fun _ _ h => h
    | cons g gs ih =>
      intro w v h
      obtain ⟨len, bound, reads⟩ := h
      change Rel (gs.foldl step (step w g)) ((gs.map move).foldl step (step v (move g)))
      apply ih
      have value : (move g).op.eval ((move g).inputs.map fun i => v.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [move, List.map_map, Function.comp_def, reads]
      let b := g.op.eval (g.inputs.map fun i => w.getD i false)
      change Rel (w ++ [b]) (v ++ [(move g).op.eval ((move g).inputs.map fun i => v.getD i false)])
      rw [value]
      change (w ++ [b]).length = (v ++ [b]).length ∧ 9 ≤ (w ++ [b]).length ∧ _
      refine ⟨by simp [len], by simp; omega, ?_⟩
      intro i
      by_cases hi : i < w.length
      · have hw : wire i < v.length := by
          dsimp [wire]
          split
          · rename_i hi9
            exact (p ⟨i, hi9⟩).isLt.trans_le (by omega)
          · omega
        rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hi]
        exact reads i
      · have hwire : wire i = i := by simp [wire, show ¬ i < 9 by omega]
        rw [hwire, List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len]
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map move, wire C.output⟩
  have fanD : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨(fan g' hg').1, by simpa [move] using (fan g' hg').2⟩
  have sizeD : D.size ≤ 13 := by
    change (C.gates.map move).length ≤ 13
    rw [List.length_map]
    exact size
  have evalD (x : Fin 9 → Bool) (ys : List Bool) :
      D.eval (List.ofFn x ++ ys) = C.eval (List.ofFn (x ∘ p) ++ ys) := by
    have base : Rel (List.ofFn (x ∘ p) ++ ys) (List.ofFn x ++ ys) := by
      refine ⟨by simp, by simp, ?_⟩
      intro i
      by_cases hi : i < 9
      · have hw : wire i < 9 := by simp [wire, hi]
        rw [List.getD_append _ _ _ _ (by simpa using hw),
          List.getD_append _ _ _ _ (by simpa using hi)]
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hw),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
        simp only [List.getElem_ofFn, Function.comp_def]
        congr 1
        apply Fin.ext
        simp [wire, hi]
      · rw [show wire i = i by simp [wire, hi],
          List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi),
          List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi)]
        simp
    exact (foldMove C.gates _ _ base).2.2 C.output
  -- every representative case is closed by one of the hypotheses
  have close : ∀ i j : Fin 9, (i, j) ∈ (([(1,3), (1,5)] : List (Fin 9 × Fin 9)) ++ ([(1,8), (2,8)] : List (Fin 9 × Fin 9)) ++ ([(1,7), (2,6), (3,6)] : List (Fin 9 × Fin 9)) ++ ([(6,7)] : List (Fin 9 × Fin 9))) →
      ∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo E → E.size ≤ 13 →
      (∀ x : Fin 9 → Bool, E.eval (List.ofFn x ++ [x 0 || x 4, x i || x j]) = f x) → False := by
    intro i j hr E hE hs he
    simp only [List.mem_append, or_assoc] at hr
    rcases hr with h | h | h | h
    · exact cubicA i j h E hE hs he
    · exact cubicB i j h E hE hs he
    · exact oneQuadratic i j h E hE hs he
    · exact bothQuadratic i j h E hE hs he
  -- the 26 ordered non-adjacent pairs fall into the representative orbits (checked as a Bool)
  have classify : ∀ i j : Fin 9,
      (i == 0 || i == 4 || j == 0 || j == 4 || i == j ||
        ([12, 21, 23, 32, 16, 61, 27, 72, 38, 83, 57, 75, 68, 86, 58, 85] : List ℕ).contains
          (i.val * 10 + j.val) ||
        (([(1,3), (1,5)] : List (Fin 9 × Fin 9)) ++ ([(1,8), (2,8)] : List (Fin 9 × Fin 9)) ++ ([(1,7), (2,6), (3,6)] : List (Fin 9 × Fin 9)) ++ ([(6,7)] : List (Fin 9 × Fin 9))).contains (i, j) || (([(1,3), (1,5)] : List (Fin 9 × Fin 9)) ++ ([(1,8), (2,8)] : List (Fin 9 × Fin 9)) ++ ([(1,7), (2,6), (3,6)] : List (Fin 9 × Fin 9)) ++ ([(6,7)] : List (Fin 9 × Fin 9))).contains (j, i) ||
        (([(1,3), (1,5)] : List (Fin 9 × Fin 9)) ++ ([(1,8), (2,8)] : List (Fin 9 × Fin 9)) ++ ([(1,7), (2,6), (3,6)] : List (Fin 9 × Fin 9)) ++ ([(6,7)] : List (Fin 9 × Fin 9))).contains (p i, p j) || (([(1,3), (1,5)] : List (Fin 9 × Fin 9)) ++ ([(1,8), (2,8)] : List (Fin 9 × Fin 9)) ++ ([(1,7), (2,6), (3,6)] : List (Fin 9 × Fin 9)) ++ ([(6,7)] : List (Fin 9 × Fin 9))).contains (p j, p i)) = true := by
    decide
  have hcl := classify a b
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, or_assoc] at hcl
  have hf : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) = f x :=
    fun x => (hC x).trans (edgeForm x)
  rcases hcl with h | h | h | h | h | h | h | h | h | h
  · exact absurd h ha0
  · exact absurd h ha4
  · exact absurd h hb0
  · exact absurd h hb4
  · exact absurd h hab
  · exact absurd h hnon
  · exact close a b h C fan size hf
  · apply close b a h C fan size
    intro x
    rw [Bool.or_comm (x b) (x a)]
    exact hf x
  · apply close (p a) (p b) h D fanD sizeD
    intro x
    rw [evalD]
    have hc := hf (x ∘ p)
    simp only [Function.comp_def, p0, p4] at hc
    exact hc.trans (symm x)
  · apply close (p b) (p a) h D fanD sizeD
    intro x
    rw [evalD, Bool.or_comm (x (p b)) (x (p a))]
    have hc := hf (x ∘ p)
    simp only [Function.comp_def, p0, p4] at hc
    exact hc.trans (symm x)
