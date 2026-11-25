import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.SplitCount

-- Normalize any Monotone2 circuit to a size-minimal IsAO2 circuit (proving ReadsBack,
-- exact binary fan-in, and positive-degree vertex peeling directly), then split
-- high-minimum-degree girth-5+ graphs into clean ANDs, one-hot-on dirty ANDs,
-- and one-hot-off dirty ANDs.
theorem PEqualNP.Outside.R_meta_606_271
    (cleanCase : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit),
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty →
      IsLeastAO G C →
      junk G C = ∅ →
      G.edgeFinset.card ≤ c * (C.size + 1))
    (oneHotDirtyCase : ∃ d c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit),
      (∀ v : Fin n, G.degree v = 0 ∨ d ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty →
      IsLeastAO G C →
      (∃ j ∈ junk G C, ∃ v : Fin n, gateVal n C j (unitInput v) = true) →
      G.edgeFinset.card ≤ c * (C.size + 1))
    (pairDirtyCase : ∃ d c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit),
      (∀ v : Fin n, G.degree v = 0 ∨ d ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty →
      IsLeastAO G C →
      (junk G C).Nonempty →
      (∀ j ∈ junk G C, ∀ v : Fin n, gateVal n C j (unitInput v) = false) →
      G.edgeFinset.card ≤ c * (C.size + 1)) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      G.edgeFinset.card ≤ c * (D.size + 1) := by
  classical
  letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  -- Basic GateOp.eval facts without invoking simp on project definitions
  have hEvalAnd : ∀ bs : List Bool, GateOp.and.eval bs = bs.all id := fun _ => rfl
  have hEvalOr : ∀ bs : List Bool, GateOp.or.eval bs = bs.any id := fun _ => rfl
  have hEvalAndNil : GateOp.and.eval [] = true := by decide
  have hEvalOrNil : GateOp.or.eval [] = false := by decide
  have hEvalAndOne : ∀ b : Bool, GateOp.and.eval [b] = b := by decide
  have hEvalOrOne : ∀ b : Bool, GateOp.or.eval [b] = b := by decide
  -- Basic wire step and foldl properties
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hWiresEq : ∀ (C : Circuit) (xs : List Bool), C.wires xs = C.gates.foldl step xs :=
    fun _ _ => rfl
  have hEvalEq : ∀ (C : Circuit) (xs : List Bool),
      C.eval xs = (C.gates.foldl step xs).getD C.output false := fun _ _ => rfl
  have hFoldLen : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have hFoldPrefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ i (by simp [step]; omega)]
      simp only [step]
      rw [List.getD_append _ _ _ _ hi]
  have hGetDOob : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    exact List.getD_eq_default w false hi
  have hGetDSnocLt : ∀ (w : List Bool) (b : Bool) (i : ℕ), i < w.length →
      (w ++ [b]).getD i false = w.getD i false := by
    intro w b i hi
    exact List.getD_append w [b] false i hi
  have hGetDSnocEq : ∀ (w : List Bool) (b : Bool), (w ++ [b]).getD w.length false = b := by
    intro w b
    rw [List.getD_append_right w [b] false w.length (le_refl _)]
    simp
  have hGetDSnocGt : ∀ (w : List Bool) (b : Bool) (i : ℕ), w.length < i →
      (w ++ [b]).getD i false = false := by
    intro w b i hi
    exact hGetDOob (w ++ [b]) i (by simp; omega)
  have hMonoOp : ∀ {C : Circuit} {g : Gate}, Monotone2 C → g ∈ C.gates →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro C g hM hg
    have h1 := hM g hg
    refine ⟨?_, h1.2⟩
    have hmem : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := h1.1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hGateAtEq : ∀ {C : Circuit} {k : ℕ} (hk : k < C.gates.length), gateAt C k = C.gates[k]'hk := by
    intro C k hk
    dsimp only [gateAt]
    rw [List.getD_eq_getElem C.gates _ hk]
  have hListSplit : ∀ (gs : List Gate) (k : ℕ) (hk : k < gs.length),
      gs = gs.take k ++ [gs[k]'hk] ++ gs.drop (k + 1) := by
    intro gs k hk
    calc gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
      _ = gs.take k ++ ((gs[k]'hk) :: gs.drop (k + 1)) := by rw [List.drop_eq_getElem_cons hk]
      _ = gs.take k ++ [gs[k]'hk] ++ gs.drop (k + 1) := by rw [List.append_assoc, List.singleton_append]
  -- Gate rewrites
  let shiftDown : ℕ → ℕ → ℕ := fun t i => if t < i then i - 1 else i
  let rwFalse : ℕ → Gate → Gate := fun t g =>
    if t ∈ g.inputs then
      if g.op = GateOp.and then ⟨GateOp.or, []⟩
      else ⟨GateOp.or, (g.inputs.filter (fun i => decide (i ≠ t))).map (shiftDown t)⟩
    else ⟨g.op, g.inputs.map (shiftDown t)⟩
  let rwTrue : ℕ → Gate → Gate := fun t g =>
    if t ∈ g.inputs then
      if g.op = GateOp.or then ⟨GateOp.and, []⟩
      else ⟨GateOp.and, (g.inputs.filter (fun i => decide (i ≠ t))).map (shiftDown t)⟩
    else ⟨g.op, g.inputs.map (shiftDown t)⟩
  let rwCopy : ℕ → ℕ → Gate → Gate := fun t w g =>
    ⟨g.op, g.inputs.map (fun i => if i = t then w else shiftDown t i)⟩
  let rwSubF : ℕ → Gate → Gate := fun v0 g =>
    if v0 ∈ g.inputs then
      if g.op = GateOp.and then ⟨GateOp.or, []⟩
      else ⟨GateOp.or, g.inputs.filter (fun i => decide (i ≠ v0))⟩
    else g
  -- Monotonicity preservation of each gate rewrite
  have hRwFalseMono : ∀ t g, (g.op = GateOp.and ∨ g.op = GateOp.or) → g.inputs.length ≤ 2 →
      ((rwFalse t g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (rwFalse t g).inputs.length ≤ 2) := by
    intro t g hop hlen
    dsimp only [rwFalse]
    by_cases hm : t ∈ g.inputs
    · rw [if_pos hm]
      by_cases ha : g.op = GateOp.and
      · rw [if_pos ha]; simp
      · rw [if_neg ha]
        refine ⟨by simp, ?_⟩
        rw [List.length_map]
        exact (List.length_filter_le _ _).trans hlen
    · rw [if_neg hm]
      refine ⟨?_, by rw [List.length_map]; exact hlen⟩
      rcases hop with h | h <;> simp [h]
  have hRwTrueMono : ∀ t g, (g.op = GateOp.and ∨ g.op = GateOp.or) → g.inputs.length ≤ 2 →
      ((rwTrue t g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (rwTrue t g).inputs.length ≤ 2) := by
    intro t g hop hlen
    dsimp only [rwTrue]
    by_cases hm : t ∈ g.inputs
    · rw [if_pos hm]
      by_cases ho : g.op = GateOp.or
      · rw [if_pos ho]; simp
      · rw [if_neg ho]
        refine ⟨by simp, ?_⟩
        rw [List.length_map]
        exact (List.length_filter_le _ _).trans hlen
    · rw [if_neg hm]
      refine ⟨?_, by rw [List.length_map]; exact hlen⟩
      rcases hop with h | h <;> simp [h]
  have hRwCopyMono : ∀ t w g, (g.op = GateOp.and ∨ g.op = GateOp.or) → g.inputs.length ≤ 2 →
      ((rwCopy t w g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (rwCopy t w g).inputs.length ≤ 2) := by
    intro t w g hop hlen
    dsimp only [rwCopy]
    refine ⟨?_, by rw [List.length_map]; exact hlen⟩
    rcases hop with h | h <;> simp [h]
  have hRwSubFMono : ∀ v0 g, (g.op = GateOp.and ∨ g.op = GateOp.or) → g.inputs.length ≤ 2 →
      ((rwSubF v0 g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (rwSubF v0 g).inputs.length ≤ 2) := by
    intro v0 g hop hlen
    dsimp only [rwSubF]
    by_cases hm : v0 ∈ g.inputs
    · rw [if_pos hm]
      by_cases ha : g.op = GateOp.and
      · rw [if_pos ha]; simp
      · rw [if_neg ha]
        exact ⟨by simp, (List.length_filter_le _ _).trans hlen⟩
    · rw [if_neg hm]
      refine ⟨?_, hlen⟩
      rcases hop with h | h <;> simp [h]
  -- One-gate semantic equivalences
  have hAnyFilterFalse : ∀ (bs : List ℕ) (t : ℕ) (f g : ℕ → Bool),
      f t = false → (∀ i, i ≠ t → g i = f i) →
      (bs.filter (fun i => decide (i ≠ t))).any g = bs.any f := by
    intro bs t f g hft hfg
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨i, ⟨hi, hne⟩, hgi⟩
      exact ⟨i, hi, (hfg i hne).symm.trans hgi⟩
    · rintro ⟨i, hi, hfi⟩
      have hne : i ≠ t := by
        intro heq
        rw [heq, hft] at hfi
        cases hfi
      exact ⟨i, ⟨hi, hne⟩, (hfg i hne).trans hfi⟩
  have hAllFilterTrue : ∀ (bs : List ℕ) (t : ℕ) (f g : ℕ → Bool),
      f t = true → (∀ i, i ≠ t → g i = f i) →
      (bs.filter (fun i => decide (i ≠ t))).all g = bs.all f := by
    intro bs t f g hft hfg
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_filter, decide_eq_true_eq]
    constructor
    · intro h i hi
      by_cases hne : i = t
      · rw [hne]; exact hft
      · exact (hfg i hne).symm.trans (h i ⟨hi, hne⟩)
    · rintro h i ⟨hi, hne⟩
      exact (hfg i hne).trans (h i hi)
  have hRwFalseStep : ∀ (t : ℕ) (g : Gate) (A B : List Bool),
      (g.op = GateOp.and ∨ g.op = GateOp.or) →
      A.getD t false = false →
      (∀ i, i ≠ t → B.getD (shiftDown t i) false = A.getD i false) →
      (rwFalse t g).op.eval ((rwFalse t g).inputs.map fun i => B.getD i false) =
        g.op.eval (g.inputs.map fun i => A.getD i false) := by
    intro t g A B hop hAt hAB
    dsimp only [rwFalse]
    by_cases hm : t ∈ g.inputs
    · rw [if_pos hm]
      rcases hop with ha | ho
      · rw [if_pos ha, ha]
        dsimp only
        rw [List.map_nil, hEvalOrNil, hEvalAnd]
        symm
        rw [List.all_eq_false]
        exact ⟨false, List.mem_map.mpr ⟨t, hm, hAt⟩, by decide⟩
      · have hne : g.op ≠ GateOp.and := by rw [ho]; decide
        rw [if_neg hne, ho, hEvalOr, hEvalOr, List.map_map, List.any_map, List.any_map]
        exact hAnyFilterFalse g.inputs t (fun i => A.getD i false)
          (fun i => B.getD (shiftDown t i) false) hAt hAB
    · rw [if_neg hm]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact hAB i (fun heq => hm (heq ▸ hi))
  have hRwTrueStep : ∀ (t : ℕ) (g : Gate) (A B : List Bool),
      (g.op = GateOp.and ∨ g.op = GateOp.or) →
      A.getD t false = true →
      (∀ i, i ≠ t → B.getD (shiftDown t i) false = A.getD i false) →
      (rwTrue t g).op.eval ((rwTrue t g).inputs.map fun i => B.getD i false) =
        g.op.eval (g.inputs.map fun i => A.getD i false) := by
    intro t g A B hop hAt hAB
    dsimp only [rwTrue]
    by_cases hm : t ∈ g.inputs
    · rw [if_pos hm]
      rcases hop with ha | ho
      · have hne : g.op ≠ GateOp.or := by rw [ha]; decide
        rw [if_neg hne, ha, hEvalAnd, hEvalAnd, List.map_map, List.all_map, List.all_map]
        exact hAllFilterTrue g.inputs t (fun i => A.getD i false)
          (fun i => B.getD (shiftDown t i) false) hAt hAB
      · rw [if_pos ho, ho]
        dsimp only
        rw [List.map_nil, hEvalAndNil, hEvalOr]
        symm
        rw [List.any_eq_true]
        exact ⟨true, List.mem_map.mpr ⟨t, hm, hAt⟩, by decide⟩
    · rw [if_neg hm]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact hAB i (fun heq => hm (heq ▸ hi))
  have hRwCopyStep : ∀ (t w : ℕ) (g : Gate) (A B : List Bool),
      B.getD w false = A.getD t false →
      (∀ i, i ≠ t → B.getD (shiftDown t i) false = A.getD i false) →
      (rwCopy t w g).op.eval ((rwCopy t w g).inputs.map fun i => B.getD i false) =
        g.op.eval (g.inputs.map fun i => A.getD i false) := by
    intro t w g A B hwt hAB
    dsimp only [rwCopy]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    dsimp only [Function.comp_apply]
    by_cases hi : i = t
    · rw [if_pos hi, hi]; exact hwt
    · rw [if_neg hi]; exact hAB i hi
  have hRwSubFStep : ∀ (v0 : ℕ) (g : Gate) (A B : List Bool),
      (g.op = GateOp.and ∨ g.op = GateOp.or) →
      A.getD v0 false = false →
      (∀ i, i ≠ v0 → B.getD i false = A.getD i false) →
      (rwSubF v0 g).op.eval ((rwSubF v0 g).inputs.map fun i => B.getD i false) =
        g.op.eval (g.inputs.map fun i => A.getD i false) := by
    intro v0 g A B hop hAv hAB
    dsimp only [rwSubF]
    by_cases hm : v0 ∈ g.inputs
    · rw [if_pos hm]
      rcases hop with ha | ho
      · rw [if_pos ha, ha]
        dsimp only
        rw [List.map_nil, hEvalOrNil, hEvalAnd]
        symm
        rw [List.all_eq_false]
        exact ⟨false, List.mem_map.mpr ⟨v0, hm, hAv⟩, by decide⟩
      · have hne : g.op ≠ GateOp.and := by rw [ho]; decide
        rw [if_neg hne, ho, hEvalOr, hEvalOr, List.any_map, List.any_map]
        exact hAnyFilterFalse g.inputs v0 (fun i => A.getD i false)
          (fun i => B.getD i false) hAv hAB
    · rw [if_neg hm]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hAB i (fun heq => hm (heq ▸ hi))
  -- Foldl preservation on initial segment (equal lists) and tail (deleted index t)
  have hPreFalse : ∀ (pre : List Gate) (t : ℕ) (w : List Bool),
      w.length + pre.length ≤ t →
      (∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or) →
      (pre.map (rwFalse t)).foldl step w = pre.foldl step w := by
    intro pre
    induction pre with
    | nil => intro _ _ _ _; rfl
    | cons g gs ih =>
      intro t w hlen hop
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hgt : w.length < t := by simp at hlen; omega
      have hst : step w (rwFalse t g) = step w g := by
        dsimp only [step]
        congr 2
        apply hRwFalseStep t g w w (hop g (List.mem_cons_self ..)) (hGetDOob w t (by omega))
        intro i hi
        dsimp only [shiftDown]
        by_cases hlt : t < i
        · rw [if_pos hlt, hGetDOob w (i - 1) (by omega), hGetDOob w i (by omega)]
        · rw [if_neg hlt]
      rw [hst]
      apply ih t (step w g) (by simp [step] at hlen ⊢; omega)
        (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
  have hPostFalse : ∀ (post : List Gate) (t : ℕ) (A B : List Bool),
      A.length = B.length + 1 → t < A.length → A.getD t false = false →
      (∀ i, i ≠ t → B.getD (shiftDown t i) false = A.getD i false) →
      (∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or) →
      (∀ i, i ≠ t → ((post.map (rwFalse t)).foldl step B).getD (shiftDown t i) false =
        (post.foldl step A).getD i false) := by
    intro post
    induction post with
    | nil => intro _ _ _ _ _ _ hAB _; exact hAB
    | cons g gs ih =>
      intro t A B hlen ht hAt hAB hop
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hv : (rwFalse t g).op.eval ((rwFalse t g).inputs.map fun i => B.getD i false) =
          g.op.eval (g.inputs.map fun i => A.getD i false) :=
        hRwFalseStep t g A B (hop g (List.mem_cons_self ..)) hAt hAB
      apply ih t (step A g) (step B (rwFalse t g))
      · simp [step]; omega
      · simp [step]; omega
      · dsimp only [step]; rw [hGetDSnocLt A _ t ht]; exact hAt
      · intro i hi
        dsimp only [step]
        rw [hv]
        by_cases hlt : i < A.length
        · rw [hGetDSnocLt A _ i hlt]
          have hsi : shiftDown t i < B.length := by dsimp only [shiftDown]; split_ifs <;> omega
          rw [hGetDSnocLt B _ _ hsi]
          exact hAB i hi
        · by_cases heq : i = A.length
          · rw [heq, hGetDSnocEq A _]
            have hsi : shiftDown t A.length = B.length := by
              dsimp only [shiftDown]; rw [if_pos ht]; omega
            rw [hsi, hGetDSnocEq B _]
          · have hgt : A.length < i := by omega
            rw [hGetDSnocGt A _ i hgt]
            have hsi : B.length < shiftDown t i := by
              dsimp only [shiftDown]; rw [if_pos (by omega)]; omega
            rw [hGetDSnocGt B _ _ hsi]
      · exact fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')
  have hPostTrue : ∀ (post : List Gate) (t : ℕ) (A B : List Bool),
      A.length = B.length + 1 → t < A.length → A.getD t false = true →
      (∀ i, i ≠ t → B.getD (shiftDown t i) false = A.getD i false) →
      (∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or) →
      (∀ i, i ≠ t → ((post.map (rwTrue t)).foldl step B).getD (shiftDown t i) false =
        (post.foldl step A).getD i false) := by
    intro post
    induction post with
    | nil => intro _ _ _ _ _ _ hAB _; exact hAB
    | cons g gs ih =>
      intro t A B hlen ht hAt hAB hop
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hv : (rwTrue t g).op.eval ((rwTrue t g).inputs.map fun i => B.getD i false) =
          g.op.eval (g.inputs.map fun i => A.getD i false) :=
        hRwTrueStep t g A B (hop g (List.mem_cons_self ..)) hAt hAB
      apply ih t (step A g) (step B (rwTrue t g))
      · simp [step]; omega
      · simp [step]; omega
      · dsimp only [step]; rw [hGetDSnocLt A _ t ht]; exact hAt
      · intro i hi
        dsimp only [step]
        rw [hv]
        by_cases hlt : i < A.length
        · rw [hGetDSnocLt A _ i hlt]
          have hsi : shiftDown t i < B.length := by dsimp only [shiftDown]; split_ifs <;> omega
          rw [hGetDSnocLt B _ _ hsi]
          exact hAB i hi
        · by_cases heq : i = A.length
          · rw [heq, hGetDSnocEq A _]
            have hsi : shiftDown t A.length = B.length := by
              dsimp only [shiftDown]; rw [if_pos ht]; omega
            rw [hsi, hGetDSnocEq B _]
          · have hgt : A.length < i := by omega
            rw [hGetDSnocGt A _ i hgt]
            have hsi : B.length < shiftDown t i := by
              dsimp only [shiftDown]; rw [if_pos (by omega)]; omega
            rw [hGetDSnocGt B _ _ hsi]
      · exact fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')
  have hPostCopy : ∀ (post : List Gate) (t w : ℕ) (A B : List Bool),
      A.length = B.length + 1 → w < t → t < A.length → B.getD w false = A.getD t false →
      (∀ i, i ≠ t → B.getD (shiftDown t i) false = A.getD i false) →
      (∀ i, ((post.map (rwCopy t w)).foldl step B).getD (if i = t then w else shiftDown t i) false =
        (post.foldl step A).getD i false) := by
    intro post
    induction post with
    | nil =>
      intro t w A B _ _ _ hwt hAB i
      by_cases hi : i = t
      · rw [if_pos hi, hi]; exact hwt
      · rw [if_neg hi]; exact hAB i hi
    | cons g gs ih =>
      intro t w A B hlen hwtLt ht hwt hAB
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hv : (rwCopy t w g).op.eval ((rwCopy t w g).inputs.map fun i => B.getD i false) =
          g.op.eval (g.inputs.map fun i => A.getD i false) :=
        hRwCopyStep t w g A B hwt hAB
      apply ih t w (step A g) (step B (rwCopy t w g))
      · simp [step]; omega
      · exact hwtLt
      · simp [step]; omega
      · dsimp only [step]
        rw [hGetDSnocLt B _ w (by omega), hGetDSnocLt A _ t ht]
        exact hwt
      · intro i hi
        dsimp only [step]
        rw [hv]
        by_cases hlt : i < A.length
        · rw [hGetDSnocLt A _ i hlt]
          have hsi : shiftDown t i < B.length := by dsimp only [shiftDown]; split_ifs <;> omega
          rw [hGetDSnocLt B _ _ hsi]
          exact hAB i hi
        · by_cases heq : i = A.length
          · rw [heq, hGetDSnocEq A _]
            have hsi : shiftDown t A.length = B.length := by
              dsimp only [shiftDown]; rw [if_pos ht]; omega
            rw [hsi, hGetDSnocEq B _]
          · have hgt : A.length < i := by omega
            rw [hGetDSnocGt A _ i hgt]
            have hsi : B.length < shiftDown t i := by
              dsimp only [shiftDown]; rw [if_pos (by omega)]; omega
            rw [hGetDSnocGt B _ _ hsi]
  have hFoldSubF : ∀ (gs : List Gate) (v0 : ℕ) (A B : List Bool),
      A.length = B.length → v0 < A.length → A.getD v0 false = false →
      (∀ i, i ≠ v0 → B.getD i false = A.getD i false) →
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      (∀ i, i ≠ v0 → ((gs.map (rwSubF v0)).foldl step B).getD i false =
        (gs.foldl step A).getD i false) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ _ _ _ hAB _; exact hAB
    | cons g gs ih =>
      intro v0 A B hlen hv0 hAv hAB hop
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hv : (rwSubF v0 g).op.eval ((rwSubF v0 g).inputs.map fun i => B.getD i false) =
          g.op.eval (g.inputs.map fun i => A.getD i false) :=
        hRwSubFStep v0 g A B (hop g (List.mem_cons_self ..)) hAv hAB
      apply ih v0 (step A g) (step B (rwSubF v0 g))
      · simp [step]; omega
      · simp [step]; omega
      · dsimp only [step]; rw [hGetDSnocLt A _ v0 hv0]; exact hAv
      · intro i hi
        dsimp only [step]
        rw [hv]
        by_cases hlt : i < A.length
        · rw [hGetDSnocLt A _ i hlt, hGetDSnocLt B _ i (by omega)]
          exact hAB i hi
        · by_cases heq : i = A.length
          · rw [heq, hGetDSnocEq A _, hlen, hGetDSnocEq B _]
          · rw [hGetDSnocGt A _ i (by omega), hGetDSnocGt B _ i (by omega)]
      · exact fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')
  -- Circuit-level gate elimination lemmas
  have hElimFalse : ∀ (n : ℕ) (C : Circuit) (k : ℕ),
      Monotone2 C → (hk : k < C.gates.length) → C.output ≠ n + k →
      (∀ x : Fin n → Bool,
        let w1 := (C.gates.take k).foldl step (List.ofFn x)
        (C.gates[k]'hk).op.eval ((C.gates[k]'hk).inputs.map fun i => w1.getD i false) = false) →
      ∃ C' : Circuit, Monotone2 C' ∧ C'.size < C.size ∧ circuitFun n C' = circuitFun n C := by
    intro n C k hM hk hout hkf
    let pre := C.gates.take k
    let post := C.gates.drop (k + 1)
    let t := n + k
    let C' : Circuit := ⟨pre.map (rwFalse t) ++ post.map (rwFalse t), shiftDown t C.output⟩
    refine ⟨C', ?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with h1 | h2
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h1
        have hmem : g0 ∈ C.gates := List.mem_of_mem_take hg0
        have hm0 := hMonoOp hM hmem
        exact hRwFalseMono t g0 hm0.1 hm0.2
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h2
        have hmem : g0 ∈ C.gates := List.mem_of_mem_drop hg0
        have hm0 := hMonoOp hM hmem
        exact hRwFalseMono t g0 hm0.1 hm0.2
    · show C'.gates.length < C.gates.length
      dsimp only [C', pre, post]
      rw [List.length_append, List.length_map, List.length_map, List.length_take, List.length_drop]
      omega
    · funext x
      dsimp only [circuitFun]
      rw [hEvalEq C', hEvalEq C]
      have hsp := hListSplit C.gates k hk
      conv_rhs => rw [hsp]
      dsimp only [C']
      rw [List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hpreLen : pre.length = k := List.length_take_of_le (Nat.le_of_lt hk)
      have hpreOp : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or :=
        fun g hg => (hMonoOp hM (List.mem_of_mem_take hg)).1
      have hpostOp : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
        fun g hg => (hMonoOp hM (List.mem_of_mem_drop hg)).1
      have hPreEq := hPreFalse pre t (List.ofFn x) (by simp [hpreLen, t]) hpreOp
      rw [hPreEq]
      let A1 := pre.foldl step (List.ofFn x)
      have hA1Len : A1.length = t := by
        dsimp only [A1, t]; rw [hFoldLen, List.length_ofFn, hpreLen]
      have hstepK : step A1 C.gates[k] = A1 ++ [false] := by
        dsimp only [step, A1, pre]
        rw [hkf x]
      change ((post.map (rwFalse t)).foldl step A1).getD (shiftDown t C.output) false =
        (post.foldl step (step A1 C.gates[k])).getD C.output false
      rw [hstepK]
      apply hPostFalse post t (A1 ++ [false]) A1 (by simp) (by simp [hA1Len])
        (by rw [← hA1Len]; exact hGetDSnocEq A1 false)
      · intro i hi
        dsimp only [shiftDown]
        by_cases hlt : t < i
        · rw [if_pos hlt, hGetDOob A1 (i - 1) (by omega), hGetDSnocGt A1 false i (by omega)]
        · rw [if_neg hlt, hGetDSnocLt A1 false i (by omega)]
      · exact hpostOp
      · exact hout
  have hElimCopy : ∀ (n : ℕ) (C : Circuit) (k w : ℕ),
      Monotone2 C → (hk : k < C.gates.length) → w < n + k →
      (∀ x : Fin n → Bool,
        let w1 := (C.gates.take k).foldl step (List.ofFn x)
        (C.gates[k]'hk).op.eval ((C.gates[k]'hk).inputs.map fun i => w1.getD i false) = w1.getD w false) →
      ∃ C' : Circuit, Monotone2 C' ∧ C'.size < C.size ∧ circuitFun n C' = circuitFun n C := by
    intro n C k w hM hk hwk hkw
    let pre := C.gates.take k
    let post := C.gates.drop (k + 1)
    let t := n + k
    let C' : Circuit := ⟨pre.map (rwFalse t) ++ post.map (rwCopy t w),
      if C.output = t then w else shiftDown t C.output⟩
    refine ⟨C', ?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with h1 | h2
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h1
        have hm0 := hMonoOp hM (List.mem_of_mem_take hg0)
        exact hRwFalseMono t g0 hm0.1 hm0.2
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h2
        have hm0 := hMonoOp hM (List.mem_of_mem_drop hg0)
        exact hRwCopyMono t w g0 hm0.1 hm0.2
    · show C'.gates.length < C.gates.length
      dsimp only [C', pre, post]
      rw [List.length_append, List.length_map, List.length_map, List.length_take, List.length_drop]
      omega
    · funext x
      dsimp only [circuitFun]
      rw [hEvalEq C', hEvalEq C]
      have hsp := hListSplit C.gates k hk
      conv_rhs => rw [hsp]
      dsimp only [C']
      rw [List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hpreLen : pre.length = k := List.length_take_of_le (Nat.le_of_lt hk)
      have hpreOp : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or :=
        fun g hg => (hMonoOp hM (List.mem_of_mem_take hg)).1
      rw [hPreFalse pre t (List.ofFn x) (by simp [hpreLen, t]) hpreOp]
      let A1 := pre.foldl step (List.ofFn x)
      have hA1Len : A1.length = t := by
        dsimp only [A1, t]; rw [hFoldLen, List.length_ofFn, hpreLen]
      have hstepK : step A1 C.gates[k] = A1 ++ [A1.getD w false] := by
        dsimp only [step, A1, pre]
        rw [hkw x]
      change ((post.map (rwCopy t w)).foldl step A1).getD
          (if C.output = t then w else shiftDown t C.output) false =
        (post.foldl step (step A1 C.gates[k])).getD C.output false
      rw [hstepK]
      apply hPostCopy post t w (A1 ++ [A1.getD w false]) A1 (by simp) hwk (by simp [hA1Len])
        (by rw [← hA1Len]; exact (hGetDSnocEq A1 _).symm)
      intro i hi
      dsimp only [shiftDown]
      by_cases hlt : t < i
      · rw [if_pos hlt, hGetDOob A1 (i - 1) (by omega), hGetDSnocGt A1 _ i (by omega)]
      · rw [if_neg hlt, hGetDSnocLt A1 _ i (by omega)]
  have hElimTrue : ∀ (n : ℕ) (C : Circuit) (k : ℕ),
      Monotone2 C → (hk : k < C.gates.length) → C.output ≠ n + k →
      (∀ x : Fin n → Bool,
        let w1 := (C.gates.take k).foldl step (List.ofFn x)
        (C.gates[k]'hk).op.eval ((C.gates[k]'hk).inputs.map fun i => w1.getD i false) = true) →
      ∃ C' : Circuit, Monotone2 C' ∧ C'.size < C.size ∧ circuitFun n C' = circuitFun n C := by
    intro n C k hM hk hout hkt
    let pre := C.gates.take k
    let post := C.gates.drop (k + 1)
    let t := n + k
    let C' : Circuit := ⟨pre.map (rwFalse t) ++ post.map (rwTrue t), shiftDown t C.output⟩
    refine ⟨C', ?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with h1 | h2
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h1
        have hm0 := hMonoOp hM (List.mem_of_mem_take hg0)
        exact hRwFalseMono t g0 hm0.1 hm0.2
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h2
        have hm0 := hMonoOp hM (List.mem_of_mem_drop hg0)
        exact hRwTrueMono t g0 hm0.1 hm0.2
    · show C'.gates.length < C.gates.length
      dsimp only [C', pre, post]
      rw [List.length_append, List.length_map, List.length_map, List.length_take, List.length_drop]
      omega
    · funext x
      dsimp only [circuitFun]
      rw [hEvalEq C', hEvalEq C]
      have hsp := hListSplit C.gates k hk
      conv_rhs => rw [hsp]
      dsimp only [C']
      rw [List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hpreLen : pre.length = k := List.length_take_of_le (Nat.le_of_lt hk)
      have hpreOp : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or :=
        fun g hg => (hMonoOp hM (List.mem_of_mem_take hg)).1
      have hpostOp : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
        fun g hg => (hMonoOp hM (List.mem_of_mem_drop hg)).1
      rw [hPreFalse pre t (List.ofFn x) (by simp [hpreLen, t]) hpreOp]
      let A1 := pre.foldl step (List.ofFn x)
      have hA1Len : A1.length = t := by
        dsimp only [A1, t]; rw [hFoldLen, List.length_ofFn, hpreLen]
      have hstepK : step A1 C.gates[k] = A1 ++ [true] := by
        dsimp only [step, A1, pre]
        rw [hkt x]
      change ((post.map (rwTrue t)).foldl step A1).getD (shiftDown t C.output) false =
        (post.foldl step (step A1 C.gates[k])).getD C.output false
      rw [hstepK]
      apply hPostTrue post t (A1 ++ [true]) A1 (by simp) (by simp [hA1Len])
        (by rw [← hA1Len]; exact hGetDSnocEq A1 true)
      · intro i hi
        dsimp only [shiftDown]
        by_cases hlt : t < i
        · rw [if_pos hlt, hGetDOob A1 (i - 1) (by omega), hGetDSnocGt A1 true i (by omega)]
        · rw [if_neg hlt, hGetDSnocLt A1 true i (by omega)]
      · exact hpostOp
      · exact hout
  -- graphFun G empty equals the edge function in L-meta-606
  have hGraphFunEq : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      graphFun G ∅ =
        (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) := by
    intro n G _
    funext x
    dsimp only [graphFun]
    simp
  -- Any size-minimal Monotone2 circuit for a nonempty graph is IsLeastAO (and has output >= n)
  have hNormalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.Nonempty →
      ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
      ∃ C : Circuit, IsLeastAO G C ∧ C.size ≤ D.size ∧ n ≤ C.output ∧ C.output < n + C.gates.length := by
    intro n G _ hne D hDM hDF
    have hEx : ∃ s : ℕ, ∃ E : Circuit, Monotone2 E ∧ circuitFun n E = graphFun G ∅ ∧ E.size = s :=
      ⟨D.size, D, hDM, hDF, rfl⟩
    let s0 := Nat.find hEx
    have hs0Spec := Nat.find_spec hEx
    obtain ⟨C, hCM, hCF, hCs⟩ := hs0Spec
    have hCleD : C.size ≤ D.size := by
      rw [hCs]
      exact Nat.find_min' hEx ⟨D, hDM, hDF, rfl⟩
    have hMin : ∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → C.size ≤ E.size := by
      intro E hEM hEF
      rw [hCs]
      exact Nat.find_min' hEx ⟨E, hEM, hEF, rfl⟩
    -- Obtain an edge (u0, v0) of G
    obtain ⟨e0, he0⟩ := hne
    have hEdgeWit : ∃ u0 v0 : Fin n, G.Adj u0 v0 := by
      revert he0
      refine Sym2.ind ?_ e0
      intro a b hab
      exact ⟨a, b, (SimpleGraph.mem_edgeFinset).mp hab⟩
    obtain ⟨u0, v0, huv0⟩ := hEdgeWit
    have hFTrue : circuitFun n C (pairInput u0 v0) = true := by
      rw [hCF, hGraphFunEq]
      simp only [decide_eq_true_eq]
      refine ⟨u0, v0, huv0, ?_, ?_⟩
      · dsimp only [pairInput]; simp
      · dsimp only [pairInput]; simp
    have hFFalse : circuitFun n C (fun _ => false) = false := by
      rw [hCF, hGraphFunEq]
      simp
    have hFUnit : ∀ v : Fin n, circuitFun n C (unitInput v) = false := by
      intro v
      rw [hCF, hGraphFunEq]
      simp only [decide_eq_false_iff_not]
      rintro ⟨i, j, hij, hi, hj⟩
      dsimp only [unitInput] at hi hj
      rw [decide_eq_true_eq] at hi hj
      subst hi; subst hj
      exact G.loopless.irrefl _ hij
    -- Helper: gate k cannot be constantly false (and cannot be constantly true)
    have hNotConstFalse : ∀ (k : ℕ) (hk : k < C.gates.length),
        ¬ (∀ x : Fin n → Bool,
          let w1 := (C.gates.take k).foldl step (List.ofFn x)
          (C.gates[k]'hk).op.eval ((C.gates[k]'hk).inputs.map fun i => w1.getD i false) = false) := by
      intro k hk hkf
      have houtNe : C.output ≠ n + k := by
        intro houtEq
        have hv : circuitFun n C (pairInput u0 v0) = false := by
          dsimp only [circuitFun]
          rw [hEvalEq C, houtEq]
          have hsp := hListSplit C.gates k hk
          conv_lhs => rw [hsp]
          rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hpreLen : (C.gates.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
          let A1 := (C.gates.take k).foldl step (List.ofFn (pairInput u0 v0))
          have hA1Len : A1.length = n + k := by
            dsimp only [A1]; rw [hFoldLen, List.length_ofFn, hpreLen]
          rw [hFoldPrefix _ _ (n + k) (by dsimp only [step]; rw [List.length_append, List.length_singleton, hA1Len]; omega)]
          dsimp only [step]
          rw [← hA1Len, hGetDSnocEq A1 _]
          exact hkf (pairInput u0 v0)
        rw [hFTrue] at hv
        cases hv
      obtain ⟨C', hM', hlt', hF'⟩ := hElimFalse n C k hCM hk houtNe hkf
      have hge := hMin C' hM' (hF'.trans hCF)
      omega
    have hNotConstTrue : ∀ (k : ℕ) (hk : k < C.gates.length),
        ¬ (∀ x : Fin n → Bool,
          let w1 := (C.gates.take k).foldl step (List.ofFn x)
          (C.gates[k]'hk).op.eval ((C.gates[k]'hk).inputs.map fun i => w1.getD i false) = true) := by
      intro k hk hkt
      have houtNe : C.output ≠ n + k := by
        intro houtEq
        have hv : circuitFun n C (fun _ => false) = true := by
          dsimp only [circuitFun]
          rw [hEvalEq C, houtEq]
          have hsp := hListSplit C.gates k hk
          conv_lhs => rw [hsp]
          rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hpreLen : (C.gates.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
          let A1 := (C.gates.take k).foldl step (List.ofFn (fun _ : Fin n => false))
          have hA1Len : A1.length = n + k := by
            dsimp only [A1]; rw [hFoldLen, List.length_ofFn, hpreLen]
          rw [hFoldPrefix _ _ (n + k) (by dsimp only [step]; rw [List.length_append, List.length_singleton, hA1Len]; omega)]
          dsimp only [step]
          rw [← hA1Len, hGetDSnocEq A1 _]
          exact hkt (fun _ => false)
        rw [hFFalse] at hv
        cases hv
      obtain ⟨C', hM', hlt', hF'⟩ := hElimTrue n C k hCM hk houtNe hkt
      have hge := hMin C' hM' (hF'.trans hCF)
      omega
    have hNotCopy : ∀ (k w : ℕ) (hk : k < C.gates.length), w < n + k →
        ¬ (∀ x : Fin n → Bool,
          let w1 := (C.gates.take k).foldl step (List.ofFn x)
          (C.gates[k]'hk).op.eval ((C.gates[k]'hk).inputs.map fun i => w1.getD i false) = w1.getD w false) := by
      intro k w hk hwk hkw
      obtain ⟨C', hM', hlt', hF'⟩ := hElimCopy n C k w hCM hk hwk hkw
      have hge := hMin C' hM' (hF'.trans hCF)
      omega
    -- Prove ReadsBack n C
    have hRB : ReadsBack n C := by
      intro k hk i hi
      rw [hGateAtEq hk] at hi
      by_contra hge
      have hge' : n + k ≤ i := Nat.le_of_not_lt hge
      have hm := hMonoOp hCM (List.getElem_mem hk)
      have hpreLen : (C.gates.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
      have hW1Len : ∀ x : Fin n → Bool,
          ((C.gates.take k).foldl step (List.ofFn x)).length = n + k := by
        intro x; rw [hFoldLen, List.length_ofFn, hpreLen]
      rcases hm.1 with hop | hop
      · apply hNotConstFalse k hk
        intro x
        dsimp only
        rw [hop, hEvalAnd, List.all_eq_false]
        exact ⟨false, List.mem_map.mpr ⟨i, hi, hGetDOob _ i (by rw [hW1Len x]; exact hge')⟩, by decide⟩
      · -- OR gate with at most 2 inputs, one of which is >= n + k
        generalize hL : (C.gates[k]).inputs = ins at hi hm
        rcases ins with _ | ⟨a, rest⟩
        · simp at hi
        · rcases rest with _ | ⟨b, rest2⟩
          · simp only [List.mem_singleton] at hi
            subst hi
            apply hNotConstFalse k hk
            intro x
            dsimp only
            rw [hop, hL, List.map_cons, List.map_nil, hEvalOrOne]
            exact hGetDOob _ i (by rw [hW1Len x]; exact hge')
          · rcases rest2 with _ | ⟨c, rest3⟩
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · by_cases hb : b < n + k
                · apply hNotCopy k b hk hb
                  intro x
                  dsimp only
                  rw [hop, hL, List.map_cons, List.map_cons, List.map_nil, hEvalOr]
                  have ha0 : ((C.gates.take k).foldl step (List.ofFn x)).getD i false = false :=
                    hGetDOob _ i (by rw [hW1Len x]; exact hge')
                  rw [ha0]; simp
                · apply hNotConstFalse k hk
                  intro x
                  dsimp only
                  rw [hop, hL, List.map_cons, List.map_cons, List.map_nil, hEvalOr]
                  have ha0 : ((C.gates.take k).foldl step (List.ofFn x)).getD i false = false :=
                    hGetDOob _ i (by rw [hW1Len x]; exact hge')
                  have hb0 : ((C.gates.take k).foldl step (List.ofFn x)).getD b false = false :=
                    hGetDOob _ b (by rw [hW1Len x]; omega)
                  rw [ha0, hb0]; decide
              · by_cases ha : a < n + k
                · apply hNotCopy k a hk ha
                  intro x
                  dsimp only
                  rw [hop, hL, List.map_cons, List.map_cons, List.map_nil, hEvalOr]
                  have hb0 : ((C.gates.take k).foldl step (List.ofFn x)).getD i false = false :=
                    hGetDOob _ i (by rw [hW1Len x]; exact hge')
                  rw [hb0]; simp
                · apply hNotConstFalse k hk
                  intro x
                  dsimp only
                  rw [hop, hL, List.map_cons, List.map_cons, List.map_nil, hEvalOr]
                  have ha0 : ((C.gates.take k).foldl step (List.ofFn x)).getD a false = false :=
                    hGetDOob _ a (by rw [hW1Len x]; omega)
                  have hb0 : ((C.gates.take k).foldl step (List.ofFn x)).getD i false = false :=
                    hGetDOob _ i (by rw [hW1Len x]; exact hge')
                  rw [ha0, hb0]; decide
            · exfalso; have h2 := hm.2; simp at h2
    -- Prove exact fan-in 2 for every gate of C
    have hLen2 : ∀ g ∈ C.gates, g.inputs.length = 2 := by
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      have hm := hMonoOp hCM (List.getElem_mem hk)
      have hrbk : ∀ i ∈ (C.gates[k]).inputs, i < n + k := by
        intro i hi
        have := hRB k hk i (by rw [hGateAtEq hk]; exact hi)
        exact this
      generalize hL : (C.gates[k]).inputs = ins at hm hrbk ⊢
      rcases ins with _ | ⟨a, rest⟩
      · exfalso
        rcases hm.1 with hop | hop
        · apply hNotConstTrue k hk
          intro x; dsimp only; rw [hop, hL, List.map_nil, hEvalAndNil]
        · apply hNotConstFalse k hk
          intro x; dsimp only; rw [hop, hL, List.map_nil, hEvalOrNil]
      · rcases rest with _ | ⟨b, rest2⟩
        · exfalso
          have ha : a < n + k := hrbk a (List.mem_cons_self ..)
          apply hNotCopy k a hk ha
          intro x
          dsimp only
          rw [hL, List.map_cons, List.map_nil]
          rcases hm.1 with hop | hop
          · rw [hop, hEvalAndOne]
          · rw [hop, hEvalOrOne]
        · rcases rest2 with _ | ⟨c, rest3⟩
          · rfl
          · exfalso; have h2 := hm.2; simp at h2
    -- Output bounds: n <= C.output < n + C.gates.length
    have hOutGe : n ≤ C.output := by
      by_contra hlt
      have ho : C.output < n := Nat.lt_of_not_ge hlt
      let v : Fin n := ⟨C.output, ho⟩
      have hv := hFUnit v
      dsimp only [circuitFun] at hv
      rw [hEvalEq C, hFoldPrefix C.gates (List.ofFn (unitInput v)) C.output
        (by rw [List.length_ofFn]; exact ho)] at hv
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact ho), List.getElem_ofFn] at hv
      dsimp only [unitInput, v] at hv
      simp at hv
    have hOutLt : C.output < n + C.gates.length := by
      by_contra hge
      have hge' : n + C.gates.length ≤ C.output := Nat.le_of_not_lt hge
      have hv : circuitFun n C (pairInput u0 v0) = false := by
        dsimp only [circuitFun]
        rw [hEvalEq C]
        exact hGetDOob _ C.output (by rw [hFoldLen, List.length_ofFn]; exact hge')
      rw [hFTrue] at hv
      cases hv
    -- Assemble IsLeastAO G C
    have hAO2 : IsAO2 n C := ⟨fun g hg => (hMonoOp hCM hg).1, hRB, hLen2⟩
    have hLeast : IsLeastAO G C := by
      refine ⟨hAO2, hCF, ?_⟩
      intro E hE hEF
      have hEM : Monotone2 E := by
        intro g hg
        refine ⟨?_, by rw [hE.2.2 g hg]⟩
        rcases hE.1 g hg with h | h <;> simp [h]
      exact hMin E hEM hEF
    exact ⟨C, hLeast, hCleD, hOutGe, hOutLt⟩
  -- Positive-degree vertex deletion strictly shrinks circuit size
  have hPeel : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n),
      0 < G.degree v →
      ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
      ∃ (H : SimpleGraph (Fin n)) (_ : DecidableRel H.Adj) (D' : Circuit),
        (∀ a b, H.Adj a b ↔ G.Adj a b ∧ a ≠ v ∧ b ≠ v) ∧
        Monotone2 D' ∧ D'.size < D.size ∧ circuitFun n D' = graphFun H ∅ := by
    intro n G _ v hdeg D hDM hDF
    -- Witness neighbor u of v
    have hNb : ∃ u : Fin n, G.Adj v u := by
      have hcard : 0 < (G.neighborFinset v).card := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hcard
      exact ⟨u, (SimpleGraph.mem_neighborFinset G v u).mp hu⟩
    obtain ⟨u, hvu⟩ := hNb
    have hne : G.edgeFinset.Nonempty := ⟨s(v, u), SimpleGraph.mem_edgeFinset.mpr hvu⟩
    obtain ⟨C, hLeast, hCleD, hOutGe, hOutLt⟩ := hNormalize n G hne D hDM hDF
    have hCpos : 0 < C.gates.length := by omega
    -- Construct H = G with all edges incident to v removed
    let H : SimpleGraph (Fin n) := {
      Adj := fun a b => G.Adj a b ∧ a ≠ v ∧ b ≠ v
      symm := ⟨fun a b h => ⟨G.symm.symm a b h.1, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩
    }
    letI : DecidableRel H.Adj := fun a b =>
      inferInstanceAs (Decidable (G.Adj a b ∧ a ≠ v ∧ b ≠ v))
    have hFunUpdate : ∀ x : Fin n → Bool,
        graphFun G ∅ (Function.update x v false) = graphFun H ∅ x := by
      intro x
      rw [hGraphFunEq, hGraphFunEq]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        have hav : a ≠ v := by
          intro heq; rw [heq, Function.update_self] at ha; cases ha
        have hbv : b ≠ v := by
          intro heq; rw [heq, Function.update_self] at hb; cases hb
        rw [Function.update_of_ne hav] at ha
        rw [Function.update_of_ne hbv] at hb
        exact ⟨a, b, ⟨hab, hav, hbv⟩, ha, hb⟩
      · rintro ⟨a, b, ⟨hab, hav, hbv⟩, ha, hb⟩
        exact ⟨a, b, hab, by rw [Function.update_of_ne hav]; exact ha,
          by rw [Function.update_of_ne hbv]; exact hb⟩
    -- Some gate k of C must read wire v.val
    have hReadsV : ∃ (k : ℕ) (hk : k < C.gates.length), v.val ∈ (C.gates[k]'hk).inputs := by
      by_contra hno
      have hno' : ∀ g ∈ C.gates, v.val ∉ g.inputs := by
        intro g hg hmem
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
        exact hno ⟨k, hk, hmem⟩
      have hSame : ∀ (gs : List Gate) (A B : List Bool),
          A.length = B.length →
          (∀ i, i ≠ v.val → B.getD i false = A.getD i false) →
          (∀ g ∈ gs, v.val ∉ g.inputs) →
          (∀ i, i ≠ v.val → (gs.foldl step B).getD i false = (gs.foldl step A).getD i false) := by
        intro gs
        induction gs with
        | nil => intro _ _ _ hAB _; exact hAB
        | cons g gs ih =>
          intro A B hlen hAB hnv
          rw [List.foldl_cons, List.foldl_cons]
          have hgv : v.val ∉ g.inputs := hnv g (List.mem_cons_self ..)
          have hvEq : g.op.eval (g.inputs.map fun i => B.getD i false) =
              g.op.eval (g.inputs.map fun i => A.getD i false) := by
            congr 1
            apply List.map_congr_left
            intro i hi
            exact hAB i (fun heq => hgv (heq ▸ hi))
          apply ih (step A g) (step B g) (by simp [step]; omega)
          · intro i hi
            dsimp only [step]
            rw [hvEq]
            by_cases hlt : i < A.length
            · rw [hGetDSnocLt A _ i hlt, hGetDSnocLt B _ i (by omega)]
              exact hAB i hi
            · by_cases heq : i = A.length
              · rw [heq, hGetDSnocEq A _, hlen, hGetDSnocEq B _]
              · rw [hGetDSnocGt A _ i (by omega), hGetDSnocGt B _ i (by omega)]
          · exact fun g' hg' => hnv g' (List.mem_cons_of_mem _ hg')
      have hEvEq : circuitFun n C (pairInput v u) = circuitFun n C (unitInput u) := by
        dsimp only [circuitFun]
        rw [hEvalEq C, hEvalEq C]
        apply hSame C.gates (List.ofFn (unitInput u)) (List.ofFn (pairInput v u))
          (by simp) _ hno' C.output (by omega)
        intro i hi
        by_cases hin : i < n
        · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hin),
            List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hin),
            List.getElem_ofFn, List.getElem_ofFn]
          dsimp only [pairInput, unitInput]
          have hne : (⟨i, hin⟩ : Fin n) ≠ v := by intro heq; exact hi (congrArg Fin.val heq)
          simp [hne]
        · rw [hGetDOob _ i (by rw [List.length_ofFn]; omega),
            hGetDOob _ i (by rw [List.length_ofFn]; omega)]
      rw [hLeast.2.1, hGraphFunEq] at hEvEq
      have hT : decide (∃ a b : Fin n, G.Adj a b ∧ pairInput v u a = true ∧ pairInput v u b = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨v, u, hvu, by dsimp only [pairInput]; simp, by dsimp only [pairInput]; simp⟩
      have hF : decide (∃ a b : Fin n, G.Adj a b ∧ unitInput u a = true ∧ unitInput u b = true) = false := by
        simp only [decide_eq_false_iff_not]
        rintro ⟨a, b, hab, ha, hb⟩
        dsimp only [unitInput] at ha hb
        rw [decide_eq_true_eq] at ha hb
        subst ha; subst hb
        exact G.loopless.irrefl _ hab
      dsimp only at hEvEq
      rw [hT, hF] at hEvEq
      cases hEvEq
    obtain ⟨k, hk, hvk⟩ := hReadsV
    -- Build C1 by substituting x_v := false
    let C1 : Circuit := ⟨C.gates.map (rwSubF v.val), C.output⟩
    have hC1M : Monotone2 C1 := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact hRwSubFMono v.val g0 (hLeast.1.1 g0 hg0) (by rw [hLeast.1.2.2 g0 hg0])
    have hC1F : circuitFun n C1 = graphFun H ∅ := by
      funext x
      rw [← hFunUpdate x, ← hLeast.2.1]
      dsimp only [circuitFun, C1]
      rw [hEvalEq ⟨C.gates.map (rwSubF v.val), C.output⟩, hEvalEq C]
      apply hFoldSubF C.gates v.val (List.ofFn (Function.update x v false)) (List.ofFn x)
        (by simp) (by rw [List.length_ofFn]; exact v.isLt)
      · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact v.isLt), List.getElem_ofFn]
        simp
      · intro i hi
        by_cases hin : i < n
        · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hin),
            List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hin),
            List.getElem_ofFn, List.getElem_ofFn]
          have hne : (⟨i, hin⟩ : Fin n) ≠ v := by intro heq; exact hi (congrArg Fin.val heq)
          rw [Function.update_of_ne hne]
        · rw [hGetDOob _ i (by rw [List.length_ofFn]; omega),
            hGetDOob _ i (by rw [List.length_ofFn]; omega)]
      · exact hLeast.1.1
      · dsimp only; have hvlt : v.val < n := v.isLt; omega
    have hk1 : k < C1.gates.length := by dsimp only [C1]; rw [List.length_map]; exact hk
    have hgk1 : C1.gates[k] = rwSubF v.val C.gates[k] := by
      dsimp only [C1]; exact List.getElem_map ..
    have hC1Len : C1.size = C.size := by show C1.gates.length = C.gates.length; dsimp only [C1]; rw [List.length_map]
    -- Gate k of C1 is either constant false (⟨.or, []⟩) or unary copy (⟨.or, [w]⟩ with w < n + k)
    have hgkOp : (C.gates[k]).op = GateOp.and ∨ (C.gates[k]).op = GateOp.or :=
      hLeast.1.1 _ (List.getElem_mem hk)
    have hgkLen : (C.gates[k]).inputs.length = 2 := hLeast.1.2.2 _ (List.getElem_mem hk)
    have hgkRB : ∀ i ∈ (C.gates[k]).inputs, i < n + k := by
      intro i hi
      exact hLeast.1.2.1 k hk i (by rw [hGateAtEq hk]; exact hi)
    -- Analyze rwSubF v.val C.gates[k]
    have hShrink : ∃ D' : Circuit, Monotone2 D' ∧ D'.size < C1.size ∧ circuitFun n D' = circuitFun n C1 := by
      rcases hgkOp with ha | ho
      · have hgkEq : C1.gates[k] = ⟨GateOp.or, []⟩ := by
          rw [hgk1]; dsimp only [rwSubF]; rw [if_pos hvk, if_pos ha]
        by_cases houtK : C1.output = n + k
        · -- Output is constantly false, so 0-gate circuit computes the same function
          refine ⟨⟨[], n⟩, (fun _ hg => by cases hg), ?_, ?_⟩
          · show 0 < C1.gates.length; omega
          · funext x
            dsimp only [circuitFun]
            rw [hEvalEq ⟨[], n⟩, List.foldl_nil, hGetDOob _ n (by rw [List.length_ofFn])]
            symm
            rw [hEvalEq C1, houtK]
            have hsp := hListSplit C1.gates k hk1
            conv_lhs => rw [hsp]
            rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
            have hpreLen : (C1.gates.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk1)
            let A1 := (C1.gates.take k).foldl step (List.ofFn x)
            have hA1Len : A1.length = n + k := by
              dsimp only [A1]; rw [hFoldLen, List.length_ofFn, hpreLen]
            rw [hFoldPrefix _ _ (n + k) (by dsimp only [step]; rw [List.length_append, List.length_singleton, hA1Len]; omega)]
            dsimp only [step]
            rw [← hA1Len, hGetDSnocEq A1 _, hgkEq]
            dsimp only
            rw [List.map_nil, hEvalOrNil]
        · exact hElimFalse n C1 k hC1M hk1 houtK (fun x => by dsimp only; rw [hgkEq]; dsimp only; rw [List.map_nil, hEvalOrNil])
      · have hneAnd : (C.gates[k]).op ≠ GateOp.and := by rw [ho]; decide
        have hgkEq : C1.gates[k] = ⟨GateOp.or, (C.gates[k]).inputs.filter (fun i => decide (i ≠ v.val))⟩ := by
          rw [hgk1]; dsimp only [rwSubF]; rw [if_pos hvk, if_neg hneAnd]
        have hFiltLen : ((C.gates[k]).inputs.filter (fun i => decide (i ≠ v.val))).length ≤ 1 := by
          generalize hL : (C.gates[k]).inputs = ins at hvk hgkLen ⊢
          rcases ins with _ | ⟨a, rest⟩
          · simp at hgkLen
          · rcases rest with _ | ⟨b, rest2⟩
            · simp at hgkLen
            · rcases rest2 with _ | ⟨c, rest3⟩
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hvk
                rcases hvk with rfl | rfl
                · by_cases hb : b = v.val <;> simp [hb]
                · by_cases ha : a = v.val <;> simp [ha]
              · simp at hgkLen
        generalize hF : (C.gates[k]).inputs.filter (fun i => decide (i ≠ v.val)) = fl at hgkEq hFiltLen
        rcases fl with _ | ⟨w, rest⟩
        · by_cases houtK : C1.output = n + k
          · refine ⟨⟨[], n⟩, (fun _ hg => by cases hg), ?_, ?_⟩
            · show 0 < C1.gates.length; omega
            · funext x
              dsimp only [circuitFun]
              rw [hEvalEq ⟨[], n⟩, List.foldl_nil, hGetDOob _ n (by rw [List.length_ofFn])]
              symm
              rw [hEvalEq C1, houtK]
              have hsp := hListSplit C1.gates k hk1
              conv_lhs => rw [hsp]
              rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
              have hpreLen : (C1.gates.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk1)
              let A1 := (C1.gates.take k).foldl step (List.ofFn x)
              have hA1Len : A1.length = n + k := by
                dsimp only [A1]; rw [hFoldLen, List.length_ofFn, hpreLen]
              rw [hFoldPrefix _ _ (n + k) (by dsimp only [step]; rw [List.length_append, List.length_singleton, hA1Len]; omega)]
              dsimp only [step]
              rw [← hA1Len, hGetDSnocEq A1 _, hgkEq]
              dsimp only
              rw [List.map_nil, hEvalOrNil]
          · exact hElimFalse n C1 k hC1M hk1 houtK (fun x => by dsimp only; rw [hgkEq]; dsimp only; rw [List.map_nil, hEvalOrNil])
        · rcases rest with _ | ⟨w2, rest2⟩
          · have hwMem : w ∈ (C.gates[k]).inputs := by
              have h1 : w ∈ (C.gates[k]).inputs.filter (fun i => decide (i ≠ v.val)) := by
                rw [hF]; exact List.mem_cons_self ..
              exact (List.mem_filter.mp h1).1
            have hwk : w < n + k := hgkRB w hwMem
            exact hElimCopy n C1 k w hC1M hk1 hwk (fun x => by
              dsimp only; rw [hgkEq]; dsimp only; rw [List.map_cons, List.map_nil, hEvalOrOne])
          · exfalso; simp at hFiltLen
    obtain ⟨D', hD'M, hD'lt, hD'F⟩ := hShrink
    refine ⟨H, inferInstance, D', fun _ _ => Iff.rfl, hD'M, by omega, hD'F.trans hC1F⟩
  -- Unpack the three children
  obtain ⟨c1, hClean⟩ := cleanCase
  obtain ⟨d2, c2, hOneHot⟩ := oneHotDirtyCase
  obtain ⟨d3, c3, hPair⟩ := pairDirtyCase
  let d := max 3 (max d2 d3)
  let c := max d (max c1 (max c2 c3))
  refine ⟨c, ?_⟩
  -- Strong induction on circuit size
  have hBudget : ∀ s : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, D.size = s → Monotone2 D →
      circuitFun n D = graphFun G ∅ →
      G.edgeFinset.card ≤ c * (D.size + 1) := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro n G _ hg D hsize hDM hDF
      by_cases hne : G.edgeFinset.Nonempty
      · by_cases hdegAll : ∀ v : Fin n, G.degree v = 0 ∨ d ≤ G.degree v
        · obtain ⟨C, hLeast, hCleD, _, _⟩ := hNormalize n G hne D hDM hDF
          have hBoundC : G.edgeFinset.card ≤ c * (C.size + 1) := by
            by_cases hJE : junk G C = ∅
            · have hdeg3 : ∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v := fun v =>
                (hdegAll v).imp_right (fun hd => (le_max_left 3 (max d2 d3)).trans hd)
              have h1 := hClean n G C hdeg3 hg hne hLeast hJE
              have hc1 : c1 ≤ c := (le_max_left c1 (max c2 c3)).trans (le_max_right d _)
              exact h1.trans (Nat.mul_le_mul_right _ hc1)
            · have hJNe : (junk G C).Nonempty := Finset.nonempty_iff_ne_empty.mpr hJE
              by_cases hOH : ∃ j ∈ junk G C, ∃ v : Fin n, gateVal n C j (unitInput v) = true
              · have hdeg2 : ∀ v : Fin n, G.degree v = 0 ∨ d2 ≤ G.degree v := fun v =>
                  (hdegAll v).imp_right (fun hd =>
                    ((le_max_left d2 d3).trans (le_max_right 3 _)).trans hd)
                have h2 := hOneHot n G C hdeg2 hg hne hLeast hOH
                have hc2 : c2 ≤ c :=
                  ((le_max_left c2 c3).trans (le_max_right c1 _)).trans (le_max_right d _)
                exact h2.trans (Nat.mul_le_mul_right _ hc2)
              · have hOff : ∀ j ∈ junk G C, ∀ v : Fin n, gateVal n C j (unitInput v) = false := by
                  intro j hj v
                  have hnt : gateVal n C j (unitInput v) ≠ true := fun ht => hOH ⟨j, hj, v, ht⟩
                  exact Bool.eq_false_iff.mpr hnt
                have hdeg3' : ∀ v : Fin n, G.degree v = 0 ∨ d3 ≤ G.degree v := fun v =>
                  (hdegAll v).imp_right (fun hd =>
                    ((le_max_right d2 d3).trans (le_max_right 3 _)).trans hd)
                have h3 := hPair n G C hdeg3' hg hne hLeast hJNe hOff
                have hc3 : c3 ≤ c :=
                  ((le_max_right c2 c3).trans (le_max_right c1 _)).trans (le_max_right d _)
                exact h3.trans (Nat.mul_le_mul_right _ hc3)
          exact hBoundC.trans (Nat.mul_le_mul_left c (Nat.succ_le_succ hCleD))
        · push_neg at hdegAll
          obtain ⟨v, hvne, hvlt⟩ := hdegAll
          have hvpos : 0 < G.degree v := Nat.pos_of_ne_zero hvne
          obtain ⟨H, instH, D', hHAdj, hD'M, hD'lt, hD'F⟩ := hPeel n G v hvpos D hDM hDF
          letI := instH
          have hHleG : H ≤ G := fun a b hab => (hHAdj a b).mp hab |>.1
          have hHcycle : ∀ (u : Fin n) (p : H.Walk u u), p.IsCycle → 5 ≤ p.length := by
            intro u p hp
            have := hg u (p.mapLe hHleG) (hp.mapLe hHleG)
            simpa only [SimpleGraph.Walk.length_mapLe] using this
          have hIH := ih D'.size (hsize ▸ hD'lt) n H hHcycle D' rfl hD'M hD'F
          have hHsub : H.edgeFinset ⊆ G.edgeFinset := by
            intro e he
            revert he
            refine Sym2.ind ?_ e
            intro a b hab
            exact SimpleGraph.mem_edgeFinset.mpr (hHleG (SimpleGraph.mem_edgeFinset.mp hab))
          have hDiffSub : G.edgeFinset \ H.edgeFinset ⊆ (G.neighborFinset v).image (fun u => s(v, u)) := by
            intro e he
            obtain ⟨heG, heH⟩ := Finset.mem_sdiff.mp he
            revert heG heH
            refine Sym2.ind ?_ e
            intro a b hab hnab
            have hab' : G.Adj a b := SimpleGraph.mem_edgeFinset.mp hab
            have hnab' : ¬ (G.Adj a b ∧ a ≠ v ∧ b ≠ v) := by
              intro h1
              exact hnab (SimpleGraph.mem_edgeFinset.mpr ((hHAdj a b).mpr h1))
            have hor : a = v ∨ b = v := by
              by_contra h1
              push_neg at h1
              exact hnab' ⟨hab', h1.1, h1.2⟩
            rcases hor with rfl | rfl
            · exact Finset.mem_image.mpr ⟨b, (SimpleGraph.mem_neighborFinset G a b).mpr hab', rfl⟩
            · exact Finset.mem_image.mpr ⟨a, (SimpleGraph.mem_neighborFinset G b a).mpr (G.symm.symm a b hab'), Sym2.eq_swap⟩
          have hDiffCard : (G.edgeFinset \ H.edgeFinset).card ≤ G.degree v := by
            calc (G.edgeFinset \ H.edgeFinset).card
                ≤ ((G.neighborFinset v).image (fun u => s(v, u))).card := Finset.card_le_card hDiffSub
              _ ≤ (G.neighborFinset v).card := Finset.card_image_le
              _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
          have hSplit := Finset.card_sdiff_add_card_eq_card hHsub
          have hSucc : D'.size + 1 ≤ D.size := by omega
          have hMul : c * (D'.size + 1) + c ≤ c * (D.size + 1) := by
            calc c * (D'.size + 1) + c = c * (D'.size + 1 + 1) := (Nat.mul_succ c (D'.size + 1)).symm
              _ ≤ c * (D.size + 1) := Nat.mul_le_mul_left c (by omega)
          have hdc : d ≤ c := le_max_left d _
          omega
      · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
        simp [hempty]
  intro n G _ hg D hDM hDF
  exact hBudget D.size n G hg D rfl hDM (hDF.trans (hGraphFunEq n G).symm)
