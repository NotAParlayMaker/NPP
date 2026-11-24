import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2044_1 :
    (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D →
      D.size = 14 →
      (PEqualNP.TopForm.junk
        (PEqualNP.EdgeOwnership.edgeGraph 9
          [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]) D).card = 0 →
      PEqualNP.MetaComplexity.circuitFun 9 D ≠
        PEqualNP.MetaComplexity.NestedCover.graphFun
          (PEqualNP.EdgeOwnership.edgeGraph 9
            [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]) ∅) →
    (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D →
      D.size = 14 →
      (PEqualNP.TopForm.junk
        (PEqualNP.EdgeOwnership.edgeGraph 9
          [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]) D).card = 1 →
      PEqualNP.MetaComplexity.circuitFun 9 D ≠
        PEqualNP.MetaComplexity.NestedCover.graphFun
          (PEqualNP.EdgeOwnership.edgeGraph 9
            [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]) ∅) →
    (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D →
      D.size = 14 →
      2 ≤ (PEqualNP.TopForm.junk
        (PEqualNP.EdgeOwnership.edgeGraph 9
          [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]) D).card →
      PEqualNP.MetaComplexity.circuitFun 9 D ≠
        PEqualNP.MetaComplexity.NestedCover.graphFun
          (PEqualNP.EdgeOwnership.edgeGraph 9
            [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]) ∅) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (0 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) := by
  intro h0 h1 h2 C hFan hWire9 hSize hZeroNot hFun
  have getD_snoc_lt : ∀ (l : List Bool) (a : Bool) (k : ℕ),
      k < l.length → (l ++ [a]).getD k false = l.getD k false := by
    intro l a k hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have getD_snoc_eq : ∀ (l : List Bool) (a : Bool),
      (l ++ [a]).getD l.length false = a := by
    intro l a
    simp [List.getD_eq_getElem?_getD]
  have getD_snoc_len : ∀ (l : List Bool) (a : Bool) (n : ℕ),
      n = l.length → (l ++ [a]).getD n false = a := by
    intro l a n hn
    subst hn
    exact getD_snoc_eq l a
  have getD_ge : ∀ (l : List Bool) (k : ℕ),
      l.length ≤ k → l.getD k false = false := by
    intro l k hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
  have getD_ofFn : ∀ (z : Fin 9 → Bool) (k : ℕ) (hk : k < 9),
      (List.ofFn z).getD k false = z ⟨k, hk⟩ := by
    intro z k hk
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn]
  let isNot : PEqualNP.CircuitLowerBounds.Gate → Bool :=
    fun g => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op
  have hNoNot : ∀ g ∈ C.gates, isNot g = false := by
    have hc : List.countP isNot C.gates = 0 := hZeroNot
    rw [List.countP_eq_zero] at hc
    intro g hg
    cases h : isNot g
    · rfl
    · exact absurd (hc g hg) (by rw [h]; decide)
  have hAO : ∀ g ∈ C.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hFan g hg
    refine ⟨?_, hlen⟩
    have hnn := hNoNot g hg
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      dsimp only [isNot] at hnn
      rw [h] at hnn
      cases hnn
  have hLen15 : C.gates.length = 15 := hSize
  rcases hGates : C.gates with _ | ⟨g0, gs⟩
  · rw [hGates] at hLen15; cases hLen15
  have hGsLen : gs.length = 14 := by
    rw [hGates, List.length_cons] at hLen15
    omega
  have hGsAO : ∀ g ∈ gs,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    exact hAO g (by rw [hGates]; exact List.mem_cons_of_mem g0 hg)
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hPres : ∀ (l : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (l.foldl step w).getD i false = w.getD i false := by
    intro l
    induction l with
    | nil => intro _ _ _; rfl
    | cons g rest ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ i (by simp [step]; omega)]
      exact getD_snoc_lt w _ i hi
  have hWiresC : ∀ x : Fin 9 → Bool,
      C.wires (List.ofFn x) = gs.foldl step (List.ofFn x ++ [x 0 && x 2]) := by
    intro x
    have hw9 := hWire9 x
    have hInit : step (List.ofFn x) g0 =
        List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)] := rfl
    have hFoldC : C.wires (List.ofFn x) = gs.foldl step (step (List.ofFn x) g0) := by
      change C.gates.foldl step (List.ofFn x) = gs.foldl step (step (List.ofFn x) g0)
      rw [hGates, List.foldl_cons]
    have h9lt : 9 < (step (List.ofFn x) g0).length := by simp [step]
    have h9eq : (step (List.ofFn x) g0).getD 9 false = (x 0 && x 2) := by
      rw [← hPres gs (step (List.ofFn x) g0) 9 h9lt, ← hFoldC]
      exact hw9
    have h9val : g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 && x 2) := by
      rw [hInit, getD_snoc_len (List.ofFn x) _ 9 List.length_ofFn.symm] at h9eq
      exact h9eq
    rw [hFoldC, hInit, h9val]
  let ρ : ℕ → ℕ := fun w => if w < 9 then w else if w = 9 then 23 else w - 1
  let mapGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun g => ⟨g.op, g.inputs.map ρ⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs.map mapGate, ρ C.output⟩
  have hDSize : D.size = 14 := by
    change D.gates.length = 14
    dsimp only [D]
    rw [List.length_map, hGsLen]
  have hDMono : PEqualNP.MetaComplexity.Monotone2 D := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨g', hg', rfl⟩
    obtain ⟨hop, hlen⟩ := hGsAO g' hg'
    refine ⟨?_, ?_⟩
    · rcases hop with h | h
      · exact Or.inl h
      · exact Or.inr h
    · dsimp only [mapGate]
      rw [List.length_map]
      exact hlen
  have hShift : ∀ (l : List PEqualNP.CircuitLowerBounds.Gate) (wF wD : List Bool),
      wF.length = wD.length + 1 →
      9 ≤ wD.length →
      wD.length + l.length ≤ 23 →
      (∀ i < 9, wF.getD i false = wD.getD i false) →
      wF.getD 9 false = false →
      (∀ i, 10 ≤ i → i < wF.length → wF.getD i false = wD.getD (i - 1) false) →
      ∀ w : ℕ, ((l.map mapGate).foldl step wD).getD (ρ w) false =
        (l.foldl step wF).getD w false := by
    intro l
    induction l with
    | nil =>
      intro wF wD hlen h9 h23 hlt9 h9f hge10 w
      dsimp only [List.map, List.foldl, ρ]
      split_ifs with hw9 hw9eq
      · exact (hlt9 w hw9).symm
      · subst hw9eq
        rw [h9f, getD_ge wD 23 (by omega)]
      · by_cases hwlt : w < wF.length
        · exact (hge10 w (by omega) hwlt).symm
        · rw [getD_ge wD (w - 1) (by omega), getD_ge wF w (by omega)]
    | cons g rest ih =>
      intro wF wD hlen h9 h23 hlt9 h9f hge10 w
      have hInEq : ((g.inputs.map ρ).map fun i => wD.getD i false) =
          (g.inputs.map fun i => wF.getD i false) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        dsimp only [Function.comp_apply, ρ]
        split_ifs with hi9 hi9eq
        · exact (hlt9 i hi9).symm
        · subst hi9eq
          rw [h9f, getD_ge wD 23 (by omega)]
        · by_cases hilt : i < wF.length
          · exact (hge10 i (by omega) hilt).symm
          · rw [getD_ge wD (i - 1) (by omega), getD_ge wF i (by omega)]
      let b : Bool := g.op.eval (g.inputs.map fun i => wF.getD i false)
      have hStepD : step wD (mapGate g) = wD ++ [b] := by
        dsimp only [step, mapGate, b]
        rw [hInEq]
      have hStepF : step wF g = wF ++ [b] := rfl
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, hStepD, hStepF]
      apply ih (wF ++ [b]) (wD ++ [b])
      · simp only [List.length_append, List.length_singleton]; omega
      · simp only [List.length_append, List.length_singleton]; omega
      · simp only [List.length_cons] at h23
        simp only [List.length_append, List.length_singleton]; omega
      · intro i hi
        rw [getD_snoc_lt wF b i (by omega), getD_snoc_lt wD b i (by omega)]
        exact hlt9 i hi
      · rw [getD_snoc_lt wF b 9 (by omega)]
        exact h9f
      · intro i hi10 hilt
        simp only [List.length_append, List.length_singleton] at hilt
        by_cases hilt' : i < wF.length
        · rw [getD_snoc_lt wF b i hilt', getD_snoc_lt wD b (i - 1) (by omega)]
          exact hge10 i hi10 hilt'
        · have hieq : i = wF.length := by omega
          have hw1eq : wF.length - 1 = wD.length := by omega
          rw [hieq, hw1eq, getD_snoc_eq wF b, getD_snoc_eq wD b]
  have hDEval : ∀ x : Fin 9 → Bool,
      D.eval (List.ofFn x) = (gs.foldl step (List.ofFn x ++ [false])).getD C.output false := by
    intro x
    change ((gs.map mapGate).foldl step (List.ofFn x)).getD (ρ C.output) false = _
    apply hShift gs (List.ofFn x ++ [false]) (List.ofFn x)
    · simp
    · simp
    · simp [hGsLen]
    · intro i hi
      exact getD_snoc_lt (List.ofFn x) false i (by rw [List.length_ofFn]; exact hi)
    · exact getD_snoc_len (List.ofFn x) false 9 List.length_ofFn.symm
    · intro i hi10 hilt
      simp only [List.length_append, List.length_ofFn, List.length_singleton] at hilt
      omega
  have hOpMono : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp),
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∀ (l1 l2 : List Bool), l1.length = l2.length →
      (∀ k < l1.length, l1.getD k false = true → l2.getD k false = true) →
      op.eval l1 = true → op.eval l2 = true := by
    intro op hop l1
    induction l1 with
    | nil =>
      intro l2 hlen _ hev
      cases l2 with
      | nil => exact hev
      | cons _ _ => simp at hlen
    | cons a1 r1 ih =>
      intro l2 hlen hle hev
      cases l2 with
      | nil => simp at hlen
      | cons a2 r2 =>
        simp only [List.length_cons] at hlen
        have ha : a1 = true → a2 = true := by
          have h0 := hle 0 (by simp)
          simpa using h0
        have hr : ∀ k < r1.length, r1.getD k false = true → r2.getD k false = true := by
          intro k hk
          have hk1 := hle (k + 1) (by simp; omega)
          simpa using hk1
        rcases hop with rfl | rfl
        · change (a1 && r1.all id) = true at hev
          change (a2 && r2.all id) = true
          rw [Bool.and_eq_true] at hev ⊢
          exact ⟨ha hev.1, ih r2 (by omega) hr hev.2⟩
        · change (a1 || r1.any id) = true at hev
          change (a2 || r2.any id) = true
          rw [Bool.or_eq_true] at hev ⊢
          rcases hev with h1 | h2
          · exact Or.inl (ha h1)
          · exact Or.inr (ih r2 (by omega) hr h2)
  have hFoldMono : ∀ (l : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ l, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
      ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ k < w1.length, w1.getD k false = true → w2.getD k false = true) →
      ∀ k < (l.foldl step w1).length,
      (l.foldl step w1).getD k false = true → (l.foldl step w2).getD k false = true := by
    intro l
    induction l with
    | nil =>
      intro _ w1 w2 _ hle k hk
      exact hle k hk
    | cons g rest ih =>
      intro hl w1 w2 hlen hle k hk
      rw [List.foldl_cons] at hk ⊢
      rw [List.foldl_cons]
      have hg := (hl g (List.mem_cons_self)).1
      have hrest : ∀ g' ∈ rest, (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hl g' (List.mem_cons_of_mem g hg')
      apply ih hrest (step w1 g) (step w2 g)
      · simp [step, hlen]
      · intro j hj
        simp only [step, List.length_append, List.length_singleton] at hj
        by_cases hjlt : j < w1.length
        · dsimp only [step]
          rw [getD_snoc_lt w1 _ j hjlt, getD_snoc_lt w2 _ j (by omega)]
          exact hle j hjlt
        · have hjeq1 : j = w1.length := by omega
          have hjeq2 : j = w2.length := by omega
          dsimp only [step]
          rw [hjeq1, getD_snoc_eq w1 _]
          rw [← hjeq1, hjeq2, getD_snoc_eq w2 _]
          apply hOpMono g.op hg (g.inputs.map fun i => w1.getD i false) (g.inputs.map fun i => w2.getD i false)
          · simp
          · intro m hm
            rw [List.length_map] at hm
            rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm),
              List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm),
              List.getElem_map, List.getElem_map]
            by_cases him : g.inputs[m] < w1.length
            · exact hle g.inputs[m] him
            · intro hfalse
              rw [getD_ge w1 g.inputs[m] (by omega)] at hfalse
              cases hfalse
      · exact hk
  let eFin : List (Fin 9 × Fin 9) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
  let fTarget : (Fin 9 → Bool) → Bool :=
    fun x6 => x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 ||
      x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5
  have hTargetAny : ∀ x : Fin 9 → Bool, fTarget x = eFin.any (fun p => x p.1 && x p.2) := by
    intro x
    dsimp only [fTarget, eFin, List.any]
    simp only [Bool.or_false, Bool.or_assoc]
  have hAdjIff : ∀ u v : Fin 9,
      (PEqualNP.EdgeOwnership.edgeGraph 9
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]).Adj u v ↔
      ((u, v) ∈ eFin ∨ (v, u) ∈ eFin) := by
    decide
  have hGraphEq : ∀ x : Fin 9 → Bool,
      fTarget x = PEqualNP.MetaComplexity.NestedCover.graphFun
        (PEqualNP.EdgeOwnership.edgeGraph 9
          [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]) ∅ x := by
    intro x
    rw [hTargetAny x]
    change eFin.any (fun p => x p.1 && x p.2) =
      (decide (∃ i ∈ (∅ : Finset (Fin 9)), x i = true) ||
       decide (∃ u v : Fin 9,
        (PEqualNP.EdgeOwnership.edgeGraph 9
          [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]).Adj u v ∧
        x u = true ∧ x v = true))
    have hemp : decide (∃ i ∈ (∅ : Finset (Fin 9)), x i = true) = false := by simp
    rw [hemp, Bool.false_or, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    constructor
    · rintro ⟨⟨u, v⟩, hmem, huv⟩
      rw [Bool.and_eq_true] at huv
      exact ⟨u, v, (hAdjIff u v).mpr (Or.inl hmem), huv.1, huv.2⟩
    · rintro ⟨u, v, hadj, hu, hv⟩
      rcases (hAdjIff u v).mp hadj with h1 | h2
      · exact ⟨(u, v), h1, by rw [hu, hv]; rfl⟩
      · exact ⟨(v, u), h2, by rw [hv, hu]; rfl⟩
  have hPairFacts : ∀ p ∈ eFin,
      (decide ((0 : Fin 9) = p.1 ∨ (0 : Fin 9) = p.2) &&
        decide ((2 : Fin 9) = p.1 ∨ (2 : Fin 9) = p.2)) = false ∧
      eFin.any (fun q => decide (q.1 = p.1 ∨ q.1 = p.2) && decide (q.2 = p.1 ∨ q.2 = p.2)) = true := by
    decide
  have hEdgeWitness : ∀ x : Fin 9 → Bool, fTarget x = true →
      ∃ y : Fin 9 → Bool, (∀ i : Fin 9, y i = true → x i = true) ∧ (y 0 && y 2) = false ∧ fTarget y = true := by
    intro x hfx
    rw [hTargetAny x, List.any_eq_true] at hfx
    obtain ⟨p, hp, hpx⟩ := hfx
    rw [Bool.and_eq_true] at hpx
    refine ⟨fun i => decide (i = p.1 ∨ i = p.2), ?_, (hPairFacts p hp).1, ?_⟩
    · intro i hi
      rcases of_decide_eq_true hi with rfl | rfl
      · exact hpx.1
      · exact hpx.2
    · rw [hTargetAny (fun i => decide (i = p.1 ∨ i = p.2))]
      exact (hPairFacts p hp).2
  have hDFun : PEqualNP.MetaComplexity.circuitFun 9 D =
      PEqualNP.MetaComplexity.NestedCover.graphFun
        (PEqualNP.EdgeOwnership.edgeGraph 9
          [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]) ∅ := by
    funext x
    rw [← hGraphEq x]
    have hCFunX : C.eval (List.ofFn x) = fTarget x := congr_fun hFun x
    change D.eval (List.ofFn x) = fTarget x
    rw [hDEval x]
    have hCEvalX : (gs.foldl step (List.ofFn x ++ [x 0 && x 2])).getD C.output false = fTarget x := by
      rw [← hWiresC x]
      exact hCFunX
    cases hfx : fTarget x
    · by_contra hne
      have htrue : (gs.foldl step (List.ofFn x ++ [false])).getD C.output false = true := by
        cases h : (gs.foldl step (List.ofFn x ++ [false])).getD C.output false
        · exact absurd h hne
        · rfl
      have houtlt : C.output < (gs.foldl step (List.ofFn x ++ [false])).length := by
        by_contra hge
        rw [getD_ge _ _ (by omega)] at htrue
        cases htrue
      have hup : (gs.foldl step (List.ofFn x ++ [x 0 && x 2])).getD C.output false = true := by
        apply hFoldMono gs hGsAO (List.ofFn x ++ [false]) (List.ofFn x ++ [x 0 && x 2]) (by simp) _ C.output houtlt htrue
        intro k hk
        simp only [List.length_append, List.length_ofFn, List.length_singleton] at hk
        by_cases hk9 : k < 9
        · rw [getD_snoc_lt (List.ofFn x) false k (by rw [List.length_ofFn]; exact hk9),
            getD_snoc_lt (List.ofFn x) (x 0 && x 2) k (by rw [List.length_ofFn]; exact hk9)]
          exact id
        · have hkeq : k = (List.ofFn x).length := by rw [List.length_ofFn]; omega
          rw [hkeq, getD_snoc_eq (List.ofFn x) false]
          intro hf; cases hf
      rw [hCEvalX, hfx] at hup
      cases hup
    · obtain ⟨y, hylex, hy02, hfy⟩ := hEdgeWitness x hfx
      have hCy : (gs.foldl step (List.ofFn y ++ [false])).getD C.output false = true := by
        have hCEvalY : (gs.foldl step (List.ofFn y ++ [y 0 && y 2])).getD C.output false = fTarget y := by
          rw [← hWiresC y]
          exact congr_fun hFun y
        rw [hy02, hfy] at hCEvalY
        exact hCEvalY
      have houtlt : C.output < (gs.foldl step (List.ofFn y ++ [false])).length := by
        by_contra hge
        rw [getD_ge _ _ (by omega)] at hCy
        cases hCy
      apply hFoldMono gs hGsAO (List.ofFn y ++ [false]) (List.ofFn x ++ [false]) (by simp) _ C.output houtlt hCy
      intro k hk
      simp only [List.length_append, List.length_ofFn, List.length_singleton] at hk
      by_cases hk9 : k < 9
      · rw [getD_snoc_lt (List.ofFn y) false k (by rw [List.length_ofFn]; exact hk9),
          getD_snoc_lt (List.ofFn x) false k (by rw [List.length_ofFn]; exact hk9),
          getD_ofFn y k hk9, getD_ofFn x k hk9]
        exact hylex ⟨k, hk9⟩
      · have hkeqy : k = (List.ofFn y).length := by rw [List.length_ofFn]; omega
        rw [hkeqy, getD_snoc_eq (List.ofFn y) false]
        intro hf; cases hf
  by_cases hj0 : (PEqualNP.TopForm.junk
      (PEqualNP.EdgeOwnership.edgeGraph 9
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]) D).card = 0
  · exact h0 D hDMono hDSize hj0 hDFun
  · by_cases hj1 : (PEqualNP.TopForm.junk
        (PEqualNP.EdgeOwnership.edgeGraph 9
          [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]) D).card = 1
    · exact h1 D hDMono hDSize hj1 hDFun
    · exact h2 D hDMono hDSize (by omega) hDFun
