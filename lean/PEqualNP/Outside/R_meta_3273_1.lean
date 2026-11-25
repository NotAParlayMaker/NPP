import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3273_1
    (h1 :
      ∀ (b : Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 →
          x3.size - PEqualNP.NotBracket.notCount x3 ≤ (12 : ℕ) →
            ∃ (x6 : Fin (9 : ℕ) → Bool),
              x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [b]) ≠
                (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
                  x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
                  x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
                  x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
                  x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
                  x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
                  x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
                  x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                  x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                  x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                  x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                  x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h2 :
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x3 →
          x3.size ≤ (13 : ℕ) →
            ∃ (x6 : Fin (9 : ℕ) → Bool),
              x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [Bool.false]) ≠
                (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
                  x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
                  x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
                  x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
                  x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
                  x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
                  x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
                  x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                  x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                  x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                  x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                  x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h3 :
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x3 →
          x3.size ≤ (13 : ℕ) →
            ∃ (x6 : Fin (9 : ℕ) → Bool),
              x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [Bool.true]) ≠
                (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
                  x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
                  x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
                  x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
                  x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
                  x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
                  x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
                  x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                  x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                  x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                  x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                  x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ x1 ∈ [((0 : Fin (12 : ℕ)), (0 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (1 : Fin (12 : ℕ))),
      ((2 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))),
      ((4 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))),
      ((9 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((10 : Fin (12 : ℕ)), (10 : Fin (12 : ℕ))),
      ((11 : Fin (12 : ℕ)), (11 : Fin (12 : ℕ)))],
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 →
          x3.size ≤ (13 : ℕ) →
            ∃ (x6 : Fin (9 : ℕ) → Bool),
              have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];
              have x8 : Fin (12 : ℕ) → Bool := fun (x8 : Fin (12 : ℕ)) =>
                if x8 = (11 : Fin (12 : ℕ)) then Bool.true else x7.getD (↑x8) Bool.false;
              x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) ≠
                (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
                  x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
                  x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
                  x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
                  x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
                  x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
                  x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
                  x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                  x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                  x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                  x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                  x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 x3 hfan hsize
  have hbase : ∀ (b : Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
        ∃ (x6 : Fin 9 → Bool),
          C.eval (List.ofFn x6 ++ [!x6 0] ++ [b]) ≠
            (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 ||
              x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 ||
              x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5) := by
    intro b C hCfan hCsize
    by_cases hnot : PEqualNP.NotBracket.notCount C = 0
    · have hmono : PEqualNP.MetaComplexity.Monotone2 C := by
        intro g hg
        have hnil := List.length_eq_zero_iff.mp hnot
        have hne : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
          have hfalse := (List.filter_eq_nil_iff.mp hnil) g hg
          intro heq
          exact hfalse (by simp [heq])
        obtain ⟨hop, hlen⟩ := hCfan g hg
        refine ⟨?_, hlen⟩
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact False.elim (hne h)
      cases b
      · exact h2 C hmono hCsize
      · exact h3 C hmono hCsize
    · exact h1 b C hCfan (by omega)
  have hcopy : ∀ (t : ℕ), t < 10 →
      ∃ (x6 : Fin 9 → Bool),
        x3.eval (List.ofFn x6 ++ [!x6 0] ++ [(List.ofFn x6 ++ [!x6 0]).getD t false]) ≠
          (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 ||
            x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 ||
            x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5) := by
    intro t ht
    let rwIdx : ℕ → ℕ := fun w => if w = 10 then t else w
    let rwGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
      fun g => { op := g.op, inputs := g.inputs.map rwIdx }
    let C' : PEqualNP.CircuitLowerBounds.Circuit :=
      { gates := x3.gates.map rwGate, output := rwIdx x3.output }
    have hC'fan : PEqualNP.MetaComplexity.FanInTwo C' := by
      intro g hg
      rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
      obtain ⟨hop, hlen⟩ := hfan g0 hg0
      exact ⟨hop, by rw [List.length_map]; exact hlen⟩
    have hC'size : C'.size ≤ 13 := by
      change (x3.gates.map rwGate).length ≤ 13
      rw [List.length_map]
      exact hsize
    obtain ⟨x6, hx6⟩ := hbase false C' hC'fan hC'size
    refine ⟨x6, ?_⟩
    have heval : C'.eval (List.ofFn x6 ++ [!x6 0] ++ [false]) =
        x3.eval (List.ofFn x6 ++ [!x6 0] ++ [(List.ofFn x6 ++ [!x6 0]).getD t false]) := by
      let x7 : List Bool := List.ofFn x6 ++ [!x6 0]
      let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
        fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have hfold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w1 w2 : List Bool),
          w1.length = w2.length → 11 ≤ w1.length →
          (∀ i, i ≠ 10 → w1.getD i false = w2.getD i false) →
          w1.getD t false = w2.getD 10 false →
          ((gs.map rwGate).foldl step w1).length = (gs.foldl step w2).length ∧
          (∀ i, i ≠ 10 → ((gs.map rwGate).foldl step w1).getD i false = (gs.foldl step w2).getD i false) ∧
          ((gs.map rwGate).foldl step w1).getD t false = (gs.foldl step w2).getD 10 false := by
        intro gs
        induction gs with
        | nil =>
          intro w1 w2 hlen _ hne ht10
          exact ⟨hlen, hne, ht10⟩
        | cons g rest ih =>
          intro w1 w2 hlen hge hne ht10
          simp only [List.map_cons, List.foldl_cons]
          have hval : (rwGate g).op.eval ((rwGate g).inputs.map fun i => w1.getD i false) =
              g.op.eval (g.inputs.map fun i => w2.getD i false) := by
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro i _
            change w1.getD (if i = 10 then t else i) false = w2.getD i false
            by_cases hi : i = 10
            · subst hi; simp only [ite_true]; exact ht10
            · simp only [hi, ite_false]; exact hne i hi
          apply ih (step w1 (rwGate g)) (step w2 g)
          · simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]
          · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          · intro i hi
            change (w1 ++ [(rwGate g).op.eval ((rwGate g).inputs.map fun j => w1.getD j false)]).getD i false =
              (w2 ++ [g.op.eval (g.inputs.map fun j => w2.getD j false)]).getD i false
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
            by_cases hlt : i < w1.length
            · rw [List.getElem?_append_left hlt, List.getElem?_append_left (by omega : i < w2.length)]
              have := hne i hi
              rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
              exact this
            · rw [List.getElem?_append_right (by omega : w1.length ≤ i),
                List.getElem?_append_right (by omega : w2.length ≤ i), hlen, hval]
          · change (w1 ++ [(rwGate g).op.eval ((rwGate g).inputs.map fun j => w1.getD j false)]).getD t false =
              (w2 ++ [g.op.eval (g.inputs.map fun j => w2.getD j false)]).getD 10 false
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_left (by omega : t < w1.length),
              List.getElem?_append_left (by omega : 10 < w2.length)]
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at ht10
            exact ht10
      have hx7len : x7.length = 10 := by
        simp only [x7, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have hres := hfold x3.gates (x7 ++ [false]) (x7 ++ [x7.getD t false])
        (by simp only [List.length_append, List.length_cons, List.length_nil])
        (by simp only [List.length_append, List.length_cons, List.length_nil, hx7len]; omega)
        (by
          intro i hi
          simp only [List.getD_eq_getElem?_getD]
          by_cases hlt : i < x7.length
          · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
          · rw [List.getElem?_append_right (by omega : x7.length ≤ i),
              List.getElem?_append_right (by omega : x7.length ≤ i)]
            have hge1 : 1 ≤ i - x7.length := by omega
            rw [List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega),
              List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)])
        (by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega : t < x7.length),
            List.getElem?_append_right (by omega : x7.length ≤ 10), hx7len, Nat.sub_self,
            List.getElem?_singleton]
          rfl)
      change ((x3.gates.map rwGate).foldl step (x7 ++ [false])).getD (rwIdx x3.output) false =
        (x3.gates.foldl step (x7 ++ [x7.getD t false])).getD x3.output false
      by_cases hout : x3.output = 10
      · rw [hout]
        change ((x3.gates.map rwGate).foldl step (x7 ++ [false])).getD t false = _
        exact hres.2.2
      · change ((x3.gates.map rwGate).foldl step (x7 ++ [false])).getD (if x3.output = 10 then t else x3.output) false = _
        simp only [hout, ite_false]
        exact hres.2.1 x3.output hout
    rw [← heval]
    exact hx6
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx1
  rcases hx1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨x6, hx6⟩ := hcopy 0 (by omega)
    refine ⟨x6, ?_⟩
    simpa [Bool.and_self] using hx6
  · obtain ⟨x6, hx6⟩ := hcopy 1 (by omega)
    refine ⟨x6, ?_⟩
    simpa [Bool.and_self] using hx6
  · obtain ⟨x6, hx6⟩ := hcopy 2 (by omega)
    refine ⟨x6, ?_⟩
    simpa [Bool.and_self] using hx6
  · obtain ⟨x6, hx6⟩ := hcopy 3 (by omega)
    refine ⟨x6, ?_⟩
    simpa [Bool.and_self] using hx6
  · obtain ⟨x6, hx6⟩ := hcopy 4 (by omega)
    refine ⟨x6, ?_⟩
    simpa [Bool.and_self] using hx6
  · obtain ⟨x6, hx6⟩ := hcopy 6 (by omega)
    refine ⟨x6, ?_⟩
    simpa [Bool.and_self] using hx6
  · obtain ⟨x6, hx6⟩ := hcopy 9 (by omega)
    refine ⟨x6, ?_⟩
    simpa [Bool.and_self] using hx6
  · obtain ⟨x6, hx6⟩ := hbase false x3 hfan hsize
    refine ⟨x6, ?_⟩
    have h10 : (List.ofFn x6 ++ [!x6 0]).getD 10 false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega
    simpa [h10, Bool.and_self] using hx6
  · obtain ⟨x6, hx6⟩ := hbase true x3 hfan hsize
    refine ⟨x6, ?_⟩
    simpa [Bool.and_self] using hx6
