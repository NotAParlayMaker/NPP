import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

/-- Reduction of L-meta-1675 (weight 90):
    Internally proves:
    1. Minimalization via `Nat.find`: replaces `C` with a minimum-size `FanInTwo` circuit `C'`
       with first gate `y 0 || y 3` computing `f9`.
    2. Output-wire bounds: `9 ≤ C'.output ∧ C'.output < 9 + C'.size` (and `1 ≤ C'.size`).
    3. When `notCount C' = 1`, the output gate cannot be `.not` (otherwise every preceding gate
       is `.and`/`.or`, making `C'` anti-monotone between `allFalse` and `allTrue`, contradicting
       `f9 allFalse = false` and `f9 allTrue = true`).
    Splits the remaining minimal circuits (`C'.size ≤ 15`) by `notCount C'`: `monotone` (= 0),
    `one_not` (= 1, with non-NOT output), and `multi_not` (≥ 2). -/
theorem PEqualNP.Outside.R_meta_1675_512
    (monotone :
      let f9 : (Fin 9 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
        (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit,
        FanInTwo C →
        (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
        circuitFun 9 C = f9 →
        (∀ C' : Circuit, FanInTwo C' →
          (∀ y : Fin 9 → Bool, (C'.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
          circuitFun 9 C' = f9 → C.size ≤ C'.size) →
        C.size ≤ 15 →
        9 ≤ C.output →
        C.output < 9 + C.size →
        notCount C = 0 →
        False)
    (one_not :
      let f9 : (Fin 9 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
        (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit,
        FanInTwo C →
        (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
        circuitFun 9 C = f9 →
        (∀ C' : Circuit, FanInTwo C' →
          (∀ y : Fin 9 → Bool, (C'.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
          circuitFun 9 C' = f9 → C.size ≤ C'.size) →
        C.size ≤ 15 →
        9 ≤ C.output →
        C.output < 9 + C.size →
        notCount C = 1 →
        (gateAt C (C.output - 9)).op ≠ GateOp.not →
        False)
    (multi_not :
      let f9 : (Fin 9 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
        (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit,
        FanInTwo C →
        (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
        circuitFun 9 C = f9 →
        (∀ C' : Circuit, FanInTwo C' →
          (∀ y : Fin 9 → Bool, (C'.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
          circuitFun 9 C' = f9 → C.size ≤ C'.size) →
        C.size ≤ 15 →
        9 ≤ C.output →
        C.output < 9 + C.size →
        2 ≤ notCount C →
        False) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
          (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
          (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size := by
  classical
  intro C0 hfan0 hg0_0 hfun0
  by_contra hlt16
  have hle15 : C0.size ≤ 15 := by omega
  let f9 : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  -- Step 1: Minimalize C0 via Nat.find
  let P : ℕ → Prop := fun s =>
    ∃ C : Circuit, FanInTwo C ∧
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) ∧
      circuitFun 9 C = f9 ∧ C.size = s
  have hP_ex : ∃ s, P s := ⟨C0.size, C0, hfan0, hg0_0, hfun0, rfl⟩
  have hsMin_le : Nat.find hP_ex ≤ C0.size := Nat.find_min' hP_ex ⟨C0, hfan0, hg0_0, hfun0, rfl⟩
  rcases Nat.find_spec hP_ex with ⟨C, hfan, hg0, hfun, hszEq⟩
  have hsz15 : C.size ≤ 15 := by omega
  have hmin : ∀ C' : Circuit, FanInTwo C' →
      (∀ y : Fin 9 → Bool, (C'.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      circuitFun 9 C' = f9 → C.size ≤ C'.size := by
    intro C' h1 h2 h3
    rw [hszEq]
    exact Nat.find_min' hP_ex ⟨C', h1, h2, h3, rfl⟩
  -- Helper: wireStep length and earlier-entry preservation
  let wireStep : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]
  have hfold_len : ∀ (gs : List Gate) (ws : List Bool),
      (gs.foldl wireStep ws).length = ws.length + gs.length := by
    intro gs; induction gs with
    | nil => intro ws; simp
    | cons g r ih =>
      intro ws; simp only [List.foldl_cons, List.length_cons]
      rw [ih]; simp [wireStep]; omega
  have hfold_prev : ∀ (gs : List Gate) (ws : List Bool) (w : ℕ),
      w < ws.length → (gs.foldl wireStep ws).getD w false = ws.getD w false := by
    intro gs; induction gs with
    | nil => intro ws w _; rfl
    | cons g r ih =>
      intro ws w hw
      simp only [List.foldl_cons]
      rw [ih (wireStep ws g) w (by simp [wireStep]; omega)]
      dsimp only [wireStep]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hw, ← List.getD_eq_getElem?_getD]
  -- Step 2: Output wire bounds 9 ≤ C.output < 9 + C.size
  have houtGe : 9 ≤ C.output := by
    by_contra hlt
    push Not at hlt
    let i0 : Fin 9 := ⟨C.output, hlt⟩
    let x : Fin 9 → Bool := fun k => decide (k = i0)
    have hCx : circuitFun 9 C x = true := by
      unfold circuitFun Circuit.eval Circuit.wires
      change (C.gates.foldl wireStep (List.ofFn x)).getD C.output false = true
      rw [hfold_prev _ _ C.output (by simp [hlt]),
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlt]),
          Option.getD_some, List.getElem_ofFn]
      simp [x, i0]
    have hfx : f9 x = false := by
      have hAll : ∀ j : Fin 9, f9 (fun k => decide (k = j)) = false := by decide
      exact hAll i0
    have hEq := congrFun hfun x
    rw [hCx, hfx] at hEq
    contradiction
  have houtLt : C.output < 9 + C.size := by
    by_contra hge
    push Not at hge
    let x1 : Fin 9 → Bool := fun _ => true
    have hCx : circuitFun 9 C x1 = false := by
      unfold circuitFun Circuit.eval Circuit.wires
      change (C.gates.foldl wireStep (List.ofFn x1)).getD C.output false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
      · rfl
      · rw [hfold_len, List.length_ofFn]; exact hge
    have hfx : f9 x1 = true := by simp [f9, x1]
    have hEq := congrFun hfun x1
    rw [hCx, hfx] at hEq
    contradiction
  -- Step 3: Split by notCount C
  by_cases hn0 : notCount C = 0
  · exact monotone C hfan hg0 hfun hmin hsz15 houtGe houtLt hn0
  · by_cases hn1 : notCount C = 1
    · -- Prove output gate cannot be .not when notCount C = 1
      have houtNot : (gateAt C (C.output - 9)).op ≠ GateOp.not := by
        intro hnotOut
        let k := C.output - 9
        have hk : k < C.gates.length := by change C.output < 9 + C.gates.length at houtLt; omega
        have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
          conv_lhs => rw [← List.take_append_drop k C.gates]
          congr 1; rw [List.drop_eq_getElem_cons hk]
        have hgatk : gateAt C k = C.gates[k] := by
          unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
        have hgkNot : (C.gates[k]).op = GateOp.not := by rwa [← hgatk]
        have htakeNoNot : ∀ g ∈ C.gates.take k, g.op ≠ GateOp.not := by
          intro g hg hgop
          have hcnt : notCount C =
              notCount ⟨C.gates.take k, 0⟩ + notCount ⟨C.gates[k] :: C.gates.drop (k + 1), 0⟩ := by
            unfold notCount; dsimp only
            conv_lhs => rw [hsplit]
            rw [List.filter_append, List.length_append]
          have h1 : 1 ≤ notCount ⟨C.gates.take k, 0⟩ := by
            unfold notCount
            exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, by simp [hgop]⟩)
          have h2 : 1 ≤ notCount ⟨C.gates[k] :: C.gates.drop (k + 1), 0⟩ := by
            unfold notCount
            exact @List.length_pos_of_mem _ C.gates[k] _
              (List.mem_filter.mpr ⟨List.mem_cons_self, by simp [hgkNot]⟩)
          omega
        have htakeAO : ∀ g ∈ C.gates.take k, g.op = GateOp.and ∨ g.op = GateOp.or := by
          intro g hg
          rcases hfan g (List.mem_of_mem_take hg) with ⟨h | h | h, _⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact (htakeNoNot g hg h).elim
        have hfold_mono : ∀ (gs : List Gate) (w0 w1 : List Bool),
            w0.length = w1.length →
            (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
            (∀ i, w0.getD i false = true → w1.getD i false = true) →
            ∀ i, (gs.foldl wireStep w0).getD i false = true →
              (gs.foldl wireStep w1).getD i false = true := by
          intro gs; induction gs with
          | nil => intro w0 w1 _ _ hle; exact hle
          | cons g r ih =>
            intro w0 w1 hlen hno hle
            simp only [List.foldl_cons]
            have hstep : g.op.eval (g.inputs.map (fun i => w0.getD i false)) = true →
                g.op.eval (g.inputs.map (fun i => w1.getD i false)) = true := by
              rcases hno g (by simp) with hop | hop
              · rw [hop]
                change (g.inputs.map (fun i => w0.getD i false)).all id = true →
                  (g.inputs.map (fun i => w1.getD i false)).all id = true
                simp only [List.all_eq_true, List.mem_map, id_eq]
                intro h b hb; rcases hb with ⟨u, hu, rfl⟩
                exact hle u (h (w0.getD u false) ⟨u, hu, rfl⟩)
              · rw [hop]
                change (g.inputs.map (fun i => w0.getD i false)).any id = true →
                  (g.inputs.map (fun i => w1.getD i false)).any id = true
                simp only [List.any_eq_true, List.mem_map, id_eq]
                rintro ⟨_, ⟨u, hu, rfl⟩, htrue⟩
                exact ⟨w1.getD u false, ⟨u, hu, rfl⟩, hle u htrue⟩
            apply ih (wireStep w0 g) (wireStep w1 g) (by simp [wireStep, hlen])
              (fun g' hg' => hno g' (by simp [hg']))
            intro i hi
            dsimp only [wireStep] at hi ⊢
            by_cases hlt : i < w0.length
            · have hlt1 : i < w1.length := by omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hi
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1, ← List.getD_eq_getElem?_getD]
              exact hle i hi
            · by_cases heq : i = w0.length
              · rw [heq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)] at hi
                simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
                rw [heq, hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
                simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
                exact hstep hi
              · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
                simp at hi
        let x0 : Fin 9 → Bool := fun _ => false
        let x1 : Fin 9 → Bool := fun _ => true
        have hinit_mono : ∀ i, (List.ofFn x0).getD i false = true → (List.ofFn x1).getD i false = true := by
          intro i hi
          by_cases hlt : i < 9
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlt]),
                Option.getD_some, List.getElem_ofFn] at hi
            simp [x0] at hi
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
            simp at hi
        let w0 := (C.gates.take k).foldl wireStep (List.ofFn x0)
        let w1 := (C.gates.take k).foldl wireStep (List.ofFn x1)
        have hw_mono : ∀ i, w0.getD i false = true → w1.getD i false = true :=
          hfold_mono (C.gates.take k) (List.ofFn x0) (List.ofFn x1) (by simp) htakeAO hinit_mono
        have heval_at : ∀ (x : Fin 9 → Bool),
            let wk := (C.gates.take k).foldl wireStep (List.ofFn x)
            circuitFun 9 C x = !((C.gates[k].inputs.map (fun i => wk.getD i false)).headD false) := by
          intro x wk
          unfold circuitFun Circuit.eval Circuit.wires
          change (C.gates.foldl wireStep (List.ofFn x)).getD C.output false = _
          conv_lhs => rw [hsplit]
          rw [List.foldl_append, List.foldl_cons]
          change ((C.gates.drop (k + 1)).foldl wireStep (wireStep wk C.gates[k])).getD C.output false = _
          have hwk_len : wk.length = C.output := by
            dsimp only [wk]; rw [hfold_len]; simp [List.length_take, Nat.min_eq_left hk.le]; omega
          rw [hfold_prev _ _ C.output (by simp [wireStep, hwk_len])]
          dsimp only [wireStep]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hwk_len]
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hgkNot]
          rfl
        have h0 := heval_at x0
        have h1 := heval_at x1
        cases hhead0 : (C.gates[k].inputs.map (fun i => w0.getD i false)).headD false with
        | false =>
          have hEq := congrFun hfun x0
          rw [h0, hhead0] at hEq
          simp [f9, x0] at hEq
        | true =>
          have hhead1 : (C.gates[k].inputs.map (fun i => w1.getD i false)).headD false = true := by
            cases hin : C.gates[k].inputs with
            | nil => simp [hin] at hhead0
            | cons u tl =>
              rw [hin] at hhead0
              simpa using hw_mono u (by simpa using hhead0)
          have hEq := congrFun hfun x1
          rw [h1, hhead1] at hEq
          simp [f9, x1] at hEq
      exact one_not C hfan hg0 hfun hmin hsz15 houtGe houtLt hn1 houtNot
    · exact multi_not C hfan hg0 hfun hmin hsz15 houtGe houtLt (by omega)
