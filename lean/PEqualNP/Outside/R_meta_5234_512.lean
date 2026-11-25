import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

/-- Reduction of L-meta-5234:
    Internally proves:
    1. When `notCount C = 1`, the output gate cannot be `.not` (otherwise every gate before the
       output is monotone, so the circuit is anti-monotone between `allFalse` and `allTrue`,
       contradicting `petersen allFalse = false` and `petersen allTrue = true`).
    2. When wire 10 (`x 0 || x 2`) is never read by any gate in `C`, shifting wires `≥ 11` down by
       1 yields an equivalent pure 10-input circuit `C'` (`ReadsBack 10`, same size and `notCount`).
    Splits the remaining circuits into `pure10`, `uses10_not1` (with non-NOT output), and `uses10_not2`. -/
theorem PEqualNP.Outside.R_meta_5234_512
    (pure10 :
      ∀ (C : Circuit),
        FanInTwo C →
        ReadsBack 10 C →
        C.size ≤ 18 →
        10 ≤ C.output →
        C.output < 10 + C.size →
        1 ≤ notCount C →
        notCount C ≤ 2 →
        (notCount C = 1 → (gateAt C (C.output - 10)).op ≠ GateOp.not) →
        ∃ (x : Fin 10 → Bool),
          C.eval (List.ofFn x) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
             x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (uses10_not1 :
      ∀ (C : Circuit),
        FanInTwo C →
        ReadsBack 11 C →
        C.size ≤ 18 →
        11 ≤ C.output →
        C.output < 11 + C.size →
        notCount C = 1 →
        (gateAt C (C.output - 11)).op ≠ GateOp.not →
        (∃ g ∈ C.gates, 10 ∈ g.inputs) →
        ∃ (x : Fin 10 → Bool),
          C.eval (List.ofFn x ++ [x 0 || x 2]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
             x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (uses10_not2 :
      ∀ (C : Circuit),
        FanInTwo C →
        ReadsBack 11 C →
        C.size ≤ 18 →
        11 ≤ C.output →
        C.output < 11 + C.size →
        notCount C = 2 →
        (∃ g ∈ C.gates, 10 ∈ g.inputs) →
        ∃ (x : Fin 10 → Bool),
          C.eval (List.ofFn x ++ [x 0 || x 2]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
             x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 →
      x1.size ≤ (18 : ℕ) →
      (11 : ℕ) ≤ x1.output →
      x1.output < (11 : ℕ) + x1.size →
      (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 →
      PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) →
      ∃ (x9 : Fin (10 : ℕ) → Bool),
        x1.eval (List.ofFn x9 ++ [x9 (0 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ))]) ≠
          (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) ||
           x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) ||
           x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) ||
           x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) ||
           x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) ||
           x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) ||
           x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) ||
           x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) ||
           x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) ||
           x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) ||
           x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) ||
           x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) ||
           x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) ||
           x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) ||
           x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))) := by
  intro C hfan hrb hsz houtGe houtLt hnotGe hnotLe
  classical
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
  -- Step 1: Eliminate the case notCount C = 1 with output gate = .not
  by_cases hbadNot : notCount C = 1 ∧ (gateAt C (C.output - 11)).op = GateOp.not
  · rcases hbadNot with ⟨hnot1, houtNot⟩
    let k := C.output - 11
    have hk : k < C.gates.length := by change C.output < 11 + C.gates.length at houtLt; omega
    have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
      conv_lhs => rw [← List.take_append_drop k C.gates]
      congr 1; rw [List.drop_eq_getElem_cons hk]
    have hgatk : gateAt C k = C.gates[k] := by
      unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
    have hgkNot : (C.gates[k]).op = GateOp.not := by rwa [← hgatk]
    -- Every gate in C.gates.take k is NOT a .not gate
    have htakeNoNot : ∀ g ∈ C.gates.take k, g.op ≠ GateOp.not := by
      intro g hg hgop
      have hcnt : notCount C =
          notCount ⟨C.gates.take k, 0⟩ + notCount ⟨C.gates[k] :: C.gates.drop (k + 1), 0⟩ := by
        unfold notCount
        dsimp only
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
      have hgC : g ∈ C.gates := List.mem_of_mem_take hg
      have hno : g.op ≠ GateOp.not := htakeNoNot g hg
      rcases hfan g hgC with ⟨h | h | h, _⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact (hno h).elim
    -- Monotonicity of a NOT-free gate fold
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
        have hgao : g.op = GateOp.and ∨ g.op = GateOp.or := hno g (by simp)
        have hstep : g.op.eval (g.inputs.map (fun i => w0.getD i false)) = true →
            g.op.eval (g.inputs.map (fun i => w1.getD i false)) = true := by
          rcases hgao with hop | hop
          · rw [hop]
            change (g.inputs.map (fun i => w0.getD i false)).all id = true →
              (g.inputs.map (fun i => w1.getD i false)).all id = true
            simp only [List.all_eq_true, List.mem_map, id_eq]
            intro h b hb
            rcases hb with ⟨u, hu, rfl⟩
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
    -- Evaluate C at allFalse vs allTrue
    let x0 : Fin 10 → Bool := fun _ => false
    let x1 : Fin 10 → Bool := fun _ => true
    let init0 := List.ofFn x0 ++ [x0 0 || x0 2]
    let init1 := List.ofFn x1 ++ [x1 0 || x1 2]
    have hinit_len : init0.length = init1.length := by simp [init0, init1]
    have hinit_mono : ∀ i, init0.getD i false = true → init1.getD i false = true := by
      intro i hi
      by_cases hlt : i < 10
      · dsimp only [init0] at hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlt]),
            List.getElem?_eq_getElem (by simp [hlt]), Option.getD_some, List.getElem_ofFn] at hi
        simp [x0] at hi
      · by_cases heq : i = 10
        · dsimp only [init0] at hi
          rw [heq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)] at hi
          simp [x0] at hi
        · dsimp only [init0] at hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi
    let w0 := (C.gates.take k).foldl wireStep init0
    let w1 := (C.gates.take k).foldl wireStep init1
    have hw0_len : w0.length = C.output := by
      dsimp only [w0]; rw [hfold_len]; simp [init0, List.length_take, Nat.min_eq_left hk.le]; omega
    have hw1_len : w1.length = C.output := by
      dsimp only [w1]; rw [hfold_len]; simp [init1, List.length_take, Nat.min_eq_left hk.le]; omega
    have hw_mono : ∀ i, w0.getD i false = true → w1.getD i false = true :=
      hfold_mono (C.gates.take k) init0 init1 hinit_len htakeAO hinit_mono
    have heval_at : ∀ (x : Fin 10 → Bool),
        let init := List.ofFn x ++ [x 0 || x 2]
        let wk := (C.gates.take k).foldl wireStep init
        C.eval init = !((C.gates[k].inputs.map (fun i => wk.getD i false)).headD false) := by
      intro x init wk
      unfold Circuit.eval Circuit.wires
      change (C.gates.foldl wireStep init).getD C.output false = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
      change ((C.gates.drop (k + 1)).foldl wireStep (wireStep wk C.gates[k])).getD C.output false = _
      have hwk_len : wk.length = C.output := by
        dsimp only [wk]; rw [hfold_len]; simp [init, List.length_take, Nat.min_eq_left hk.le]; omega
      rw [hfold_prev _ _ C.output (by simp [wireStep, hwk_len])]
      dsimp only [wireStep]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hwk_len]
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hgkNot]
      rfl
    have h0 := heval_at x0
    have h1 := heval_at x1
    cases hhead0 : (C.gates[k].inputs.map (fun i => w0.getD i false)).headD false with
    | false =>
      refine ⟨x0, ?_⟩
      change C.eval init0 ≠ _
      rw [h0, hhead0]
      simp [x0]
    | true =>
      have hhead1 : (C.gates[k].inputs.map (fun i => w1.getD i false)).headD false = true := by
        cases hin : C.gates[k].inputs with
        | nil => simp [hin] at hhead0
        | cons u tl =>
          rw [hin] at hhead0
          simpa using hw_mono u (by simpa using hhead0)
      refine ⟨x1, ?_⟩
      change C.eval init1 ≠ _
      rw [h1, hhead1]
      simp [x1]
  · -- Not the bad case: if notCount C = 1 then output gate ≠ .not
    have houtNot_ok : notCount C = 1 → (gateAt C (C.output - 11)).op ≠ GateOp.not := by
      intro h1 h2; exact hbadNot ⟨h1, h2⟩
    -- Step 2: Check whether wire 10 is used by any gate in C
    by_cases huse10 : ∃ g ∈ C.gates, 10 ∈ g.inputs
    · by_cases hn1 : notCount C = 1
      · exact uses10_not1 C hfan hrb hsz houtGe houtLt hn1 (houtNot_ok hn1) huse10
      · exact uses10_not2 C hfan hrb hsz houtGe houtLt (by omega) huse10
    · -- Wire 10 is unused: shift all wires ≥ 11 down by 1 to obtain a pure 10-input circuit C'
      push Not at huse10
      let shift : ℕ → ℕ := fun w => if 11 ≤ w then w - 1 else w
      let shiftGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map shift⟩
      let C' : Circuit := ⟨C.gates.map shiftGate, C.output - 1⟩
      have hfan' : FanInTwo C' := by
        intro g hg
        rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
        simpa [shiftGate] using hfan g0 hg0
      have hsz' : C'.size ≤ 18 := by
        change (C.gates.map shiftGate).length ≤ 18
        rw [List.length_map]; exact hsz
      have hrb' : ReadsBack 10 C' := by
        intro j hj i hi
        have hjC : j < C.gates.length := by simpa [C'] using hj
        have hgat' : gateAt C' j = shiftGate (gateAt C j) := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
              List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjC]
          simp [C']
        rw [hgat'] at hi
        rcases List.mem_map.mp hi with ⟨u, hu, rfl⟩
        have hu_lt : u < 11 + j := hrb j hjC u hu
        have hu_ne10 : u ≠ 10 := by
          intro h10; subst h10
          have hmemC : gateAt C j ∈ C.gates := by
            unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjC]
            exact List.getElem_mem hjC
          exact huse10 (gateAt C j) hmemC hu
        dsimp only [shift]
        split_ifs <;> omega
      have hnot' : notCount C' = notCount C := by
        unfold notCount
        simp only [C', List.filter_map]
        rw [List.length_map]
        rfl
      have hout_op' : notCount C' = 1 → (gateAt C' (C'.output - 10)).op ≠ GateOp.not := by
        intro hn1
        have hidx : C'.output - 10 = C.output - 11 := by dsimp only [C']; omega
        have hk : C.output - 11 < C.gates.length := by change C.output < 11 + C.gates.length at houtLt; omega
        have hgat' : (gateAt C' (C'.output - 10)).op = (gateAt C (C.output - 11)).op := by
          rw [hidx]; unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [C'] using hk),
              List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
          simp [C', shiftGate]
        rw [hgat']
        exact houtNot_ok (by omega)
      rcases pure10 C' hfan' hrb' hsz' (by dsimp only [C']; omega)
        (by change C.output - 1 < 10 + (C.gates.map shiftGate).length; rw [List.length_map]; change C.output < 11 + C.gates.length at houtLt; omega)
        (by omega) (by omega) hout_op' with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      -- Show C.eval (List.ofFn x ++ [x 0 || x 2]) = C'.eval (List.ofFn x)
      have hsim : ∀ (gs : List Gate) (w1 w2 : List Bool),
          w1.length = w2.length + 1 → 10 ≤ w2.length →
          (∀ g ∈ gs, 10 ∉ g.inputs) →
          (∀ u, u ≠ 10 → w1.getD u false = w2.getD (shift u) false) →
          ∀ u, u ≠ 10 → (gs.foldl wireStep w1).getD u false =
            ((gs.map shiftGate).foldl wireStep w2).getD (shift u) false := by
        intro gs; induction gs with
        | nil => intro w1 w2 _ _ _ hinv; exact hinv
        | cons g r ih =>
          intro w1 w2 hlen h10 hno10 hinv
          simp only [List.map_cons, List.foldl_cons]
          have hg10 : 10 ∉ g.inputs := hno10 g (by simp)
          have hval : g.op.eval (g.inputs.map (fun i => w1.getD i false)) =
              (shiftGate g).op.eval ((shiftGate g).inputs.map (fun i => w2.getD i false)) := by
            dsimp only [shiftGate]
            rw [List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu
            exact hinv u (fun h => hg10 (h ▸ hu))
          apply ih (wireStep w1 g) (wireStep w2 (shiftGate g))
            (by simp [wireStep, hlen]) (by simp [wireStep]; omega)
            (fun g' hg' => hno10 g' (by simp [hg']))
          intro u hu
          dsimp only [wireStep]
          rw [← hval]
          by_cases hge : 11 ≤ u
          · have hsh : shift u = u - 1 := by simp [shift, hge]
            rw [hsh]
            by_cases hlt1 : u < w1.length
            · have hlt2 : u - 1 < w2.length := by omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
                  List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
              simpa [List.getD_eq_getElem?_getD, hsh] using hinv u hu
            · by_cases heq1 : u = w1.length
              · simp only [List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
                simp [heq1, hlen]
              · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
                    List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
          · have hsh : shift u = u := by simp [shift, hge]
            rw [hsh]
            have hlt1 : u < w1.length := by omega
            have hlt2 : u < w2.length := by omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
                List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
            simpa [List.getD_eq_getElem?_getD, hsh] using hinv u hu
      have hinit_sim : ∀ u, u ≠ 10 →
          (List.ofFn x ++ [x 0 || x 2]).getD u false = (List.ofFn x).getD (shift u) false := by
        intro u hu
        by_cases hlt : u < 10
        · have hsh : shift u = u := by simp [shift]; omega
          rw [hsh, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlt]),
              ← List.getD_eq_getElem?_getD]
        · have hge : 11 ≤ u := by omega
          have hsh : shift u = u - 1 := by simp [shift, hge]
          rw [hsh, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
              List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      have heq_eval : C.eval (List.ofFn x ++ [x 0 || x 2]) = C'.eval (List.ofFn x) := by
        unfold Circuit.eval Circuit.wires
        change (C.gates.foldl wireStep (List.ofFn x ++ [x 0 || x 2])).getD C.output false =
          ((C.gates.map shiftGate).foldl wireStep (List.ofFn x)).getD (C.output - 1) false
        have h := hsim C.gates (List.ofFn x ++ [x 0 || x 2]) (List.ofFn x) (by simp) (by simp)
          huse10 hinit_sim C.output (by omega)
        have hsh : shift C.output = C.output - 1 := by simp [shift, houtGe]
        rwa [hsh] at h
      rwa [heq_eval]
