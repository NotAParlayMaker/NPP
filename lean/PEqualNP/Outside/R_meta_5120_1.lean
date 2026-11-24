import PEqualNP.Defs

-- Eliminate readCount 4 = 0 directly, lift to a 15-gate Petersen-v circuit to
-- strip notCount >= 3 via the L-meta-3400 lower bound, and split the remaining
-- notCount in {0, 1, 2} cases with 1 <= readCount 4 <= 2.
theorem PEqualNP.Outside.R_meta_5120_1
    (many_nots :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C →
        PEqualNP.MetaComplexity.circuitFun 9 C =
          (fun x : Fin 9 → Bool =>
            x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
            x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
        13 ≤ C.size - PEqualNP.NotBracket.notCount C)
    (not0 :
      let f8 : (Fin 8 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
      let inp : (Fin 8 → Bool) → Bool → List Bool := fun x b =>
        List.ofFn (Fin.insertNth (4 : Fin 9) b x) ++ [x 0 || x 3]
      let rcnt (v : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) : ℕ :=
        List.countP (fun g => g.inputs.head? == some v || !g.op.eval [false] && g.inputs.contains v) C.gates
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size ≤ 14 →
        PEqualNP.NotBracket.notCount C = 0 →
        1 ≤ rcnt 4 C →
        (∀ v ∈ ([4, 6, 7] : List ℕ), rcnt v C ≤ 2) →
        (∀ y : Fin 8 → Bool, C.eval (inp y false) = f8 y) →
        ∃ y : Fin 8 → Bool, C.eval (inp y true) ≠ (f8 y || y 0 || y 3))
    (not1 :
      let f8 : (Fin 8 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
      let inp : (Fin 8 → Bool) → Bool → List Bool := fun x b =>
        List.ofFn (Fin.insertNth (4 : Fin 9) b x) ++ [x 0 || x 3]
      let rcnt (v : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) : ℕ :=
        List.countP (fun g => g.inputs.head? == some v || !g.op.eval [false] && g.inputs.contains v) C.gates
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size ≤ 14 →
        PEqualNP.NotBracket.notCount C = 1 →
        1 ≤ rcnt 4 C →
        (∀ v ∈ ([4, 6, 7] : List ℕ), rcnt v C ≤ 2) →
        (∀ y : Fin 8 → Bool, C.eval (inp y false) = f8 y) →
        ∃ y : Fin 8 → Bool, C.eval (inp y true) ≠ (f8 y || y 0 || y 3))
    (not2 :
      let f8 : (Fin 8 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
      let inp : (Fin 8 → Bool) → Bool → List Bool := fun x b =>
        List.ofFn (Fin.insertNth (4 : Fin 9) b x) ++ [x 0 || x 3]
      let rcnt (v : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) : ℕ :=
        List.countP (fun g => g.inputs.head? == some v || !g.op.eval [false] && g.inputs.contains v) C.gates
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size ≤ 14 →
        PEqualNP.NotBracket.notCount C = 2 →
        1 ≤ rcnt 4 C →
        (∀ v ∈ ([4, 6, 7] : List ℕ), rcnt v C ≤ 2) →
        (∀ y : Fin 8 → Bool, C.eval (inp y false) = f8 y) →
        ∃ y : Fin 8 → Bool, C.eval (inp y true) ≠ (f8 y || y 0 || y 3)) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); have x2 : (Fin (8 : ℕ) → Bool) → Bool → List Bool := fun (x2 : Fin (8 : ℕ) → Bool) (x3 : Bool) => List.ofFn (Fin.insertNth (4 : Fin (9 : ℕ)) x3 x2) ++ [x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → (∀ x6 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)], List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.head? == Option.some x6 || !x8.op.eval [Bool.false] && x8.inputs.contains x6) x3.gates ≤ (2 : ℕ)) → (∀ (x7 : Fin (8 : ℕ) → Bool), x3.eval (x2 x7 Bool.false) = x1 x7) → ∃ (x8 : Fin (8 : ℕ) → Bool), x3.eval (x2 x8 Bool.true) ≠ (x1 x8 || x8 (0 : Fin (8 : ℕ)) || x8 (3 : Fin (8 : ℕ))) := by
  intro f8 inp C hfan hsz hrc hfalse
  let rpred (v : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) : Bool :=
    g.inputs.head? == some v || !g.op.eval [false] && g.inputs.contains v
  by_cases hr4 : List.countP (rpred 4) C.gates = 0
  · have hall0 : ∀ g ∈ C.gates, rpred 4 g = false := by
      intro g hg
      by_contra hne
      have ht : rpred 4 g = true := by
        cases h : rpred 4 g
        · exact False.elim (hne h)
        · rfl
      have hpos : 0 < List.countP (rpred 4) C.gates := List.countP_pos_iff.mpr ⟨g, hg, ht⟩
      omega
    let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have hgate_eq : ∀ g ∈ C.gates, ∀ w1 w2 : List Bool,
        (∀ i, i ≠ 4 → w1.getD i false = w2.getD i false) →
        g.op.eval (g.inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w2.getD i false) := by
      intro g hg w1 w2 hag
      have hfg := hfan g hg
      have hp0 := hall0 g hg
      have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hfg.1
      rcases hop with h | h | h
      · rw [h]
        apply congrArg PEqualNP.CircuitLowerBounds.GateOp.and.eval
        apply List.map_congr_left
        intro i hi
        apply hag i
        rintro rfl
        have hev : g.op.eval [false] = false := by rw [h]; rfl
        simp [rpred, hev] at hp0
        exact hp0.2 hi
      · rw [h]
        apply congrArg PEqualNP.CircuitLowerBounds.GateOp.or.eval
        apply List.map_congr_left
        intro i hi
        apply hag i
        rintro rfl
        have hev : g.op.eval [false] = false := by rw [h]; rfl
        simp [rpred, hev] at hp0
        exact hp0.2 hi
      · rw [h]
        cases hins : g.inputs with
        | nil => rfl
        | cons a rest =>
          have hne4 : a ≠ 4 := by
            rintro rfl
            simp [rpred, hins] at hp0
          change (!(w1.getD a false)) = (!(w2.getD a false))
          exact congrArg Bool.not (hag a hne4)
    have hfold_eq : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
        (∀ g ∈ gs, g ∈ C.gates) →
        ∀ w1 w2 : List Bool, w1.length = w2.length →
        (∀ i, i ≠ 4 → w1.getD i false = w2.getD i false) →
        ∀ i, i ≠ 4 → (gs.foldl step w1).getD i false = (gs.foldl step w2).getD i false := by
      intro gs
      induction gs with
      | nil =>
        intro _ w1 w2 _ hag i hi
        exact hag i hi
      | cons g gs ih =>
        intro hsub w1 w2 hlen hag i hi
        rw [List.foldl_cons, List.foldl_cons]
        apply ih (fun g' hg' => hsub g' (List.mem_cons_of_mem g hg'))
          (step w1 g) (step w2 g) (by simp [step, hlen])
        · intro j hj
          have hv := hgate_eq g (hsub g List.mem_cons_self) w1 w2 hag
          by_cases hlt : j < w1.length
          · have hlt2 : j < w2.length := hlen ▸ hlt
            simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
              List.getElem?_append_left hlt2]
            simpa only [List.getD_eq_getElem?_getD] using hag j hj
          · by_cases heq : j = w1.length
            · have heq2 : j = w2.length := heq.trans hlen
              simp only [step, List.getD_eq_getElem?_getD]
              rw [heq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
              rw [← heq, heq2, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
              simp only [List.getElem?_cons_zero, Option.getD_some]
              exact hv
            · rw [List.getD_eq_default _ _ (by simp [step]; omega),
                  List.getD_eq_default _ _ (by simp [step]; omega)]
        · exact hi
    have hout_ne4 : C.output ≠ 4 := by
      intro ho4
      let y1 : Fin 8 → Bool := fun i => decide (i = 0 ∨ i = 1)
      have h1 := hfalse y1
      have hf1 : f8 y1 = true := by decide
      have he1 : C.eval (inp y1 false) = false := by
        change (C.gates.foldl step (inp y1 false)).getD C.output false = false
        rw [ho4]
        have hkeep : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, ∀ w : List Bool,
            4 < w.length → (gs.foldl step w).getD 4 false = w.getD 4 false := by
          intro gs
          induction gs with
          | nil => intro w _; rfl
          | cons g gs ih =>
            intro w hw
            rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
            simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
        rw [hkeep C.gates (inp y1 false) (by simp [inp])]
        decide
      rw [he1, hf1] at h1
      exact Bool.false_ne_true h1
    let y0 : Fin 8 → Bool := fun i => decide (i = 0)
    refine ⟨y0, ?_⟩
    have h0_eq : C.eval (inp y0 true) = C.eval (inp y0 false) := by
      change (C.gates.foldl step (inp y0 true)).getD C.output false =
        (C.gates.foldl step (inp y0 false)).getD C.output false
      apply hfold_eq C.gates (fun _ h => h) (inp y0 true) (inp y0 false) (by simp [inp])
      · intro i hi
        by_cases hlt : i < 10
        · interval_cases i <;> first | exact False.elim (hi rfl) | decide
        · rw [List.getD_eq_default _ _ (by simp [inp]; omega),
              List.getD_eq_default _ _ (by simp [inp]; omega)]
      · exact hout_ne4
    rw [h0_eq, hfalse y0]
    decide
  · have hr4_pos : 1 ≤ List.countP (rpred 4) C.gates := by omega
    by_cases hn0 : PEqualNP.NotBracket.notCount C = 0
    · exact not0 C hfan hsz hn0 hr4_pos hrc hfalse
    · by_cases hn1 : PEqualNP.NotBracket.notCount C = 1
      · exact not1 C hfan hsz hn1 hr4_pos hrc hfalse
      · by_cases hn2 : PEqualNP.NotBracket.notCount C = 2
        · exact not2 C hfan hsz hn2 hr4_pos hrc hfalse
        · by_contra hcontra
          have htrue : ∀ y : Fin 8 → Bool, C.eval (inp y true) = (f8 y || y 0 || y 3) := by
            intro y
            by_contra hne
            exact hcontra ⟨y, hne⟩
          let g0 : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, [0, 3]⟩
          let full : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0 :: C.gates, C.output⟩
          have hfull_fan : PEqualNP.MetaComplexity.FanInTwo full := by
            intro g hg
            rcases List.mem_cons.mp hg with rfl | hg'
            · refine ⟨?_, by decide⟩
              simp [g0, Set.mem_insert_iff, Set.mem_singleton_iff]
            · exact hfan g hg'
          have hbool_f : ∀ a0 a1 a2 a3 a5 a6 a7 a8 : Bool,
              (a0 && a1 || a1 && a2 || a2 && a3 || a0 && a5 || a1 && a6 ||
               a2 && a7 || a3 && a8 || a5 && a7 || a6 && a8 || a8 && a5) =
              (a0 && a1 || a1 && a2 || a2 && a3 || a3 && false || false && a0 ||
               a0 && a5 || a1 && a6 || a2 && a7 || a3 && a8 ||
               a5 && a7 || a6 && a8 || a8 && a5) := by decide
          have hbool_t : ∀ a0 a1 a2 a3 a5 a6 a7 a8 : Bool,
              ((a0 && a1 || a1 && a2 || a2 && a3 || a0 && a5 || a1 && a6 ||
                a2 && a7 || a3 && a8 || a5 && a7 || a6 && a8 || a8 && a5) || a0 || a3) =
              (a0 && a1 || a1 && a2 || a2 && a3 || a3 && true || true && a0 ||
               a0 && a5 || a1 && a6 || a2 && a7 || a3 && a8 ||
               a5 && a7 || a6 && a8 || a8 && a5) := by decide
          have hfull_fun : PEqualNP.MetaComplexity.circuitFun 9 full =
              (fun x : Fin 9 → Bool =>
                x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
                x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
                x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
            funext x
            let y : Fin 8 → Bool := fun i =>
              if h : i.val < 4 then x ⟨i.val, by omega⟩ else x ⟨i.val + 1, by omega⟩
            have hins : Fin.insertNth (4 : Fin 9) (x 4) y = x := by
              funext i
              fin_cases i <;> rfl
            have hstep0 : full.eval (List.ofFn x) = C.eval (inp y (x 4)) := by
              change C.eval (List.ofFn x ++
                [PEqualNP.CircuitLowerBounds.GateOp.or.eval
                  [(List.ofFn x).getD 0 false, (List.ofFn x).getD 3 false]]) = C.eval (inp y (x 4))
              have h0 : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD_eq_getElem?_getD]
              have h3 : (List.ofFn x).getD 3 false = x 3 := by simp [List.getD_eq_getElem?_getD]
              have hor : PEqualNP.CircuitLowerBounds.GateOp.or.eval [x 0, x 3] = (x 0 || x 3) := by
                cases x 0 <;> cases x 3 <;> rfl
              rw [h0, h3, hor]
              dsimp only [inp]
              rw [hins]
              rfl
            change full.eval (List.ofFn x) = _
            rw [hstep0]
            cases hx4 : x 4
            · rw [hfalse y]
              exact hbool_f (x 0) (x 1) (x 2) (x 3) (x 5) (x 6) (x 7) (x 8)
            · rw [htrue y]
              exact hbool_t (x 0) (x 1) (x 2) (x 3) (x 5) (x 6) (x 7) (x 8)
          have hlb := many_nots full hfull_fan hfull_fun
          have hfull_sz : full.size = C.size + 1 := by
            change (g0 :: C.gates).length = C.gates.length + 1
            exact List.length_cons
          have hfull_nc : PEqualNP.NotBracket.notCount full = PEqualNP.NotBracket.notCount C := by
            unfold PEqualNP.NotBracket.notCount
            dsimp only [full, g0]
            rw [List.filter_cons_of_neg (by decide)]
          omega
