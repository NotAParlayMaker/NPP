import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3831_47
    (hBase14 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9
      (fun y : Fin 9 → Bool =>
        y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 ||
          y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      14)
    (hAndLow :
      have F : (Fin 9 → Bool) → Bool := fun y : Fin 9 → Bool =>
        y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 ||
          y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
        (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) C.gates).length = 1 →
        2 ≤ x2 → x2 ≤ 4 → 9 ≤ x3 → x3 < 9 + x2 →
        9 + x2 < C.output → C.output < 9 + C.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C x2).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C x2).inputs = [0, x3] →
        (∀ y : Fin 9 → Bool,
          F (Function.update y 0 false) ≠ F (Function.update y 0 true) →
          (C.wires (List.ofFn y)).getD x3 false = true) →
        (∃ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD x3 false = false) →
        ∃ y : Fin 9 → Bool,
          PEqualNP.MetaComplexity.circuitFun 9 C (fun i : Fin 9 => if i = 0 then !y 0 else y i) ≠ F y)
    (hAndHigh :
      have F : (Fin 9 → Bool) → Bool := fun y : Fin 9 → Bool =>
        y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 ||
          y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
        (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) C.gates).length = 1 →
        5 ≤ x2 → x2 ≤ 12 → 9 ≤ x3 → x3 < 9 + x2 →
        9 + x2 < C.output → C.output < 9 + C.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C x2).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C x2).inputs = [0, x3] →
        (∀ y : Fin 9 → Bool,
          F (Function.update y 0 false) ≠ F (Function.update y 0 true) →
          (C.wires (List.ofFn y)).getD x3 false = true) →
        (∃ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD x3 false = false) →
        ∃ y : Fin 9 → Bool,
          PEqualNP.MetaComplexity.circuitFun 9 C (fun i : Fin 9 => if i = 0 then !y 0 else y i) ≠ F y)
    (hOr :
      have F : (Fin 9 → Bool) → Bool := fun y : Fin 9 → Bool =>
        y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 ||
          y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
        (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) C.gates).length = 1 →
        1 ≤ x2 → x2 ≤ 12 → 9 ≤ x3 → x3 < 9 + x2 →
        9 + x2 < C.output → C.output < 9 + C.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C x2).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C x2).inputs = [0, x3] →
        (∀ y : Fin 9 → Bool,
          F (Function.update y 0 false) ≠ F (Function.update y 0 true) →
          (C.wires (List.ofFn y)).getD x3 false = false) →
        (∃ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD x3 false = true) →
        ∃ y : Fin 9 → Bool,
          PEqualNP.MetaComplexity.circuitFun 9 C (fun i : Fin 9 => if i = 0 then !y 0 else y i) ≠ F y)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → x2 < x1.gates.length → (0 : ℕ) < x3 → x3 < (9 : ℕ) + x2 → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs = [(0 : ℕ), x3] → ∃ (x12 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x13 : Fin (9 : ℕ)) => if x13 = (0 : Fin (9 : ℕ)) then !x12 (0 : Fin (9 : ℕ)) else x12 x13) ≠ (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ))) := by
  intro C x2 x3 hfan hsz hflt hx2lt hx3pos hx3lt hop hinp
  have hszC : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = D.gates.length := fun _ => rfl
  have hwiresC : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (w : List Bool), D.wires w =
      D.gates.foldl (fun s g => s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]) w :=
    fun _ _ => rfl
  have hevC : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (w : List Bool),
      D.eval w = (D.wires w).getD D.output false := fun _ _ => rfl
  have hcfunC : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (y : Fin 9 → Bool),
      PEqualNP.MetaComplexity.circuitFun 9 D y = D.eval (List.ofFn y) := fun _ _ => rfl
  have hgateAt : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ),
      PEqualNP.MetaComplexity.NestedCover.gateAt D j =
        D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := fun _ _ => rfl
  have hfanC : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D =
      (∀ g ∈ D.gates,
        g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
        g.inputs.length ≤ 2) := fun _ => rfl
  have hhasSz : ∀ (f : (Fin 9 → Bool) → Bool) (s : ℕ),
      PEqualNP.MetaComplexity.HasCircuitSize 9 f s =
        (∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ s ∧
          ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = f y) := fun _ _ => rfl
  have hevalAnd : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id :=
    fun _ => rfl
  have hevalOr : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id :=
    fun _ => rfl
  have hevalNot : ∀ l : List Bool,
      PEqualNP.CircuitLowerBounds.GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  let F := fun y : Fin 9 → Bool =>
    y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 ||
      y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5
  let flip0 := fun y : Fin 9 → Bool => List.ofFn (fun i : Fin 9 => if i = 0 then !y 0 else y i)
  let step := fun (s : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
    s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]
  let run := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (s : List Bool) => gs.foldl step s
  by_contra hno
  have hC : ∀ y : Fin 9 → Bool, C.eval (flip0 y) = F y := by
    intro y
    by_contra hy
    apply hno
    refine ⟨y, ?_⟩
    rw [hcfunC]
    exact hy
  have step_len : ∀ (s : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate),
      (step s g).length = s.length + 1 := by intro s g; simp [step]
  have run_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (s : List Bool),
      (run gs s).length = s.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro s; simp [run]
    | cons g gs ih =>
      intro s
      change (run gs (step s g)).length = s.length + (g :: gs).length
      rw [ih, step_len]
      simp only [List.length_cons]
      omega
  have run_keep : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (s : List Bool) (i : ℕ),
      i < s.length → (run gs s).getD i false = s.getD i false := by
    intro gs
    induction gs with
    | nil => intro s i _; rfl
    | cons g gs ih =>
      intro s i hi
      change (run gs (step s g)).getD i false = s.getD i false
      rw [ih _ _ (by rw [step_len]; omega), List.getD_append _ _ _ _ hi]
  have run_noZero : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (s1 s2 : List Bool),
      s1.length = s2.length →
      (∀ g ∈ gs, 0 ∉ g.inputs) →
      (∀ i : ℕ, i ≠ 0 → s1.getD i false = s2.getD i false) →
      ∀ i : ℕ, i ≠ 0 → (run gs s1).getD i false = (run gs s2).getD i false := by
    intro gs
    induction gs with
    | nil => intro s1 s2 _ _ hag i hi; exact hag i hi
    | cons g gs ih =>
      intro s1 s2 hsl hno hag
      change ∀ i : ℕ, i ≠ 0 → (run gs (step s1 g)).getD i false = (run gs (step s2 g)).getD i false
      have hg0 : 0 ∉ g.inputs := hno g List.mem_cons_self
      have hmap : g.inputs.map (fun i => s1.getD i false) =
          g.inputs.map (fun i => s2.getD i false) := by
        apply List.map_congr_left
        intro a ha
        exact hag a (fun h0 => hg0 (h0 ▸ ha))
      have hs2 : step s2 g = s2 ++ [g.op.eval (g.inputs.map fun i => s1.getD i false)] := by
        dsimp only [step]; rw [hmap]
      rw [hs2]
      dsimp only [step]
      generalize g.op.eval (g.inputs.map fun i => s1.getD i false) = v
      apply ih (s1 ++ [v]) (s2 ++ [v])
      · simp [hsl]
      · exact fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')
      · intro i hi
        by_cases hlt : i < s1.length
        · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hsl ▸ hlt)]
          exact hag i hi
        · by_cases heq : i = s1.length
          · subst heq
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (le_refl _), hsl,
              List.getElem?_append_right (le_refl _)]
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have split_at : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (j : ℕ)
      (g : PEqualNP.CircuitLowerBounds.Gate),
      gs[j]? = some g → gs = gs.take j ++ g :: gs.drop (j + 1) := by
    intro gs
    induction gs with
    | nil => intro j g h; simp at h
    | cons h gs ih =>
      intro j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rfl
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
        exact congrArg (h :: ·) (ih j g hj)
  let gx2 := PEqualNP.MetaComplexity.NestedCover.gateAt C x2
  have hgx2_some : C.gates[x2]? = some gx2 := by
    dsimp only [gx2]
    rw [hgateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx2lt]
    rfl
  let pre := C.gates.take x2
  let post := C.gates.drop (x2 + 1)
  have hpre_len : pre.length = x2 := by simp [pre]; omega
  have hsplit : C.gates = pre ++ gx2 :: post := split_at C.gates x2 gx2 hgx2_some
  have hgx2_c0 : gx2.inputs.contains 0 = true := by
    dsimp only [gx2]; rw [hinp]; simp
  have hno0_pre_post : (∀ g ∈ pre, 0 ∉ g.inputs) ∧ (∀ g ∈ post, 0 ∉ g.inputs) := by
    have hf_eq := hflt
    rw [hsplit, List.filter_append] at hf_eq
    simp only [List.filter_cons, hgx2_c0, ↓reduceIte, List.length_append, List.length_cons] at hf_eq
    have hp0 : (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) pre).length = 0 := by omega
    have hq0 : (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) post).length = 0 := by omega
    have hp_nil := List.length_eq_zero_iff.mp hp0
    have hq_nil := List.length_eq_zero_iff.mp hq0
    refine ⟨?_, ?_⟩
    · intro g hg h0
      have hm : g ∈ List.filter (fun h : PEqualNP.CircuitLowerBounds.Gate => h.inputs.contains 0) pre :=
        List.mem_filter.mpr ⟨hg, List.contains_iff_mem.mpr h0⟩
      rw [hp_nil] at hm; exact List.not_mem_nil hm
    · intro g hg h0
      have hm : g ∈ List.filter (fun h : PEqualNP.CircuitLowerBounds.Gate => h.inputs.contains 0) post :=
        List.mem_filter.mpr ⟨hg, List.contains_iff_mem.mpr h0⟩
      rw [hq_nil] at hm; exact List.not_mem_nil hm
  have hno0_pre := hno0_pre_post.1
  have hno0_post := hno0_pre_post.2
  have flip0_len : ∀ y : Fin 9 → Bool, (flip0 y).length = 9 := by intro y; simp [flip0]
  have flip0_zero : ∀ y : Fin 9 → Bool, (flip0 y).getD 0 false = !y 0 := by
    intro y; dsimp only [flip0]; simp [List.getD_eq_getElem?_getD]
  have flip0_ne0 : ∀ (y : Fin 9 → Bool) (i : ℕ),
      i ≠ 0 → (flip0 y).getD i false = (List.ofFn y).getD i false := by
    intro y i hi
    by_cases hlt : i < 9
    · interval_cases i <;> first | rfl | exact absurd rfl hi
    · rw [List.getD_eq_default _ _ (by simp [flip0]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  have wpre_flip_eq : ∀ (y : Fin 9 → Bool) (i : ℕ),
      i ≠ 0 → (run pre (flip0 y)).getD i false = (run pre (List.ofFn y)).getD i false := by
    intro y i hi
    exact run_noZero pre (flip0 y) (List.ofFn y) (by simp [flip0]) hno0_pre (flip0_ne0 y) i hi
  have wpre_upd_eq : ∀ (y : Fin 9 → Bool) (b : Bool) (i : ℕ),
      i ≠ 0 →
      (run pre (List.ofFn (Function.update y 0 b))).getD i false =
        (run pre (List.ofFn y)).getD i false := by
    intro y b i hi
    apply run_noZero pre _ _ (by simp) hno0_pre _ i hi
    intro k hk
    by_cases hlt : k < 9
    · interval_cases k <;> first | rfl | exact absurd rfl hk
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have wires_x3 : ∀ y : Fin 9 → Bool,
      (C.wires (List.ofFn y)).getD x3 false = (run pre (List.ofFn y)).getD x3 false := by
    intro y
    rw [hwiresC]
    change (run C.gates (List.ofFn y)).getD x3 false = _
    conv_lhs => rw [hsplit]
    have happ : run (pre ++ gx2 :: post) (List.ofFn y) =
        run (gx2 :: post) (run pre (List.ofFn y)) := by simp only [run, List.foldl_append]
    rw [happ, run_keep (gx2 :: post) (run pre (List.ofFn y)) x3 (by rw [run_len]; simp [hpre_len]; exact hx3lt)]
  have eval_decomp : ∀ y : Fin 9 → Bool,
      C.eval (flip0 y) =
        (run post (run pre (flip0 y) ++
          [gx2.op.eval [!y 0, (run pre (List.ofFn y)).getD x3 false]])).getD C.output false := by
    intro y
    rw [hevC, hwiresC]
    change (run C.gates (flip0 y)).getD C.output false = _
    conv_lhs => rw [hsplit]
    have happ : run (pre ++ gx2 :: post) (flip0 y) =
        run post (step (run pre (flip0 y)) gx2) := by
      simp only [run, List.foldl_append, List.foldl_cons]
    rw [happ]
    have hstep_gx2 : step (run pre (flip0 y)) gx2 =
        run pre (flip0 y) ++ [gx2.op.eval [!y 0, (run pre (List.ofFn y)).getD x3 false]] := by
      dsimp only [step]
      have hinp' : gx2.inputs = [0, x3] := hinp
      rw [hinp']
      simp only [List.map_cons, List.map_nil]
      rw [run_keep pre (flip0 y) 0 (by rw [flip0_len]; omega), flip0_zero,
        wpre_flip_eq y x3 (by omega)]
    rw [hstep_gx2]
  let yMask := fun (m : ℕ) (i : Fin 9) => m.testBit i.val
  have hF_0 : F (yMask 0) = false := by decide
  have hF_2 : F (yMask 2) = false := by decide
  have hF_3 : F (yMask 3) = true := by decide
  have hout_ub : C.output < 9 + C.gates.length := by
    by_contra hge
    have hc := hC (yMask 3)
    rw [hevC, hwiresC] at hc
    change (run C.gates (flip0 (yMask 3))).getD C.output false = F (yMask 3) at hc
    rw [List.getD_eq_default _ _ (by rw [run_len, flip0_len]; omega), hF_3] at hc
    cases hc
  have hout_ne0 : C.output ≠ 0 := by
    intro h0
    have hc := hC (yMask 0)
    rw [hevC, hwiresC, h0] at hc
    change (run C.gates (flip0 (yMask 0))).getD 0 false = F (yMask 0) at hc
    rw [run_keep C.gates (flip0 (yMask 0)) 0 (by rw [flip0_len]; omega), flip0_zero, hF_0] at hc
    have hy0 : (yMask 0) 0 = false := by decide
    rw [hy0] at hc
    cases hc
  have hout_ge : 9 + x2 ≤ C.output := by
    by_contra hlt
    have hlt' : C.output < 9 + x2 := by omega
    have hc2 := hC (yMask 2)
    have hc3 := hC (yMask 3)
    rw [eval_decomp] at hc2 hc3
    have hlen2 : (run pre (flip0 (yMask 2)) ++
        [gx2.op.eval [!(yMask 2) 0, (run pre (List.ofFn (yMask 2))).getD x3 false]]).length =
        10 + x2 := by
      simp only [List.length_append, List.length_singleton, run_len, flip0_len, hpre_len]
      omega
    have hlen3 : (run pre (flip0 (yMask 3)) ++
        [gx2.op.eval [!(yMask 3) 0, (run pre (List.ofFn (yMask 3))).getD x3 false]]).length =
        10 + x2 := by
      simp only [List.length_append, List.length_singleton, run_len, flip0_len, hpre_len]
      omega
    rw [run_keep post _ C.output (by omega),
      List.getD_append _ _ _ _ (by rw [run_len, flip0_len, hpre_len]; exact hlt'),
      wpre_flip_eq (yMask 2) C.output hout_ne0, hF_2] at hc2
    rw [run_keep post _ C.output (by omega),
      List.getD_append _ _ _ _ (by rw [run_len, flip0_len, hpre_len]; exact hlt'),
      wpre_flip_eq (yMask 3) C.output hout_ne0, hF_3] at hc3
    have hupd23 : Function.update (yMask 3) 0 false = yMask 2 :=
      funext (by decide : ∀ i : Fin 9, Function.update (yMask 3) 0 false i = yMask 2 i)
    have hsame : (run pre (List.ofFn (yMask 2))).getD C.output false =
        (run pre (List.ofFn (yMask 3))).getD C.output false := by
      rw [← hupd23]
      exact wpre_upd_eq (yMask 3) false C.output hout_ne0
    rw [hsame, hc3] at hc2
    cases hc2
  have hout_gt : 9 + x2 < C.output := by
    by_contra hle
    have heq : C.output = 9 + x2 := by omega
    have eval_at_gx2 : ∀ y : Fin 9 → Bool,
        gx2.op.eval [!y 0, (run pre (List.ofFn y)).getD x3 false] = F y := by
      intro y
      have hc := hC y
      rw [eval_decomp, heq] at hc
      have hplen : (run pre (flip0 y)).length = 9 + x2 := by rw [run_len, flip0_len, hpre_len]
      rw [run_keep post _ (9 + x2) (by simp [hplen]), ← hplen,
        List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self] at hc
      exact hc
    rcases hop with hand | hor
    · have h3 := eval_at_gx2 (yMask 3)
      have hop' : gx2.op = PEqualNP.CircuitLowerBounds.GateOp.and := hand
      have hy3 : (yMask 3) 0 = true := by decide
      rw [hop', hevalAnd, hy3, hF_3] at h3
      cases h3
    · have h0 := eval_at_gx2 (yMask 0)
      have hop' : gx2.op = PEqualNP.CircuitLowerBounds.GateOp.or := hor
      have hy0 : (yMask 0) 0 = false := by decide
      rw [hop', hevalOr, hy0, hF_0] at h0
      cases h0
  have hx2_le12 : x2 ≤ 12 := by
    have hlen14 : C.gates.length ≤ 14 := by rwa [← hszC]
    omega
  have hsep_same : ∀ (y : Fin 9 → Bool) (b : Bool),
      gx2.op.eval [true, (run pre (List.ofFn y)).getD x3 false] = b →
      gx2.op.eval [false, (run pre (List.ofFn y)).getD x3 false] = b →
      F (Function.update y 0 false) = F (Function.update y 0 true) := by
    intro y b hb0 hb1
    let y0 := Function.update y 0 false
    let y1 := Function.update y 0 true
    have hc0 := hC y0
    have hc1 := hC y1
    rw [eval_decomp] at hc0 hc1
    have hy0_0 : y0 0 = false := rfl
    have hy1_0 : y1 0 = true := rfl
    rw [hy0_0, Bool.not_false, wpre_upd_eq y false x3 (by omega), hb0] at hc0
    rw [hy1_0, Bool.not_true, wpre_upd_eq y true x3 (by omega), hb1] at hc1
    rw [← hc0, ← hc1]
    apply run_noZero post _ _ _ hno0_post _ C.output hout_ne0
    · simp only [List.length_append, List.length_singleton, run_len, flip0_len]
    · intro i hi
      have hlen0 : (run pre (flip0 y0)).length = 9 + x2 := by rw [run_len, flip0_len, hpre_len]
      have hlen1 : (run pre (flip0 y1)).length = 9 + x2 := by rw [run_len, flip0_len, hpre_len]
      by_cases hlt : i < 9 + x2
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
          wpre_flip_eq y0 i hi, wpre_flip_eq y1 i hi,
          wpre_upd_eq y false i hi, wpre_upd_eq y true i hi]
      · by_cases heq : i = 9 + x2
        · subst heq
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
            hlen0, hlen1, Nat.sub_self]
        · rw [List.getD_eq_default _ _ (by simp [hlen0]; omega),
            List.getD_eq_default _ _ (by simp [hlen1]; omega)]
  have hnot_id : ¬ (∀ y : Fin 9 → Bool,
      gx2.op.eval [!y 0, (run pre (List.ofFn y)).getD x3 false] = !y 0) := by
    intro hid
    apply hBase14
    rw [hhasSz]
    let mapPre := fun w : ℕ => if w = 0 then 9 else if w < 9 then w else w + 1
    let mapPost := fun w : ℕ =>
      if w = 0 then 9 else if w < 9 then w else if w < 9 + x2 then w + 1
      else if w = 9 + x2 then 9 else w
    let gNot0 : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩
    let renG := fun (f : ℕ → ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) =>
      PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map f)
    let E : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨gNot0 :: (pre.map (renG mapPre) ++ post.map (renG mapPost)), mapPost C.output⟩
    have hfanE : PEqualNP.MetaComplexity.FanInTwo E := by
      rw [hfanC] at hfan ⊢
      intro g hg
      simp only [E, List.mem_cons, List.mem_append, List.mem_map] at hg
      rcases hg with rfl | ⟨g0, hg0, rfl⟩ | ⟨g0, hg0, rfl⟩
      · exact ⟨Or.inr (Or.inr rfl), by decide⟩
      · have hmem : g0 ∈ C.gates := by rw [hsplit]; exact List.mem_append_left _ hg0
        obtain ⟨ho, hl⟩ := hfan g0 hmem
        exact ⟨ho, by simpa [renG] using hl⟩
      · have hmem : g0 ∈ C.gates := by
          rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0)
        obtain ⟨ho, hl⟩ := hfan g0 hmem
        exact ⟨ho, by simpa [renG] using hl⟩
    have hszE : E.size ≤ 14 := by
      rw [hszC] at hsz ⊢
      have hclen : C.gates.length = pre.length + 1 + post.length := by
        conv_lhs => rw [hsplit]
        simp only [List.length_append, List.length_cons]
        omega
      simp only [E, List.length_cons, List.length_append, List.length_map]
      omega
    refine ⟨E, hfanE, hszE, ?_⟩
    intro y
    rw [hevC, hwiresC]
    dsimp only [E]
    have hstep0 : step (List.ofFn y) gNot0 = List.ofFn y ++ [!y 0] := by
      dsimp only [step, gNot0]
      simp only [List.map_cons, List.map_nil, hevalNot, List.headD_cons]
      have hy0 : (List.ofFn y).getD 0 false = y 0 := by simp [List.getD_eq_getElem?_getD]
      rw [hy0]
    change (run (pre.map (renG mapPre) ++ post.map (renG mapPost))
      (step (List.ofFn y) gNot0)).getD (mapPost C.output) false = F y
    rw [hstep0]
    have happE : run (pre.map (renG mapPre) ++ post.map (renG mapPost)) (List.ofFn y ++ [!y 0]) =
        run (post.map (renG mapPost)) (run (pre.map (renG mapPre)) (List.ofFn y ++ [!y 0])) := by
      simp only [run, List.foldl_append]
    rw [happE]
    have hsim_pre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (sC sE : List Bool),
        9 ≤ sC.length → sE.length = sC.length + 1 →
        (∀ i : ℕ, sE.getD (mapPre i) false = sC.getD i false) →
        ∀ i : ℕ, (run (gs.map (renG mapPre)) sE).getD (mapPre i) false =
          (run gs sC).getD i false := by
      intro gs
      induction gs with
      | nil => intro sC sE _ _ hag i; exact hag i
      | cons g gs ih =>
        intro sC sE h9 hsl hag
        change ∀ i : ℕ,
          (run (gs.map (renG mapPre)) (step sE (renG mapPre g))).getD (mapPre i) false =
          (run gs (step sC g)).getD i false
        have hval : (renG mapPre g).op.eval ((renG mapPre g).inputs.map fun i => sE.getD i false) =
            g.op.eval (g.inputs.map fun i => sC.getD i false) := by
          dsimp only [renG]; rw [List.map_map]; congr 1
          exact List.map_congr_left (fun a _ => hag a)
        have hsE : step sE (renG mapPre g) =
            sE ++ [g.op.eval (g.inputs.map fun i => sC.getD i false)] := by
          dsimp only [step]; rw [hval]
        rw [hsE]
        dsimp only [step]
        generalize g.op.eval (g.inputs.map fun i => sC.getD i false) = v
        apply ih (sC ++ [v]) (sE ++ [v]) (by simp; omega) (by simp [hsl])
        intro i
        by_cases hlt : i < sC.length
        · have hm_lt : mapPre i < sE.length := by dsimp only [mapPre]; split_ifs <;> omega
          rw [List.getD_append _ _ _ _ hm_lt, List.getD_append _ _ _ _ hlt]
          exact hag i
        · by_cases heq : i = sC.length
          · subst heq
            have hm_eq : mapPre sC.length = sE.length := by
              dsimp only [mapPre]; split_ifs <;> omega
            rw [hm_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (le_refl _), List.getElem?_append_right (le_refl _),
              Nat.sub_self, Nat.sub_self]
          · have hm_ge : (sE ++ [v]).length ≤ mapPre i := by
              simp only [List.length_append, List.length_singleton]
              dsimp only [mapPre]; split_ifs <;> omega
            rw [List.getD_eq_default _ _ hm_ge, List.getD_eq_default _ _ (by simp; omega)]
    have hsim_post : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (sC sE : List Bool),
        10 + x2 ≤ sC.length → sE.length = sC.length →
        (∀ i : ℕ, sE.getD (mapPost i) false = sC.getD i false) →
        ∀ i : ℕ, (run (gs.map (renG mapPost)) sE).getD (mapPost i) false =
          (run gs sC).getD i false := by
      intro gs
      induction gs with
      | nil => intro sC sE _ _ hag i; exact hag i
      | cons g gs ih =>
        intro sC sE h10 hsl hag
        change ∀ i : ℕ,
          (run (gs.map (renG mapPost)) (step sE (renG mapPost g))).getD (mapPost i) false =
          (run gs (step sC g)).getD i false
        have hval : (renG mapPost g).op.eval
            ((renG mapPost g).inputs.map fun i => sE.getD i false) =
            g.op.eval (g.inputs.map fun i => sC.getD i false) := by
          dsimp only [renG]; rw [List.map_map]; congr 1
          exact List.map_congr_left (fun a _ => hag a)
        have hsE : step sE (renG mapPost g) =
            sE ++ [g.op.eval (g.inputs.map fun i => sC.getD i false)] := by
          dsimp only [step]; rw [hval]
        rw [hsE]
        dsimp only [step]
        generalize g.op.eval (g.inputs.map fun i => sC.getD i false) = v
        apply ih (sC ++ [v]) (sE ++ [v]) (by simp; omega) (by simp [hsl])
        intro i
        by_cases hlt : i < sC.length
        · have hm_lt : mapPost i < sE.length := by dsimp only [mapPost]; split_ifs <;> omega
          rw [List.getD_append _ _ _ _ hm_lt, List.getD_append _ _ _ _ hlt]
          exact hag i
        · by_cases heq : i = sC.length
          · subst heq
            have hm_eq : mapPost sC.length = sE.length := by
              dsimp only [mapPost]; split_ifs <;> omega
            rw [hm_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (le_refl _), List.getElem?_append_right (le_refl _),
              Nat.sub_self, Nat.sub_self]
          · have hm_ge : (sE ++ [v]).length ≤ mapPost i := by
              simp only [List.length_append, List.length_singleton]
              dsimp only [mapPost]; split_ifs <;> omega
            rw [List.getD_eq_default _ _ hm_ge, List.getD_eq_default _ _ (by simp; omega)]
    have hpre_ag : ∀ i : ℕ,
        (run (pre.map (renG mapPre)) (List.ofFn y ++ [!y 0])).getD (mapPre i) false =
          (run pre (flip0 y)).getD i false := by
      apply hsim_pre pre (flip0 y) (List.ofFn y ++ [!y 0]) (by rw [flip0_len]) (by simp [flip0])
      intro i
      by_cases hi0 : i = 0
      · subst hi0
        dsimp only [mapPre]; simp only [↓reduceIte]
        rw [flip0_zero, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      · by_cases hi9 : i < 9
        · have hm : mapPre i = i := by dsimp only [mapPre]; split_ifs; omega
          rw [hm, flip0_ne0 y i hi0, List.getD_append _ _ _ _ (by simpa using hi9)]
        · have hm : mapPre i = i + 1 := by dsimp only [mapPre]; split_ifs; omega
          rw [hm, List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by rw [flip0_len]; omega)]
    let sC2 := run pre (flip0 y) ++ [gx2.op.eval [!y 0, (run pre (List.ofFn y)).getD x3 false]]
    let sE2 := run (pre.map (renG mapPre)) (List.ofFn y ++ [!y 0])
    have hsC2_len : sC2.length = 10 + x2 := by
      simp only [sC2, List.length_append, List.length_singleton, run_len, flip0_len, hpre_len]
      omega
    have hsE2_len : sE2.length = 10 + x2 := by
      simp only [sE2, run_len, List.length_map, List.length_append, List.length_ofFn,
        List.length_singleton, hpre_len]
    have hpost_ag := hsim_post post sC2 sE2 (by omega) (by omega) (by
      intro i
      have hp_len : (run pre (flip0 y)).length = 9 + x2 := by rw [run_len, flip0_len, hpre_len]
      by_cases hi0 : i = 0
      · subst hi0
        have hm0 : mapPost 0 = mapPre 0 := rfl
        dsimp only [sC2, sE2]
        rw [hm0, hpre_ag 0, List.getD_append _ _ _ _ (by omega)]
      · by_cases hi9x2 : i < 9 + x2
        · have hm : mapPost i = mapPre i := by dsimp only [mapPost, mapPre]; split_ifs <;> rfl
          dsimp only [sC2, sE2]
          rw [hm, hpre_ag i, List.getD_append _ _ _ _ (by omega)]
        · by_cases hieq : i = 9 + x2
          · subst hieq
            have hm : mapPost (9 + x2) = mapPre 0 := by dsimp only [mapPost, mapPre]; split_ifs <;> omega
            dsimp only [sC2, sE2]
            rw [hm, hpre_ag 0, run_keep pre (flip0 y) 0 (by rw [flip0_len]; omega), flip0_zero,
              List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hp_len,
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hid y]
          · have hm : mapPost i = i := by dsimp only [mapPost]; split_ifs <;> omega
            rw [hm, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)])
      C.output
    dsimp only [sE2] at hpost_ag
    rw [hpost_ag]
    have hc := hC y
    rw [eval_decomp] at hc
    exact hc
  have hsep_wit : ∀ m ∈ ([2, 16, 32, 20, 10, 80, 144, 258] : List ℕ),
      F (Function.update (yMask m) 0 false) ≠ F (Function.update (yMask m) 0 true) := by
    intro m hm
    have hcheck : ([2, 16, 32, 20, 10, 80, 144, 258] : List ℕ).all (fun m =>
        F (Function.update (yMask m) 0 false) != F (Function.update (yMask m) 0 true)) = true := by
      decide
    exact bne_iff_ne.mp (List.all_eq_true.mp hcheck m hm)
  have hor_wit8 : ∀ k : Fin 9, k ≠ 0 →
      ∃ m ∈ ([2, 16, 32, 20, 10, 80, 144, 258] : List ℕ),
        (List.ofFn (yMask m)).getD k.val false = true := by
    decide
  rcases hop with hand | hor
  · have hforced : ∀ y : Fin 9 → Bool,
        F (Function.update y 0 false) ≠ F (Function.update y 0 true) →
        (C.wires (List.ofFn y)).getD x3 false = true := by
      intro y hsep
      rw [wires_x3]
      by_contra hfalse
      have hf' : (run pre (List.ofFn y)).getD x3 false = false :=
        Bool.eq_false_iff.mpr hfalse
      apply hsep
      apply hsep_same y false
      · have hop' : gx2.op = PEqualNP.CircuitLowerBounds.GateOp.and := hand
        rw [hop', hf', hevalAnd]; rfl
      · have hop' : gx2.op = PEqualNP.CircuitLowerBounds.GateOp.and := hand
        rw [hop', hf', hevalAnd]; rfl
    have hnonconst : ∃ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD x3 false = false := by
      by_contra hall
      apply hnot_id
      intro y
      have ht : (run pre (List.ofFn y)).getD x3 false = true := by
        rw [← wires_x3]
        cases hb : (C.wires (List.ofFn y)).getD x3 false
        · exact False.elim (hall ⟨y, hb⟩)
        · rfl
      have hop' : gx2.op = PEqualNP.CircuitLowerBounds.GateOp.and := hand
      rw [hop', ht, hevalAnd]
      cases !y 0 <;> rfl
    have hx3_ge9 : 9 ≤ x3 := by
      by_contra hlt9
      have hlt9' : x3 < 9 := by omega
      have hw2 := hforced (yMask 2) (hsep_wit 2 (by decide))
      have hw16 := hforced (yMask 16) (hsep_wit 16 (by decide))
      rw [wires_x3, run_keep pre _ x3 (by simp; exact hlt9')] at hw2 hw16
      have h2_16 : ∀ k : Fin 9,
          ¬ ((List.ofFn (yMask 2)).getD k.val false = true ∧
             (List.ofFn (yMask 16)).getD k.val false = true) := by decide
      exact h2_16 ⟨x3, hlt9'⟩ ⟨hw2, hw16⟩
    have hx2_ge2 : 2 ≤ x2 := by
      by_contra hlt2
      have hx2_eq1 : x2 = 1 := by omega
      have hx3_eq9 : x3 = 9 := by omega
      cases hpre_c : pre with
      | nil => rw [hpre_c, List.length_nil] at hpre_len; omega
      | cons g0 pre_rest =>
        have hrest_nil : pre_rest = [] := by
          rw [hpre_c, List.length_cons] at hpre_len
          exact List.length_eq_zero_iff.mp (by omega)
        subst hrest_nil
        have hg0_mem : g0 ∈ C.gates := by rw [hsplit, hpre_c]; simp
        have hfan' := hfan
        rw [hfanC] at hfan'
        obtain ⟨hg0_op, hg0_len⟩ := hfan' g0 hg0_mem
        have hg0_no0 : 0 ∉ g0.inputs := hno0_pre g0 (by simp [hpre_c])
        have hg0_val : ∀ y : Fin 9 → Bool,
            (C.wires (List.ofFn y)).getD x3 false =
              g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false) := by
          intro y
          rw [wires_x3, hpre_c, hx3_eq9]
          change (step (List.ofFn y) g0).getD 9 false = _
          dsimp only [step]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
          simp
        let clip := fun i : ℕ => (⟨min i 9, by omega⟩ : Fin 10)
        have clip_get : ∀ (y : Fin 9 → Bool) (i : ℕ),
            (List.ofFn y).getD (clip i).val false = (List.ofFn y).getD i false := by
          intro y i
          dsimp only [clip]
          by_cases hi9 : i ≤ 9
          · rw [Nat.min_eq_left hi9]
          · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by simp),
              List.getD_eq_default _ _ (by simp; omega)]
        have clip_ne0 : ∀ i : ℕ, i ≠ 0 → (clip i).val ≠ 0 := by
          intro i hi; dsimp only [clip]; omega
        have hbin_kill : ∀ (op : Bool) (a b : Fin 10), a.val ≠ 0 → b.val ≠ 0 →
            ∃ m ∈ ([2, 16, 32] : List ℕ),
              (if op then ((List.ofFn (yMask m)).getD a.val false ||
                (List.ofFn (yMask m)).getD b.val false)
               else ((List.ofFn (yMask m)).getD a.val false &&
                (List.ofFn (yMask m)).getD b.val false)) = false := by
          decide
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg0_op
        cases hins : g0.inputs with
        | nil =>
          rcases hg0_op with ho | ho | ho
          · obtain ⟨y, hy⟩ := hnonconst
            rw [hg0_val, hins, ho, hevalAnd] at hy; cases hy
          · have ht := hforced (yMask 2) (hsep_wit 2 (by decide))
            rw [hg0_val, hins, ho, hevalOr] at ht; cases ht
          · obtain ⟨y, hy⟩ := hnonconst
            rw [hg0_val, hins, ho, hevalNot] at hy; cases hy
        | cons a rest1 =>
          have ha0 : a ≠ 0 := fun e => hg0_no0 (by simp [hins, e])
          cases rest1 with
          | nil =>
            rcases hg0_op with ho | ho | ho
            · obtain ⟨m, hm, hmf⟩ := hbin_kill false (clip a) (clip a)
                (clip_ne0 a ha0) (clip_ne0 a ha0)
              have ht := hforced (yMask m) (hsep_wit m (by simp at hm; rcases hm with rfl | rfl | rfl <;> decide))
              rw [hg0_val, hins, ho, List.map_cons, List.map_nil, hevalAnd, List.all_cons,
                List.all_nil, Bool.and_true, id_eq, ← clip_get] at ht
              simp only [Bool.and_self] at hmf
              rw [ht] at hmf; cases hmf
            · obtain ⟨m, hm, hmf⟩ := hbin_kill true (clip a) (clip a)
                (clip_ne0 a ha0) (clip_ne0 a ha0)
              have ht := hforced (yMask m) (hsep_wit m (by simp at hm; rcases hm with rfl | rfl | rfl <;> decide))
              rw [hg0_val, hins, ho, List.map_cons, List.map_nil, hevalOr, List.any_cons,
                List.any_nil, Bool.or_false, id_eq, ← clip_get] at ht
              simp only [Bool.or_self] at hmf
              rw [ht] at hmf; cases hmf
            · by_cases ha9 : a < 9
              · obtain ⟨m, hm, hmt⟩ := hor_wit8 ⟨a, ha9⟩ (fun e => ha0 (congrArg Fin.val e))
                have ht := hforced (yMask m) (hsep_wit m hm)
                rw [hg0_val, hins, ho, List.map_cons, List.map_nil, hevalNot, List.headD_cons] at ht
                change !(List.ofFn (yMask m)).getD (⟨a, ha9⟩ : Fin 9).val false = true at ht
                rw [hmt] at ht; cases ht
              · obtain ⟨y, hy⟩ := hnonconst
                rw [hg0_val, hins, ho, List.map_cons, List.map_nil, hevalNot, List.headD_cons,
                  List.getD_eq_default _ _ (by simp; omega)] at hy
                cases hy
          | cons b rest2 =>
            have hb0 : b ≠ 0 := fun e => hg0_no0 (by simp [hins, e])
            cases rest2 with
            | cons c rest3 => rw [hins] at hg0_len; simp at hg0_len
            | nil =>
              rcases hg0_op with ho | ho | ho
              · obtain ⟨m, hm, hmf⟩ := hbin_kill false (clip a) (clip b)
                  (clip_ne0 a ha0) (clip_ne0 b hb0)
                have ht := hforced (yMask m) (hsep_wit m (by simp at hm; rcases hm with rfl | rfl | rfl <;> decide))
                simp only [hg0_val, hins, ho, List.map_cons, List.map_nil, hevalAnd,
                  List.all_cons, List.all_nil, Bool.and_true, id_eq] at ht
                simp only [Bool.false_eq_true, ↓reduceIte] at hmf
                rw [clip_get (yMask m) a, clip_get (yMask m) b, ht] at hmf
                cases hmf
              · obtain ⟨m, hm, hmf⟩ := hbin_kill true (clip a) (clip b)
                  (clip_ne0 a ha0) (clip_ne0 b hb0)
                have ht := hforced (yMask m) (hsep_wit m (by simp at hm; rcases hm with rfl | rfl | rfl <;> decide))
                simp only [hg0_val, hins, ho, List.map_cons, List.map_nil, hevalOr,
                  List.any_cons, List.any_nil, Bool.or_false, id_eq] at ht
                simp only [↓reduceIte] at hmf
                rw [clip_get (yMask m) a, clip_get (yMask m) b, ht] at hmf
                cases hmf
              · by_cases ha9 : a < 9
                · obtain ⟨m, hm, hmt⟩ := hor_wit8 ⟨a, ha9⟩ (fun e => ha0 (congrArg Fin.val e))
                  have ht := hforced (yMask m) (hsep_wit m hm)
                  rw [hg0_val, hins, ho, List.map_cons, List.map_cons, List.map_nil, hevalNot,
                    List.headD_cons] at ht
                  change !(List.ofFn (yMask m)).getD (⟨a, ha9⟩ : Fin 9).val false = true at ht
                  rw [hmt] at ht; cases ht
                · obtain ⟨y, hy⟩ := hnonconst
                  rw [hg0_val, hins, ho, List.map_cons, List.map_cons, List.map_nil, hevalNot,
                    List.headD_cons, List.getD_eq_default _ _ (by simp; omega)] at hy
                  cases hy
    by_cases hx2_4 : x2 ≤ 4
    · obtain ⟨y, hy⟩ := hAndLow C x2 x3 hfan hsz hflt hx2_ge2 hx2_4 hx3_ge9 hx3lt
        hout_gt hout_ub hand hinp hforced hnonconst
      apply hy; rw [hcfunC]; exact hC y
    · obtain ⟨y, hy⟩ := hAndHigh C x2 x3 hfan hsz hflt (by omega) hx2_le12 hx3_ge9 hx3lt
        hout_gt hout_ub hand hinp hforced hnonconst
      apply hy; rw [hcfunC]; exact hC y
  · have hforced : ∀ y : Fin 9 → Bool,
        F (Function.update y 0 false) ≠ F (Function.update y 0 true) →
        (C.wires (List.ofFn y)).getD x3 false = false := by
      intro y hsep
      rw [wires_x3]
      by_contra hne_f
      have ht' : (run pre (List.ofFn y)).getD x3 false = true := by
        cases hb : (run pre (List.ofFn y)).getD x3 false
        · exact False.elim (hne_f hb)
        · rfl
      apply hsep
      apply hsep_same y true
      · have hop' : gx2.op = PEqualNP.CircuitLowerBounds.GateOp.or := hor
        rw [hop', ht', hevalOr]; rfl
      · have hop' : gx2.op = PEqualNP.CircuitLowerBounds.GateOp.or := hor
        rw [hop', ht', hevalOr]; rfl
    have hnonconst : ∃ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD x3 false = true := by
      by_contra hall
      apply hnot_id
      intro y
      have hf' : (run pre (List.ofFn y)).getD x3 false = false := by
        rw [← wires_x3]
        cases hb : (C.wires (List.ofFn y)).getD x3 false
        · rfl
        · exact False.elim (hall ⟨y, hb⟩)
      have hop' : gx2.op = PEqualNP.CircuitLowerBounds.GateOp.or := hor
      rw [hop', hf', hevalOr]
      cases !y 0 <;> rfl
    have hx3_ge9 : 9 ≤ x3 := by
      by_contra hlt9
      have hlt9' : x3 < 9 := by omega
      obtain ⟨m, hm, hmt⟩ := hor_wit8 ⟨x3, hlt9'⟩ (fun e => by
        have hv := congrArg Fin.val e; dsimp only at hv; omega)
      have hf_m := hforced (yMask m) (hsep_wit m hm)
      rw [wires_x3, run_keep pre _ x3 (by simp; exact hlt9')] at hf_m
      change (List.ofFn (yMask m)).getD (⟨x3, hlt9'⟩ : Fin 9).val false = false at hf_m
      rw [hmt] at hf_m; cases hf_m
    obtain ⟨y, hy⟩ := hOr C x2 x3 hfan hsz hflt (by omega) hx2_le12 hx3_ge9 hx3lt
      hout_gt hout_ub hor hinp hforced hnonconst
    apply hy; rw [hcfunC]; exact hC y
