import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2153_2 :
    (¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 14) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 10 false = !(y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size := by
  intro hUnrestricted hNotDeg3 hNotDeg2 hNotOr C hFan hFirst hFun hG1
  classical
  let edgeF : (Fin 9 → Bool) → Bool := (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have step_ext : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ extra, gs.foldl step w = w ++ extra ∧ extra.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨extra, heq, hlen⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: extra, ?_, by simp [hlen]⟩
      rw [List.foldl_cons, heq]
      simp [step, List.append_assoc]
  have foldl_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs w
    obtain ⟨extra, heq, hlen⟩ := step_ext gs w
    simp [heq, hlen]
  have getD_foldl_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
    intro gs w i hi
    obtain ⟨extra, heq, _⟩ := step_ext gs w
    rw [heq, List.getD_append _ _ false i hi]
  have getD_ofFn : ∀ (y : Fin 9 → Bool) (k : ℕ) (hk : k < 9),
      (List.ofFn y).getD k false = y ⟨k, hk⟩ := by
    intro y k hk
    rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
  have hlen2 : 2 ≤ C.gates.length := by
    cases h1 : C.gates[1]? with
    | none => simp [h1] at hG1
    | some g =>
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h1
      omega
  rcases C with ⟨gates, out⟩
  rcases gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · simp at hlen2
  · simp at hlen2
  have hg1op : g1.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    simpa using hG1
  have hg0_val : ∀ y : Fin 9 → Bool,
      g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false) = (y 0 || y 4) := by
    intro y
    have h := hFirst y
    change ((g1 :: rest).foldl step (step (List.ofFn y) g0)).getD 9 false = (y 0 || y 4) at h
    rw [getD_foldl_lt (g1 :: rest) (step (List.ofFn y) g0) 9 (by simp [step])] at h
    simpa [step, List.getD_eq_getElem?_getD] using h
  have hs0_eq : ∀ y : Fin 9 → Bool,
      step (List.ofFn y) g0 = List.ofFn y ++ [y 0 || y 4] := by
    intro y
    dsimp only [step]
    rw [hg0_val y]
  have hg1_val : ∀ y : Fin 9 → Bool,
      g1.op.eval (g1.inputs.map fun i => (List.ofFn y ++ [y 0 || y 4]).getD i false) =
        !((List.ofFn y ++ [y 0 || y 4]).getD (g1.inputs.headD 10) false) := by
    intro y
    rw [hg1op]
    cases hin : g1.inputs with
    | nil =>
      have h10 : (List.ofFn y ++ [y 0 || y 4]).getD 10 false = false := by
        rw [List.getD_eq_default _ false (by simp)]
      change (!false) = !((List.ofFn y ++ [y 0 || y 4]).getD 10 false)
      rw [h10]
    | cons a as => rfl
  have swapPerm : ∀ (p : Fin 9 → Fin 9) (t : Fin 9) (i : ℕ) (hi : i < 9),
      p ⟨i, hi⟩ = t →
      (∀ y : Fin 9 → Bool, edgeF (fun j => y (p j)) = edgeF y) →
      g1.inputs.head? = some i →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
        (∀ y : Fin 9 → Bool, (D.wires (List.ofFn y)).getD 9 false = !(y t)) →
        PEqualNP.MetaComplexity.circuitFun 9 D = edgeF → 16 ≤ D.size) →
      16 ≤ (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: g1 :: rest) out).size := by
    intro p t i hi hpi haut hhead hTarget
    let mw (k : ℕ) : ℕ :=
      if hk : k < 9 then (p ⟨k, hk⟩).val
      else if k = 9 then 10
      else if k = 10 then 9
      else k
    let g1' : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [t.val]⟩
    let g0' : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨g0.op, g0.inputs.map fun k => if hk : k < 9 then (p ⟨k, hk⟩).val else 10 + rest.length + 1⟩
    let rg (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨g.op, g.inputs.map mw⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨g1' :: g0' :: rest.map rg, mw out⟩
    have hDfan : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      simp only [D, List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | rfl | ⟨g', hg', rfl⟩
      · exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp [g1']⟩
      · have h0 := hFan g0 (by simp)
        exact ⟨h0.1, by simpa [g0'] using h0.2⟩
      · have hr := hFan g' (by simp [hg'])
        exact ⟨hr.1, by simpa [rg] using hr.2⟩
    have hD_w1 : ∀ y : Fin 9 → Bool,
        step (List.ofFn y) g1' = List.ofFn y ++ [!(y t)] := by
      intro y
      have ht : (List.ofFn y).getD t.val false = y t := getD_ofFn y t.val t.isLt
      change List.ofFn y ++ [!((List.ofFn y).getD t.val false)] = List.ofFn y ++ [!(y t)]
      rw [ht]
    have hD_w2 : ∀ y : Fin 9 → Bool,
        step (List.ofFn y ++ [!(y t)]) g0' = List.ofFn y ++ [!(y t), y (p 0) || y (p 4)] := by
      intro y
      have hmap : (g0'.inputs.map fun k => (List.ofFn y ++ [!(y t)]).getD k false) =
          (g0.inputs.map fun k => (List.ofFn (fun j => y (p j))).getD k false) := by
        simp only [g0', List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro k _
        by_cases hk : k < 9
        · simp only [hk, dite_true]
          rw [List.getD_append _ _ false _ (by simp)]
          rw [getD_ofFn y (p ⟨k, hk⟩).val (p ⟨k, hk⟩).isLt]
          rw [getD_ofFn (fun j => y (p j)) k hk]
        · simp only [hk, dite_false]
          rw [List.getD_eq_default _ false (by simp; omega)]
          rw [List.getD_eq_default _ false (by simp; omega)]
      dsimp only [step, g0']
      change List.ofFn y ++ [!(y t)] ++ [g0.op.eval (g0'.inputs.map fun k => (List.ofFn y ++ [!(y t)]).getD k false)] = _
      rw [hmap, hg0_val (fun j => y (p j)), List.append_assoc, List.singleton_append]
    have hD_first : ∀ y : Fin 9 → Bool, (D.wires (List.ofFn y)).getD 9 false = !(y t) := by
      intro y
      change ((g0' :: rest.map rg).foldl step (step (List.ofFn y) g1')).getD 9 false = !(y t)
      rw [hD_w1 y, getD_foldl_lt _ _ 9 (by simp)]
      simp [List.getD_eq_getElem?_getD]
    have hD_wires : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool),
        w.length = w'.length → 11 ≤ w.length →
        (∀ k, w'.getD (mw k) false = w.getD k false) →
        ∀ k, ((gs.map rg).foldl step w').getD (mw k) false = (gs.foldl step w).getD k false := by
      intro gs
      induction gs with
      | nil => intro w w' _ _ hrel k; exact hrel k
      | cons g gs ih =>
        intro w w' hlen h11 hrel k
        simp only [List.map_cons, List.foldl_cons]
        have hmap : ((rg g).inputs.map fun j => w'.getD j false) =
            (g.inputs.map fun j => w.getD j false) := by
          simp only [rg, List.map_map, Function.comp_def]
          apply List.map_congr_left
          intro j _
          exact hrel j
        have hv : (rg g).op.eval ((rg g).inputs.map fun j => w'.getD j false) =
            g.op.eval (g.inputs.map fun j => w.getD j false) := by
          simp only [rg, hmap]
        apply ih (step w g) (step w' (rg g)) (by simp [step, hlen]) (by simp [step]; omega)
        intro j
        by_cases hj : j < w.length
        · have hmj : mw j < w'.length := by
            simp only [mw]
            split_ifs with h1 h2 h3
            · exact Nat.lt_of_lt_of_le (p ⟨j, h1⟩).isLt (by omega)
            · omega
            · omega
            · omega
          rw [List.getD_append _ _ false _ hmj, List.getD_append _ _ false _ hj, hrel j]
        · by_cases heq : j = w.length
          · subst heq
            have hmw : mw w.length = w'.length := by
              simp only [mw]
              split_ifs <;> omega
            rw [hmw]
            simp only [step, List.getD_append_right _ _ false _ (le_refl _),
              Nat.sub_self, List.getD_cons_zero, hv]
          · have hgt : w.length < j := by omega
            have hmw : w'.length < mw j := by
              simp only [mw]
              split_ifs <;> omega
            rw [List.getD_eq_default _ false (by simp [step]; omega),
                List.getD_eq_default _ false (by simp [step]; omega)]
    have hD_fun : PEqualNP.MetaComplexity.circuitFun 9 D = edgeF := by
      funext y
      let y' : Fin 9 → Bool := fun j => y (p j)
      have h10 : g1.op.eval (g1.inputs.map fun k => (List.ofFn y' ++ [y' 0 || y' 4]).getD k false) = !(y t) := by
        rw [hg1_val y']
        have hhd : g1.inputs.headD 10 = i := by
          cases hin : g1.inputs with
          | nil => simp [hin] at hhead
          | cons a as => simp [hin] at hhead; subst hhead; rfl
        rw [hhd, List.getD_append _ _ false i (by simp [hi]), getD_ofFn y' i hi]
        simp [y', hpi]
      have hbase : ∀ k, (List.ofFn y ++ [!(y t), y' 0 || y' 4]).getD (mw k) false =
          (List.ofFn y' ++ [y' 0 || y' 4, !(y t)]).getD k false := by
        intro k
        by_cases hk9 : k < 9
        · simp only [mw, hk9, dite_true]
          rw [List.getD_append _ _ false _ (by simp)]
          rw [List.getD_append _ _ false _ (by simp [hk9])]
          rw [getD_ofFn y (p ⟨k, hk9⟩).val (p ⟨k, hk9⟩).isLt]
          rw [getD_ofFn y' k hk9]
        · by_cases hk9e : k = 9
          · subst hk9e
            have : mw 9 = 10 := by simp [mw]
            rw [this]
            simp [List.getD_eq_getElem?_getD]
          · by_cases hk10 : k = 10
            · subst hk10
              have : mw 10 = 9 := by simp [mw]
              rw [this]
              simp [List.getD_eq_getElem?_getD]
            · have hge11 : 11 ≤ k := by omega
              have hmk : mw k = k := by
                simp only [mw, hk9, hk9e, hk10, dite_false, ite_false]
              rw [hmk, List.getD_eq_default _ false (by simp; omega),
                  List.getD_eq_default _ false (by simp; omega)]
      have hev := hD_wires rest (List.ofFn y' ++ [y' 0 || y' 4, !(y t)])
        (List.ofFn y ++ [!(y t), y' 0 || y' 4]) (by simp) (by simp) hbase out
      have hCeval : (rest.foldl step (List.ofFn y' ++ [y' 0 || y' 4, !(y t)])).getD out false = edgeF y' := by
        have hc := congrFun hFun y'
        change (rest.foldl step (step (step (List.ofFn y') g0) g1)).getD out false = edgeF y' at hc
        have hs1 : step (List.ofFn y' ++ [y' 0 || y' 4]) g1 = List.ofFn y' ++ [y' 0 || y' 4, !(y t)] := by
          dsimp only [step]
          rw [h10, List.append_assoc, List.singleton_append]
        rw [hs0_eq y', hs1] at hc
        exact hc
      change D.eval (List.ofFn y) = edgeF y
      have hDeval : D.eval (List.ofFn y) =
          ((rest.map rg).foldl step (List.ofFn y ++ [!(y t), y' 0 || y' 4])).getD (mw out) false := by
        change ((rest.map rg).foldl step (step (step (List.ofFn y) g1') g0')).getD (mw out) false = _
        rw [hD_w1 y, hD_w2 y]
      rw [hDeval, hev, hCeval, haut y]
    have hge := hTarget D hDfan hD_first hD_fun
    have hsz : D.size = (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: g1 :: rest) out).size := by
      change (g1' :: g0' :: rest.map rg).length = (g0 :: g1 :: rest).length
      simp
    omega
  have const10_elim :
      (∀ y : Fin 9 → Bool, step (step (List.ofFn y) g0) g1 = List.ofFn y ++ [y 0 || y 4, true]) →
      16 ≤ (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: g1 :: rest) out).size := by
    intro h10true
    by_contra hlt
    have hsz15 : rest.length ≤ 13 := by
      change ¬ 16 ≤ (g0 :: g1 :: rest).length at hlt
      simp only [List.length_cons] at hlt
      omega
    let normN (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
      if g.op = PEqualNP.CircuitLowerBounds.GateOp.not then ⟨g.op, g.inputs.take 1⟩ else g
    have normN_step : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate),
        step w (normN g) = step w g := by
      intro w g
      rcases g with ⟨op, ins⟩
      cases op with
      | not =>
        simp only [normN, ite_true]
        cases ins with
        | nil => rfl
        | cons a as => rfl
      | and => simp [normN]
      | or => simp [normN]
      | mod m => simp [normN]
      | maj => simp [normN]
    have normN_foldl : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        (gs.map normN).foldl step w = gs.foldl step w := by
      intro gs
      induction gs with
      | nil => intro w; rfl
      | cons g gs ih => intro w; simp only [List.map_cons, List.foldl_cons, normN_step, ih]
    let restN := rest.map normN
    have hrestN_len : restN.length = rest.length := List.length_map ..
    have hrestN_fan : ∀ g ∈ restN,
        g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
        g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have hf := hFan g' (by simp [hg'])
      cases hop : g'.op with
      | not =>
        simp only [normN, hop, ite_true]
        exact ⟨by simp, by simp⟩
      | and => simp [normN, hop, hf]
      | or => simp [normN, hop, hf]
      | mod m => simp [hop] at hf
      | maj => simp [hop] at hf
    have hrestN_eval : ∀ y : Fin 9 → Bool,
        ((g0 :: g1 :: restN).foldl step (List.ofFn y)).getD out false = edgeF y := by
      intro y
      have hc := congrFun hFun y
      change (rest.foldl step (step (step (List.ofFn y) g0) g1)).getD out false = edgeF y at hc
      change (restN.foldl step (step (step (List.ofFn y) g0) g1)).getD out false = edgeF y
      rw [normN_foldl]
      exact hc
    have del_gate : ∀ (pre post : List PEqualNP.CircuitLowerBounds.Gate)
        (h : PEqualNP.CircuitLowerBounds.Gate) (rep : ℕ),
        (rep < 9 + pre.length ∨ 9 + pre.length + post.length ≤ rep) →
        (∀ g ∈ pre ++ post,
          g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
            PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
          g.inputs.length ≤ 2) →
        pre.length + post.length ≤ 14 →
        (∀ y : Fin 9 → Bool,
          let w := pre.foldl step (List.ofFn y)
          h.op.eval (h.inputs.map fun i => w.getD i false) = w.getD rep false) →
        (∀ y : Fin 9 → Bool,
          ((pre ++ h :: post).foldl step (List.ofFn y)).getD out false = edgeF y) →
        False := by
      intro pre post h rep hrep hfp hlen hval hev
      let d := 9 + pre.length
      let rm (k : ℕ) : ℕ := if k < d then k else if k = d then rep else k - 1
      let rg (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
        ⟨g.op, g.inputs.map rm⟩
      let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨pre ++ post.map rg, rm out⟩
      apply hUnrestricted
      refine ⟨D, ?_, ?_, ?_⟩
      · intro g hg
        simp only [D, List.mem_append, List.mem_map] at hg
        rcases hg with hg | ⟨g', hg', rfl⟩
        · exact hfp g (List.mem_append_left _ hg)
        · have hf := hfp g' (List.mem_append_right _ hg')
          exact ⟨hf.1, by simpa [rg] using hf.2⟩
      · change (pre ++ post.map rg).length ≤ 14
        simp only [List.length_append, List.length_map]
        exact hlen
      · intro y
        have hpost : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool),
            w.length = w'.length + 1 → d ≤ w'.length →
            w'.length + gs.length ≤ d + post.length →
            (∀ k, w'.getD (rm k) false = w.getD k false) →
            ∀ k, ((gs.map rg).foldl step w').getD (rm k) false = (gs.foldl step w).getD k false := by
          intro gs
          induction gs with
          | nil => intro w w' _ _ _ hrel k; exact hrel k
          | cons g gs ih =>
            intro w w' hlw hd hbd hrel k
            simp only [List.map_cons, List.foldl_cons]
            have hmap : ((rg g).inputs.map fun j => w'.getD j false) =
                (g.inputs.map fun j => w.getD j false) := by
              simp only [rg, List.map_map, Function.comp_def]
              apply List.map_congr_left
              intro j _
              exact hrel j
            have hv : (rg g).op.eval ((rg g).inputs.map fun j => w'.getD j false) =
                g.op.eval (g.inputs.map fun j => w.getD j false) := by
              simp only [rg, hmap]
            apply ih (step w g) (step w' (rg g)) (by simp [step, hlw]) (by simp [step]; omega)
              (by simp [step]; simp only [List.length_cons] at hbd; omega)
            intro j
            by_cases hj : j < w.length
            · by_cases hjd : j = d
              · subst hjd
                have hrmd : rm d = rep := by simp [rm]
                rw [hrmd]
                rcases hrep with hlt_r | hge_r
                · rw [List.getD_append _ _ false _ (by omega),
                      List.getD_append _ _ false _ hj]
                  simpa [hrmd] using hrel d
                · have hne_r : w'.length < rep := by simp only [List.length_cons] at hbd; omega
                  rw [List.getD_eq_default _ false (by simp [step]; omega)]
                  rw [List.getD_append _ _ false _ hj]
                  have hr0 := hrel d
                  rw [hrmd, List.getD_eq_default _ false (by omega)] at hr0
                  exact hr0
              · have hrm_lt : rm j < w'.length := by
                  simp only [rm]
                  split_ifs <;> omega
                rw [List.getD_append _ _ false _ hrm_lt,
                    List.getD_append _ _ false _ hj, hrel j]
            · by_cases heq : j = w.length
              · subst heq
                have hrmw : rm w.length = w'.length := by
                  simp only [rm]
                  split_ifs <;> omega
                rw [hrmw]
                simp only [step, List.getD_append_right _ _ false _ (le_refl _),
                  Nat.sub_self, List.getD_cons_zero, hv]
              · have hrm_gt : w'.length < rm j := by
                  simp only [rm]
                  split_ifs <;> omega
                rw [List.getD_eq_default _ false (by simp [step]; omega),
                    List.getD_eq_default _ false (by simp [step]; omega)]
        let w' := pre.foldl step (List.ofFn y)
        have hw'len : w'.length = d := by simp [w', d, foldl_len]
        have hbase : ∀ k, w'.getD (rm k) false = (step w' h).getD k false := by
          intro k
          by_cases hk : k < d
          · simp only [rm, hk, ite_true]
            rw [List.getD_append _ _ false k (by omega)]
          · by_cases hke : k = d
            · subst hke
              simp only [rm, lt_irrefl, ite_false, ite_true]
              rw [← hw'len]
              simp only [step, List.getD_append_right _ _ false _ (le_refl _),
                Nat.sub_self, List.getD_cons_zero]
              exact (hval y).symm
            · simp only [rm, hk, hke, ite_false]
              rw [List.getD_eq_default _ false (by omega),
                  List.getD_eq_default _ false (by simp [step, hw'len]; omega)]
        have hmain := hpost post (step w' h) w' (by simp [step]) (by omega) (by omega) hbase out
        have hD_eq : D.eval (List.ofFn y) = ((post.map rg).foldl step w').getD (rm out) false := by
          change ((pre ++ post.map rg).foldl step (List.ofFn y)).getD (rm out) false = _
          rw [List.foldl_append]
        have hC_eq : ((pre ++ h :: post).foldl step (List.ofFn y)).getD out false =
            (post.foldl step (step w' h)).getD out false := by
          rw [List.foldl_append, List.foldl_cons]
        rw [hD_eq, hmain, ← hC_eq, hev y]
    by_cases hout10 : out = 10
    · have h0 := hrestN_eval (fun _ => false)
      rw [List.foldl_cons, List.foldl_cons, h10true, hout10,
          getD_foldl_lt restN _ 10 (by simp)] at h0
      simp [edgeF, List.getD_eq_getElem?_getD] at h0
    · by_cases hhit : ∃ g ∈ restN, 10 ∈ g.inputs
      · have locate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), (∃ g ∈ gs, 10 ∈ g.inputs) →
            ∃ pre h post, gs = pre ++ h :: post ∧ 10 ∈ h.inputs := by
          intro gs
          induction gs with
          | nil => intro hex; simp at hex
          | cons g gs ih =>
            intro hex
            by_cases hg : 10 ∈ g.inputs
            · exact ⟨[], g, gs, rfl, hg⟩
            · obtain ⟨pre1, h1, post1, heq, h10⟩ := ih (by simpa [hg] using hex)
              exact ⟨g :: pre1, h1, post1, by simp [heq], h10⟩
        obtain ⟨pre1, h, post1, hsplit, h10in⟩ := locate restN hhit
        have hh_mem : h ∈ restN := by rw [hsplit]; simp
        have hpre_fan : ∀ g ∈ (g0 :: g1 :: pre1) ++ post1,
            g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
              PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
            g.inputs.length ≤ 2 := by
          intro g hg
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hg
          rcases hg with hge0 | hge1 | hg | hg
          · exact hFan g (by simp [hge0])
          · exact hFan g (by simp [hge1])
          · exact hrestN_fan g (by rw [hsplit]; simp [hg])
          · exact hrestN_fan g (by rw [hsplit]; simp [hg])
        have hpre_len : (g0 :: g1 :: pre1).length + post1.length ≤ 14 := by
          have : restN.length = pre1.length + 1 + post1.length := by
            rw [hsplit]; simp; omega
          simp only [List.length_cons]
          omega
        have hev_split : ∀ y : Fin 9 → Bool,
            (((g0 :: g1 :: pre1) ++ h :: post1).foldl step (List.ofFn y)).getD out false = edgeF y := by
          intro y
          have he := hrestN_eval y
          rw [hsplit] at he
          simpa only [List.cons_append] using he
        have hw10_true : ∀ y : Fin 9 → Bool,
            ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD 10 false = true := by
          intro y
          rw [List.foldl_cons, List.foldl_cons, h10true, getD_foldl_lt pre1 _ 10 (by simp)]
          simp [List.getD_eq_getElem?_getD]
        have hh_fan := hrestN_fan h hh_mem
        have hh_op : h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            h.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh_fan.1
        rcases hh_op with hand | hor | hnot
        · cases hin : h.inputs with
          | nil => simp [hin] at h10in
          | cons a as =>
            cases as with
            | nil =>
              have ha10 : 10 = a := by simpa [hin] using h10in
              subst ha10
              apply del_gate (g0 :: g1 :: pre1) post1 h 10 (Or.inl (by simp; omega)) hpre_fan hpre_len _ hev_split
              intro y
              rw [hand, hin]
              change (((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD 10 false && true) =
                ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD 10 false
              exact Bool.and_true _
            | cons b bs =>
              have hbs : bs = [] := by
                have hl := hh_fan.2
                rw [hin] at hl
                cases bs with
                | nil => rfl
                | cons _ _ => simp at hl
              subst hbs
              have hab : 10 = a ∨ 10 = b := by simpa [hin] using h10in
              rcases hab with h10a | h10b
              · subst h10a
                let d := 9 + (g0 :: g1 :: pre1).length
                let rep := if b < d then b else d + post1.length
                apply del_gate (g0 :: g1 :: pre1) post1 h rep
                  (by
                    dsimp only [rep, d]
                    split_ifs with hb
                    · exact Or.inl hb
                    · exact Or.inr (le_refl _))
                  hpre_fan hpre_len _ hev_split
                intro y
                have hwt := hw10_true y
                have hwlen : ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).length = d := by
                  rw [foldl_len]; simp [d]
                rw [hand, hin]
                change (((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD 10 false &&
                  (((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD b false && true)) =
                  ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD rep false
                rw [hwt, Bool.true_and, Bool.and_true]
                by_cases hb : b < d
                · simp [rep, hb]
                · simp only [rep, hb, ite_false]
                  rw [List.getD_eq_default _ false (by omega),
                      List.getD_eq_default _ false (by omega)]
              · subst h10b
                let d := 9 + (g0 :: g1 :: pre1).length
                let rep := if a < d then a else d + post1.length
                apply del_gate (g0 :: g1 :: pre1) post1 h rep
                  (by
                    dsimp only [rep, d]
                    split_ifs with ha
                    · exact Or.inl ha
                    · exact Or.inr (le_refl _))
                  hpre_fan hpre_len _ hev_split
                intro y
                have hwt := hw10_true y
                have hwlen : ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).length = d := by
                  rw [foldl_len]; simp [d]
                rw [hand, hin]
                change (((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD a false &&
                  (((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD 10 false && true)) =
                  ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD rep false
                rw [hwt, Bool.and_true, Bool.and_true]
                by_cases ha : a < d
                · simp [rep, ha]
                · simp only [rep, ha, ite_false]
                  rw [List.getD_eq_default _ false (by omega),
                      List.getD_eq_default _ false (by omega)]
        · apply del_gate (g0 :: g1 :: pre1) post1 h 10 (Or.inl (by simp; omega)) hpre_fan hpre_len _ hev_split
          intro y
          have hwt := hw10_true y
          change h.op.eval (h.inputs.map fun i => ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD i false) =
            ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD 10 false
          rw [hor, hwt]
          change (h.inputs.map fun i => ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD i false).any id = true
          simp only [List.any_eq_true, List.mem_map, id_eq]
          exact ⟨true, ⟨10, h10in, hwt⟩, rfl⟩
        · have hh_norm : h.inputs.length ≤ 1 := by
            obtain ⟨g', _, hge⟩ := List.mem_map.mp hh_mem
            cases hop' : g'.op with
            | not =>
              simp only [normN, hop', ite_true] at hge
              rw [← hge]
              simp
            | and => simp [normN, hop'] at hge; rw [← hge] at hnot; rw [hop'] at hnot; cases hnot
            | or => simp [normN, hop'] at hge; rw [← hge] at hnot; rw [hop'] at hnot; cases hnot
            | mod m => simp [normN, hop'] at hge; rw [← hge] at hnot; rw [hop'] at hnot; cases hnot
            | maj => simp [normN, hop'] at hge; rw [← hge] at hnot; rw [hop'] at hnot; cases hnot
          have hh_in : h.inputs = [10] := by
            cases hin : h.inputs with
            | nil => simp [hin] at h10in
            | cons a as =>
              cases as with
              | nil =>
                have ha : 10 = a := by simpa [hin] using h10in
                subst ha; rfl
              | cons _ _ => rw [hin] at hh_norm; simp at hh_norm
          let rep := 9 + (g0 :: g1 :: pre1).length + post1.length
          apply del_gate (g0 :: g1 :: pre1) post1 h rep (Or.inr (le_refl _)) hpre_fan hpre_len _ hev_split
          intro y
          have hwt := hw10_true y
          have hwlen : ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).length = 9 + (g0 :: g1 :: pre1).length := by
            rw [foldl_len]; simp
          change h.op.eval (h.inputs.map fun i => ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD i false) =
            ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD rep false
          rw [hnot, hh_in]
          change (!(((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD 10 false)) =
            ((g0 :: g1 :: pre1).foldl step (List.ofFn y)).getD rep false
          rw [hwt, Bool.not_true, List.getD_eq_default _ false (by omega)]
      · let rm (k : ℕ) : ℕ := if k < 10 then k else k - 1
        let rg (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
          ⟨g.op, g.inputs.map rm⟩
        let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0 :: restN.map rg, rm out⟩
        apply hUnrestricted
        refine ⟨D, ?_, ?_, ?_⟩
        · intro g hg
          simp only [D, List.mem_cons, List.mem_map] at hg
          rcases hg with hge0 | ⟨g', hg', rfl⟩
          · exact hFan g (by simp [hge0])
          · have hf := hrestN_fan g' hg'
            exact ⟨hf.1, by simpa [rg] using hf.2⟩
        · change (g0 :: restN.map rg).length ≤ 14
          simp only [List.length_cons, List.length_map, hrestN_len]
          omega
        · intro y
          have hunused : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool),
              (∀ g ∈ gs, 10 ∉ g.inputs) →
              w.length = w'.length + 1 → 10 ≤ w'.length →
              (∀ k, k ≠ 10 → w'.getD (rm k) false = w.getD k false) →
              ∀ k, k ≠ 10 → ((gs.map rg).foldl step w').getD (rm k) false = (gs.foldl step w).getD k false := by
            intro gs
            induction gs with
            | nil => intro w w' _ _ _ hrel k hk; exact hrel k hk
            | cons g gs ih =>
              intro w w' hno hlw h10 hrel k hk
              simp only [List.map_cons, List.foldl_cons]
              have hmap : ((rg g).inputs.map fun j => w'.getD j false) =
                  (g.inputs.map fun j => w.getD j false) := by
                simp only [rg, List.map_map, Function.comp_def]
                apply List.map_congr_left
                intro j hj
                have hj10 : j ≠ 10 := fun e => hno g (List.mem_cons_self ..) (e ▸ hj)
                exact hrel j hj10
              have hv : (rg g).op.eval ((rg g).inputs.map fun j => w'.getD j false) =
                  g.op.eval (g.inputs.map fun j => w.getD j false) := by
                simp only [rg, hmap]
              refine ih (step w g) (step w' (rg g))
                (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
                (by simp [step, hlw]) (by simp [step]; omega) ?_ k hk
              intro j hj10
              by_cases hj : j < w.length
              · have hrm_lt : rm j < w'.length := by simp only [rm]; split_ifs <;> omega
                rw [List.getD_append _ _ false _ hrm_lt,
                    List.getD_append _ _ false _ hj, hrel j hj10]
              · by_cases heq : j = w.length
                · subst heq
                  have hrmw : rm w.length = w'.length := by simp only [rm]; split_ifs <;> omega
                  rw [hrmw]
                  simp only [step, List.getD_append_right _ _ false _ (le_refl _),
                    Nat.sub_self, List.getD_cons_zero, hv]
                · have hrm_gt : w'.length < rm j := by simp only [rm]; split_ifs <;> omega
                  rw [List.getD_eq_default _ false (by simp [step]; omega),
                      List.getD_eq_default _ false (by simp [step]; omega)]
          have hno10 : ∀ g ∈ restN, 10 ∉ g.inputs := fun g hg h10 => hhit ⟨g, hg, h10⟩
          have hbase : ∀ k, k ≠ 10 →
              (step (List.ofFn y) g0).getD (rm k) false =
              (step (step (List.ofFn y) g0) g1).getD k false := by
            intro k hk10
            rw [h10true y, hs0_eq y]
            by_cases hk : k < 10
            · simp only [rm, hk, ite_true]
              have hcat : List.ofFn y ++ [y 0 || y 4, true] = (List.ofFn y ++ [y 0 || y 4]) ++ [true] := by simp
              rw [hcat, List.getD_append (List.ofFn y ++ [y 0 || y 4]) [true] false k (by simp; omega)]
            · simp only [rm, hk, ite_false]
              rw [List.getD_eq_default _ false (by simp; omega),
                  List.getD_eq_default _ false (by simp; omega)]
          have hres := hunused restN (step (step (List.ofFn y) g0) g1) (step (List.ofFn y) g0)
            hno10 (by simp [step]) (by simp [step]) hbase out hout10
          change ((restN.map rg).foldl step (step (List.ofFn y) g0)).getD (rm out) false = edgeF y
          rw [hres]
          exact hrestN_eval y
  cases hhd : g1.inputs.head? with
  | none =>
    apply const10_elim
    intro y
    rw [hs0_eq y]
    have h10 := hg1_val y
    have hhd10 : g1.inputs.headD 10 = 10 := by
      cases hin : g1.inputs with
      | nil => rfl
      | cons a as => simp [hin] at hhd
    rw [hhd10, List.getD_eq_default _ false (by simp)] at h10
    dsimp only [step]
    rw [h10, List.append_assoc, List.singleton_append]
    rfl
  | some i =>
    by_cases hi9 : i < 9
    · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i'
      · exact swapPerm (fun j : Fin 9 => ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List (Fin 9)).getD j.val 0) 0 0 (by omega) rfl (by intro y; revert y; decide +kernel) hhd hNotDeg3
      · exact swapPerm (fun j : Fin 9 => ([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD j.val 0) 0 1 (by omega) rfl (by intro y; revert y; decide +kernel) hhd hNotDeg3
      · exact swapPerm (fun j : Fin 9 => ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List (Fin 9)).getD j.val 0) 0 2 (by omega) rfl (by intro y; revert y; decide +kernel) hhd hNotDeg3
      · exact swapPerm (fun j : Fin 9 => ([3, 2, 1, 0, 4, 8, 7, 6, 5] : List (Fin 9)).getD j.val 0) 0 3 (by omega) rfl (by intro y; revert y; decide +kernel) hhd hNotDeg3
      · exact swapPerm (fun j : Fin 9 => ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List (Fin 9)).getD j.val 0) 4 4 (by omega) rfl (by intro y; revert y; decide +kernel) hhd hNotDeg2
      · exact swapPerm (fun j : Fin 9 => ([1, 2, 3, 8, 6, 0, 7, 4, 5] : List (Fin 9)).getD j.val 0) 0 5 (by omega) rfl (by intro y; revert y; decide +kernel) hhd hNotDeg3
      · exact swapPerm (fun j : Fin 9 => ([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD j.val 0) 4 6 (by omega) rfl (by intro y; revert y; decide +kernel) hhd hNotDeg2
      · exact swapPerm (fun j : Fin 9 => ([1, 2, 3, 8, 6, 0, 7, 4, 5] : List (Fin 9)).getD j.val 0) 4 7 (by omega) rfl (by intro y; revert y; decide +kernel) hhd hNotDeg2
      · exact swapPerm (fun j : Fin 9 => ([2, 3, 8, 5, 7, 1, 4, 6, 0] : List (Fin 9)).getD j.val 0) 0 8 (by omega) rfl (by intro y; revert y; decide +kernel) hhd hNotDeg3
      · omega
    · by_cases hi9e : i = 9
      · subst hi9e
        apply hNotOr ⟨g0 :: g1 :: rest, out⟩ hFan hFirst _ hFun
        intro y
        change (rest.foldl step (step (step (List.ofFn y) g0) g1)).getD 10 false = !(y 0 || y 4)
        rw [hs0_eq y, getD_foldl_lt rest _ 10 (by simp [step])]
        have h10 := hg1_val y
        have hhd9 : g1.inputs.headD 10 = 9 := by
          cases hin : g1.inputs with
          | nil => simp [hin] at hhd
          | cons a as => simp [hin] at hhd; subst hhd; rfl
        rw [hhd9] at h10
        dsimp only [step]
        rw [h10]
        simp [List.getD_eq_getElem?_getD]
      · apply const10_elim
        intro y
        rw [hs0_eq y]
        have h10 := hg1_val y
        have hhdi : g1.inputs.headD 10 = i := by
          cases hin : g1.inputs with
          | nil => simp [hin] at hhd
          | cons a as => simp [hin] at hhd; subst hhd; rfl
        rw [hhdi, List.getD_eq_default _ false (by simp; omega)] at h10
        dsimp only [step]
        rw [h10, List.append_assoc, List.singleton_append]
        rfl
