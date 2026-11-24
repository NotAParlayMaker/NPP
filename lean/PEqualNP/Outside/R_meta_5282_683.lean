import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The graph-independent normalization proof is carried inside this theorem.
theorem PEqualNP.Outside.R_meta_5282_683
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
        circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.and →
          ∀ v : Fin n, v.val ∈ (C.gates.get j).inputs → ∀ u : Fin n,
          (C.wires (List.ofFn (fun k : Fin n => decide (k=u)))).getD (n+j.val) false = false)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) →
      ∀ C : Circuit, IsMinimalMonoCircuit n C →
        circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        (∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.and →
          ∀ v : Fin n, v.val ∈ (C.gates.get j).inputs → ∀ u : Fin n,
          (C.wires (List.ofFn (fun k : Fin n => decide (k=u)))).getD (n+j.val) false = false) →
        ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ circuitFun n D = circuitFun n C ∧
          ∀ j g, D.gates[j]? = some g → g.op = GateOp.and →
          ∀ S : Finset (Fin n), S.card ≤ 1 →
          (D.wires (List.ofFn (fun k : Fin n => decide (k∈S)))).getD (n+j) false = false) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ (∀ (x10 : Fin x1 → Bool), x9.eval (List.ofFn x10) = x4 x10) ∧ (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → (∀ (x12 : Fin x1 → Bool), x10.eval (List.ofFn x12) = x4 x12) → x9.size ≤ x10.size) ∧ x6 x9 := by
  classical
  have eval_and (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
  have eval_or (bs : List Bool) : GateOp.or.eval bs = bs.any id := rfl
  let gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨GateOp.or, []⟩
  have graphFun_eq (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x =
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = _
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]

  have fold_mono (gs : List Gate)
      (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (a b : List Bool) (hab : ∀ i, a.getD i false = true → b.getD i false = true)
      (hlen : a.length = b.length) :
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) a).getD i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) b).getD i false = true := by
    induction gs generalizing a b with
    | nil => exact hab
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hg : g.op.eval (g.inputs.map fun j => a.getD j false) = true →
          g.op.eval (g.inputs.map fun j => b.getD j false) = true := by
        rcases hm g (by simp) with h | h
        · simp only [h, eval_and, eval_or, List.all_map]
          rw [List.all_eq_true, List.all_eq_true]
          exact fun he j hj => hab j (he j hj)
        · simp only [h, eval_and, eval_or, List.any_map]
          rw [List.any_eq_true, List.any_eq_true]
          rintro ⟨j, hj, he⟩
          exact ⟨j, hj, hab j he⟩
      apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg')) _ _ _ (by simp [hlen])
      intro i hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append, ← hlen] at hi ⊢
      split at hi <;> rename_i hlt
      · simp only [ite_eq_left hlt]
        exact hab _ hi
      · simp only [ite_eq_right hlt]
        by_cases he : i = a.length
        · subst i
          simpa using hg (by simpa using hi)
        · cases hs : i - a.length with
          | zero =>
            exact (he (Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hs) (Nat.le_of_not_gt hlt))).elim
          | succ k => simp [hs] at hi

  have wires_mono (C : Circuit) (hm : Monotone2 C) {n : ℕ} {x y : Fin n → Bool}
      (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
      (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
    apply fold_mono _ (fun g hg => by simpa using (hm g hg).1) _ _ _ (by simp)
    intro i hi
    by_cases h : i < n
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] using
        hxy ⟨i, h⟩ (by simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] using hi)
    · simp [List.getD_eq_getElem?_getD, h] at hi

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have fold_len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_singleton, List.length_cons, List.length_nil]
      omega

  have fold_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (v : Fin n) :
      (C.wires (List.ofFn x)).getD v.val false = x v := by
    change (C.gates.foldl step _).getD _ _ = _
    rw [fold_preserves _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, v.isLt]

  let copyAt (C : Circuit) (j w : ℕ) : Circuit :=
    { C with gates := C.gates.set j ⟨GateOp.or, [w]⟩ }

  have copyAt_size (C : Circuit) (j w : ℕ) : (copyAt C j w).size = C.size := by
    change (C.gates.set j ⟨GateOp.or, [w]⟩).length = C.gates.length
    simp

  have copyAt_wires (C : Circuit) (j : Fin C.gates.length) (w : ℕ) (x : List Bool)
      (h : let pre := ({ C with gates := C.gates.take j.val } : Circuit).wires x
           pre.getD w false = (C.gates.get j).op.eval
             ((C.gates.get j).inputs.map fun i => pre.getD i false)) :
      (copyAt C j.val w).wires x = C.wires x := by
    let pre := ({ C with gates := C.gates.take j.val } : Circuit).wires x
    let g := C.gates.get j
    have split : C.gates.take j.val ++ g :: C.gates.drop (j.val+1) = C.gates := by
      simp [g,List.get_eq_getElem,List.getElem_cons_drop,List.take_append_drop]
    change (C.gates.set j.val _).foldl _ x = C.gates.foldl _ x
    conv_rhs => rw [← split]
    rw [List.set_eq_take_append_cons_drop,ite_eq_left j.isLt]
    let finish := fun b : Bool =>
      ({ C with gates := C.gates.drop (j.val+1) } : Circuit).wires (pre ++ [b])
    have head : GateOp.or.eval ([w].map fun i => pre.getD i false) = pre.getD w false := by
      change (pre.getD w false || false) = pre.getD w false
      exact Bool.or_false _
    simp only [List.foldl_append, List.foldl_cons]
    exact congrArg finish (head.trans h)

  have gate_value (C : Circuit) (j : Fin C.gates.length) (x : List Bool) :
      (C.wires x).getD (x.length+j.val) false =
      let pre := ({C with gates := C.gates.take j.val} : Circuit).wires x
      (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun i => pre.getD i false) := by
    let pre := ({C with gates := C.gates.take j.val} : Circuit).wires x
    let g := C.gates.get j
    have split : C.gates.take j.val ++ g :: C.gates.drop (j.val+1) = C.gates := by
      simp [g,List.get_eq_getElem,List.getElem_cons_drop,List.take_append_drop]
    have plen : pre.length = x.length+j.val := by
      change (List.foldl step x (C.gates.take j.val)).length = _
      rw [fold_len]
      simp
    change (C.gates.foldl step x).getD _ _ = _
    have he := congrArg (fun gs : List Gate => gs.foldl step x) split.symm
    rw [he,List.foldl_append,List.foldl_cons]
    change ((C.gates.drop (j.val+1)).foldl step (step pre g)).getD _ _ = _
    rw [fold_preserves _ _ _ (by simp [step,plen])]
    change (pre ++ [_]).getD (x.length+j.val) false = _
    rw [←plen]
    simp [List.getD_eq_getElem?_getD, g, pre]

  /- A singleton-true AND reading that singleton directly is just a copy. -/
  have raw_and_absorption {n : ℕ} (C : Circuit) (hm : Monotone2 C)
      (j : Fin C.gates.length) (v : Fin n)
      (hop : (C.gates.get j).op = GateOp.and)
      (hpin : v.val ∈ (C.gates.get j).inputs)
      (hsing : (C.wires (List.ofFn (fun k : Fin n => decide (k=v)))).getD
         (n+j.val) false = true) (x : Fin n → Bool) :
      (C.wires (List.ofFn x)).getD (n+j.val) false = x v := by
    cases hx : x v with
    | false =>
      cases hg : (C.wires (List.ofFn x)).getD (n+j.val) false with
      | false => rfl
      | true =>
        have he := gate_value C j (List.ofFn x)
        simp only [List.length_ofFn, hg, hop, eval_and, eval_or, List.all_map] at he
        have hraw := List.all_eq_true.mp he.symm v.val hpin
        change (({C with gates := C.gates.take j.val} : Circuit).wires (List.ofFn x)).getD v.val false = true at hraw
        rw [wires_input] at hraw
        simp [hx] at hraw
    | true =>
      apply wires_mono C hm (x := fun k : Fin n => decide (k=v)) (y := x) _ (n+j.val) hsing
      intro k hk
      have hkv : k=v := of_decide_eq_true hk
      simpa [hkv] using hx

  have raw_and_copy_wires {n : ℕ} (C : Circuit) (hm : Monotone2 C)
      (j : Fin C.gates.length) (v : Fin n)
      (hop : (C.gates.get j).op = GateOp.and)
      (hpin : v.val ∈ (C.gates.get j).inputs)
      (hsing : (C.wires (List.ofFn (fun k : Fin n => decide (k=v)))).getD
         (n+j.val) false = true) (x : Fin n → Bool) :
      (copyAt C j.val v.val).wires (List.ofFn x) = C.wires (List.ofFn x) := by
    apply copyAt_wires
    dsimp only
    rw [wires_input]
    have he := gate_value C j (List.ofFn x)
    simp only [List.length_ofFn] at he
    exact (raw_and_absorption C hm j v hop hpin hsing x).symm.trans he

  have copyAt_gate (C : Circuit) (j w k : ℕ) (hk : k < C.gates.length) :
      gateAt (copyAt C j w) k = if j=k then ⟨GateOp.or,[w]⟩ else gateAt C k := by
    unfold gateAt copyAt
    rw [List.getD_eq_getElem _ _ (by simpa using hk),List.getElem_set,
      List.getD_eq_getElem _ _ hk]

  have copyAt_mono (C : Circuit) (hm : Monotone2 C) (j w : ℕ) :
      Monotone2 (copyAt C j w) := by
    intro g hg
    obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hg
    have hk' : k < C.gates.length := by simpa [copyAt] using hk
    dsimp only [copyAt] at hk ⊢
    rw [List.getElem_set]
    split
    · simp
    · exact hm _ (List.getElem_mem hk')

  let andCost (C : Circuit) : ℕ := by
    classical
    exact (C.gates.filter fun g => decide (g.op = GateOp.and)).length

  have copyAt_cost (C : Circuit) (j : Fin C.gates.length) (w : ℕ)
      (hop : (C.gates.get j).op = GateOp.and) :
      andCost (copyAt C j.val w) + 1 = andCost C := by
    classical
    let g := C.gates.get j
    have split : C.gates.take j.val ++ g :: C.gates.drop (j.val+1) = C.gates := by
      simp [g,List.get_eq_getElem,List.getElem_cons_drop,List.take_append_drop]
    have hc := congrArg (fun gs : List Gate => (gs.filter fun g => decide (g.op = GateOp.and)).length) split
    have hg : g.op = GateOp.and := hop
    simp only [List.filter_append,List.filter_cons,hg,decide_true,ite_true,
      List.length_append,List.length_cons] at hc
    unfold andCost
    change ((C.gates.set j.val _).filter _).length + 1 = _
    rw [List.set_eq_take_append_cons_drop,ite_eq_left j.isLt]
    simp only [List.filter_append,List.filter_cons,
      reduceCtorEq,decide_false,ite_false,List.length_append]
    omega

  have true_and_rawpin {n : ℕ} (C : Circuit) (j : Fin C.gates.length) (v : Fin n)
      (hop : (C.gates.get j).op = GateOp.and)
      (hpin : v.val ∈ (C.gates.get j).inputs) (x : Fin n → Bool)
      (hon : (C.wires (List.ofFn x)).getD (n+j.val) false = true) : x v = true := by
    have he := gate_value C j (List.ofFn x)
    simp only [List.length_ofFn,hon,hop,eval_and, eval_or,List.all_map] at he
    have hraw := List.all_eq_true.mp he.symm v.val hpin
    change (({C with gates := C.gates.take j.val} : Circuit).wires (List.ofFn x)).getD v.val false = true at hraw
    rwa [wires_input] at hraw

  let RawClean (n : ℕ) (C : Circuit) : Prop :=
    ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.and →
      ∀ v : Fin n, v.val ∈ (C.gates.get j).inputs →
      ∀ u : Fin n, (C.wires (List.ofFn (fun k : Fin n => decide (k=u)))).getD
        (n+j.val) false = false

  let NoNewAnd (C D : Circuit) : Prop :=
    ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → gateAt D j = gateAt C j

  have copyAt_noNewAnd (C : Circuit) (j w : ℕ) : NoNewAnd C (copyAt C j w) := by
    intro k hk hop
    have hk' : k < C.gates.length := by simpa [copyAt] using hk
    rw [copyAt_gate C j w k hk'] at hop ⊢
    by_cases he : j=k
    · simp [he] at hop
    · simp [he]

  /- All ANDs having a primary-input operand can be cleaned, at unchanged size.
  Every wire is preserved, not only the output. This works even when a circuit
  mentions forward or missing wires; no ReadsBack assumption is needed. -/
  have raw_normalization (n : ℕ) (C : Circuit) (hm : Monotone2 C)
      :
      ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧
        D.output = C.output ∧
        (∀ x : Fin n → Bool, D.wires (List.ofFn x) = C.wires (List.ofFn x)) ∧ RawClean n D ∧ NoNewAnd C D := by
    classical
    have main : ∀ c : ℕ, ∀ C : Circuit, andCost C = c → Monotone2 C →
        ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧
          D.output = C.output ∧
          (∀ x : Fin n → Bool, D.wires (List.ofFn x) = C.wires (List.ofFn x)) ∧ RawClean n D ∧ NoNewAnd C D := by
      intro c
      induction c using Nat.strong_induction_on with
      | ind c ih =>
        intro C hcost hm
        by_cases hclean : RawClean n C
        · exact ⟨C,hm,rfl,rfl,fun _ => rfl,hclean,fun _ _ _ => rfl⟩
        · simp only [RawClean,not_forall] at hclean
          obtain ⟨j,hj⟩ := hclean
          push Not at hj
          obtain ⟨hop,v,hpin,u,hu⟩ := hj
          have hon : (C.wires (List.ofFn (fun k : Fin n => decide (k=u)))).getD
              (n+j.val) false = true := Bool.eq_true_of_not_eq_false hu
          have hvu : v=u := of_decide_eq_true (true_and_rawpin C j v hop hpin _ hon)
          subst u
          let B := copyAt C j.val v.val
          have hBcost : andCost B < c := by
            have hc := copyAt_cost C j v.val hop
            dsimp only [B]
            omega
          have hBm : Monotone2 B := copyAt_mono C hm _ _
          obtain ⟨D,hDm,hDs,hDo,hDw,hDc,hDn⟩ := ih (andCost B) hBcost B rfl hBm
          refine ⟨D,hDm,hDs.trans (copyAt_size C _ _),hDo,?_,hDc,?_⟩
          · intro x
            exact (hDw x).trans (raw_and_copy_wires C hm j v hop hpin hon x)
          · intro k hk hkop
            have hEq := hDn k hk hkop
            have hkB : k < B.gates.length := by change k < B.size; rw [←hDs]; exact hk
            exact hEq.trans (copyAt_noNewAnd C j.val v.val k hkB (hEq ▸ hkop))
    exact main (andCost C) C rfl hm

  /- The normalizer preserves least size in the public unrestricted-wire model. -/
  have least_raw_clean (n : ℕ) (C : Circuit) (hc : IsMinimalMonoCircuit n C) :
      ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = circuitFun n C ∧ RawClean n D := by
    obtain ⟨D,hm,hs,ho,hw,hclean,_⟩ := raw_normalization n C hc.1
    have he : circuitFun n D = circuitFun n C := by
      funext x
      change (D.wires (List.ofFn x)).getD D.output false =
        (C.wires (List.ofFn x)).getD C.output false
      rw [hw,ho]
    refine ⟨D,⟨hm,?_⟩,he,hclean⟩
    intro E hE hfun
    rw [hs]
    exact hc.2 E hE (hfun.trans he)


  -- Circuit existence builder adapted from accepted L_meta_2666.


  let wf (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
      Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

  have wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
      wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
    simp [wf, List.foldl_append]

  have wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
    induction gs with
    | nil => intro w; simp [wf]
    | cons g gs ih =>
      intro w
      have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      simp only [wf, List.foldl_cons] at this ⊢
      rw [this]; simp; omega

  have wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
      (wf gs w).getD i false = w.getD i false := by
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
      simp only [wf, List.foldl_cons] at this ⊢
      rw [this]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
      (hi : i < w.length + pre.length) :
      (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
    have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
    rw [this]
    exact wf_keep post _ i (by rw [wf_len]; exact hi)

  have getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
      (L ++ [a]).getD w false = L.getD w false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

  have getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
    simp [List.getD_eq_getElem?_getD]

  have getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
      (L ++ [a]).getD w false = false := by
    rw [List.getD_eq_default]; simp; omega

  have wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
    simp [wf, List.foldl_append]

  let build (n : ℕ) : List (Fin n × Fin n) → List Gate :=
    List.rec [⟨GateOp.or, []⟩] (fun e es gs =>
      gs ++ [⟨GateOp.and, [(e.1 : ℕ), (e.2 : ℕ)]⟩,
        ⟨GateOp.or, [n + 2 * es.length, n + 2 * es.length + 1]⟩])

  have build_len (n : ℕ) : ∀ E : List (Fin n × Fin n), (build n E).length = 1 + 2 * E.length := by
    intro E
    induction E with
    | nil => rfl
    | cons e es ih =>
      change (build n es ++ [Gate.mk GateOp.and [(e.1 : ℕ), (e.2 : ℕ)],
        Gate.mk GateOp.or [n + 2 * es.length, n + 2 * es.length + 1]]).length =
          1 + 2 * (es.length + 1)
      rw [List.length_append, ih]
      simp only [List.length_cons, List.length_nil]
      omega

  have build_mono (n : ℕ) : ∀ E : List (Fin n × Fin n), ∀ g ∈ build n E,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    intro E
    induction E with
    | nil => intro g hg; simp [build] at hg; subst hg; simp
    | cons e es ih =>
      intro g hg
      simp only [build, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hg | rfl | rfl
      · exact ih g hg
      · simp
      · simp

  have build_val (n : ℕ) (x : Fin n → Bool) : ∀ E : List (Fin n × Fin n),
      (wf (build n E) (List.ofFn x)).getD (n + 2 * E.length) false
        = E.any (fun e => x e.1 && x e.2) := by
    intro E
    induction E with
    | nil =>
      show ((List.ofFn x) ++ [GateOp.eval GateOp.or ([].map fun i => (List.ofFn x).getD i false)]).getD (n + 2 * 0) false = _
      have := getD_snoc_eq (List.ofFn x) (GateOp.eval GateOp.or ([].map fun i => (List.ofFn x).getD i false))
      rw [List.length_ofFn] at this
      rw [Nat.mul_zero, Nat.add_zero, this]
      rfl
    | cons e es ih =>
      have hlen : (wf (build n es) (List.ofFn x)).length = n + 2 * es.length + 1 := by
        rw [wf_len, build_len, List.length_ofFn]; omega
      have h1 : (wf (build n es) (List.ofFn x)).getD (e.1 : ℕ) false = x e.1 := by
        rw [wf_keep _ _ _ (by simp)]; simp
      have h2 : (wf (build n es) (List.ofFn x)).getD (e.2 : ℕ) false = x e.2 := by
        rw [wf_keep _ _ _ (by simp)]; simp
      show (wf (build n es ++ [⟨GateOp.and, [(e.1 : ℕ), (e.2 : ℕ)]⟩,
        ⟨GateOp.or, [n + 2 * es.length, n + 2 * es.length + 1]⟩]) (List.ofFn x)).getD
          (n + 2 * (es.length + 1)) false = _
      rw [wf_append]
      generalize hW : wf (build n es) (List.ofFn x) = W at *
      show ((W ++ [GateOp.eval GateOp.and ([(e.1 : ℕ), (e.2 : ℕ)].map fun i => W.getD i false)]) ++
        [GateOp.eval GateOp.or ([n + 2 * es.length, n + 2 * es.length + 1].map fun i =>
          (W ++ [GateOp.eval GateOp.and ([(e.1 : ℕ), (e.2 : ℕ)].map fun i => W.getD i false)]).getD i false)]).getD
          (n + 2 * (es.length + 1)) false = _
      have e3 : n + 2 * (es.length + 1) = (W ++ [GateOp.eval GateOp.and ([(e.1 : ℕ), (e.2 : ℕ)].map fun i => W.getD i false)]).length := by
        simp [hlen]; omega
      rw [e3, getD_snoc_eq]
      have e4 : n + 2 * es.length + 1 = W.length := by omega
      simp only [List.map_cons, List.map_nil]
      rw [getD_snoc_lt _ _ _ (by omega : n + 2 * es.length < W.length), e4, getD_snoc_eq, ih, h1, h2]
      simp [eval_and, eval_or, Bool.or_comm]


  have least_graph_exists : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 ∧ PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ := by
    classical
    intro n G _
    have hex : ∃ s : ℕ, ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ D.size = s := by
      let E : List (Fin n × Fin n) :=
        ((List.finRange n).product (List.finRange n)).filter (fun e => decide (G.Adj e.1 e.2))
      refine ⟨_, ⟨build n E, n + 2 * E.length⟩, build_mono n E, ?_, rfl⟩
      funext x
      show (wf (build n E) (List.ofFn x)).getD (n + 2 * E.length) false = _
      rw [build_val, graphFun_eq, Bool.eq_iff_iff]
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨e, he, h1, h2⟩
        have := (List.mem_filter.mp he).2
        exact ⟨e.1, e.2, by simpa using this, h1, h2⟩
      · rintro ⟨u, v, huv, h1, h2⟩
        exact ⟨(u, v), List.mem_filter.mpr ⟨by simp [List.pair_mem_product], by simpa using huv⟩, h1, h2⟩
    obtain ⟨D, hD, hf, hs⟩ := Nat.find_spec hex
    refine ⟨D, ⟨hD, ?_⟩, hf⟩
    intro D' hD' hf'
    rw [hs]
    exact Nat.find_min' hex ⟨D', hD', hf'.trans hf, rfl⟩


  have normalization_proved :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
          circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
          ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.and →
            ∀ v : Fin n, v.val ∈ (C.gates.get j).inputs → ∀ u : Fin n,
            (C.wires (List.ofFn (fun k : Fin n => decide (k=u)))).getD (n+j.val) false = false := by
    intro n G inst
    obtain ⟨C,hC,hCG⟩ := least_graph_exists n G
    obtain ⟨D,hD,hDC,hraw⟩ := least_raw_clean n C hC
    exact ⟨D,hD,hDC.trans hCG,hraw⟩

  intro n G inst
  dsimp only
  intro htri hsquare
  obtain ⟨C,hC,hCG,hraw⟩ := normalization_proved n G
  obtain ⟨D,hDm,hsize,hDC,hsafe⟩ := residual n G htri hsquare C hC hCG hraw
  have hDG : circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := hDC.trans hCG
  refine ⟨D,hDm,?_,?_,hsafe⟩
  · intro x
    have h := congrFun hDG x
    change D.eval (List.ofFn x) =
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) at h
    simpa only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or] using h
  · intro T hTm hTf
    apply hsize.trans (hC.2 T hTm _)
    funext x
    rw [hCG]
    change T.eval (List.ofFn x) =
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    simpa only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or] using hTf x
