import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3360_1
  (unused :
    let f := fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ (D : Circuit), FanInTwo D → D.size = 7 → (∀ g ∈ D.gates, g.op ≠ .not) →
    (∀ g ∈ D.gates, 9 ∉ g.inputs) → ∀ S ⊆ Finset.range 17, S.card ≤ 6 → 9 ∉ S →
    ∃ (x : Fin 9 → Bool) (v : Fin 9), x v = false ∧ f x = false ∧
      f (Function.update x v true) = true ∧
      ∀ k ∈ S, (D.wires (List.ofFn x ++ [false])).getD k false =
        (D.wires (List.ofFn (Function.update x v true) ++ [false])).getD k false)
  (seen :
    let f := fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ (C : Circuit), FanInTwo C → C.size = 8 → (∀ g ∈ C.gates, g.op ≠ .not) →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
    ∀ S ⊆ Finset.range 17, S.card ≤ 6 →
    9 ∈ S → (∀ v : ℕ, v = 0 ∨ v = 2 → v ∈ S ∨ ∃ g ∈ C.gates.drop 1, v ∈ g.inputs) →
    ∃ (x : Fin 9 → Bool) (v : Fin 9), x v = false ∧ f x = false ∧
      f (Function.update x v true) = true ∧
      ∀ k ∈ S, (C.wires (List.ofFn x)).getD k false =
        (C.wires (List.ofFn (Function.update x v true))).getD k false)
  (readOnly :
    let f := fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ (C : Circuit), FanInTwo C → C.size = 8 → (∀ g ∈ C.gates, g.op ≠ .not) →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
    ∀ S ⊆ Finset.range 17, S.card ≤ 6 →
    9 ∉ S → (∃ g ∈ C.gates.drop 1, 9 ∈ g.inputs) → (∀ v : ℕ, v = 0 ∨ v = 2 → v ∈ S ∨ ∃ g ∈ C.gates.drop 1, v ∈ g.inputs) →
    ∃ (x : Fin 9 → Bool) (v : Fin 9), x v = false ∧ f x = false ∧
      f (Function.update x v true) = true ∧
      ∀ k ∈ S, (C.wires (List.ofFn x)).getD k false =
        (C.wires (List.ofFn (Function.update x v true))).getD k false) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (8 : ℕ) → (∀ x5 ∈ x2.gates, x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x6 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = (x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)))) → ∀ x7 ⊆ Finset.range (17 : ℕ), x7.card ≤ (6 : ℕ) → ∃ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ) → Bool), x1 x10 ≠ x1 x11 ∧ ∀ x12 ∈ x7, (x2.wires (List.ofFn x10)).getD x12 Bool.false = (x2.wires (List.ofFn x11)).getD x12 Bool.false := by
  intro f C fan size positive first S range small
  change ∃ x y, f x ≠ f y ∧ ∀ k ∈ S,
    (C.wires (List.ofFn x)).getD k false = (C.wires (List.ofFn y)).getD k false
  classical
  by_contra failed
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  let agree := fun (v : ℕ) (x y : List Bool) =>
    x.length = y.length ∧ ∀ k, k ≠ v → x.getD k false = y.getD k false
  have extend (v : ℕ) (x y : List Bool) (hx : agree v x y) (b : Bool) :
      agree v (x ++ [b]) (y ++ [b]) := by
    obtain ⟨len, same⟩ := hx
    refine ⟨by simp [len], fun i hi => ?_⟩
    by_cases lt : i < x.length
    · rw [List.getD_append _ _ _ _ lt, List.getD_append _ _ _ _ (by omega)]
      exact same i hi
    · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), len]
  have propagate (gs : List Gate) (v : ℕ) (hread : ∀ g ∈ gs, v ∉ g.inputs)
      (x y : List Bool) (h : agree v x y) : agree v (gs.foldl step x) (gs.foldl step y) := by
    induction gs generalizing x y with
    | nil => exact h
    | cons g gs ih =>
      have val : g.op.eval (g.inputs.map fun k => x.getD k false) =
          g.op.eval (g.inputs.map fun k => y.getD k false) := by
        congr 1
        apply List.map_congr_left
        intro i hi
        exact h.2 i fun e => hread g List.mem_cons_self (e ▸ hi)
      have hs : agree v (step x g) (step y g) := by
        simpa only [step, val] using extend v x y h _
      exact ih (fun g' hg' => hread g' (List.mem_cons_of_mem g hg')) _ _ hs
  have preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have len : C.gates.length = 8 := size
  obtain ⟨g, gs, hgs⟩ : ∃ g gs, C.gates = g :: gs := by
    cases h : C.gates with
    | nil => simp [h] at len
    | cons g gs => exact ⟨g, gs, rfl⟩
  have glen : gs.length = 7 := by
    rw [hgs, List.length_cons] at len
    omega
  have drop : C.gates.drop 1 = gs := by simp [hgs]
  have tail (x : Fin 9 → Bool) : C.wires (List.ofFn x) =
      gs.foldl step (List.ofFn x ++ [x 0 || x 2]) := by
    have h := first x
    change (C.gates.foldl step (List.ofFn x)).getD 9 false = _ at h
    rw [hgs, List.foldl_cons, preserves _ _ _ (by simp [step])] at h
    have last (b : Bool) : (List.ofFn x ++ [b]).getD 9 false = b := by
      simp [List.getD_eq_getElem?_getD]
    change (List.ofFn x ++ [_]).getD 9 false = _ at h
    rw [last] at h
    change C.gates.foldl step (List.ofFn x) = _
    rw [hgs, List.foldl_cons]
    simp only [step, h]
  have endpoint (v : ℕ) (hv : v = 0 ∨ v = 2) :
      ∃ x y : Fin 9 → Bool, f x ≠ f y ∧
        (∀ i : Fin 9, i.val ≠ v → x i = y i) ∧ (x 0 || x 2) = (y 0 || y 2) := by
    rcases hv with rfl | rfl
    · refine ⟨![false,false,true,false,true,false,false,false,false],
        ![true,false,true,false,true,false,false,false,false], ?_, ?_, ?_⟩
      · dsimp only [f]
        decide +kernel
      · decide +kernel
      · decide +kernel
    · refine ⟨![true,false,false,true,false,false,false,false,false],
        ![true,false,true,true,false,false,false,false,false], ?_, ?_, ?_⟩
      · dsimp only [f]
        decide +kernel
      · decide +kernel
      · decide +kernel
  have need (v : ℕ) (hv : v = 0 ∨ v = 2) :
      v ∈ S ∨ ∃ g ∈ C.gates.drop 1, v ∈ g.inputs := by
    by_cases obs : v ∈ S
    · exact Or.inl obs
    right
    by_contra skip
    obtain ⟨x, y, different, differOnly, sameOR⟩ := endpoint v hv
    have reads : ∀ g ∈ gs, v ∉ g.inputs := by
      intro g hg hi
      exact skip ⟨g, drop ▸ hg, hi⟩
    have rawAgree : agree v (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp, fun i hi => ?_⟩
      by_cases lt : i < 9
      · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, lt, ↓reduceDIte,
          Option.getD_some] using differOnly ⟨i, lt⟩ hi
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, lt, ↓reduceDIte, Option.getD_none]
    have inputAgree : agree v (List.ofFn x ++ [x 0 || x 2]) (List.ofFn y ++ [y 0 || y 2]) := by
      simpa only [sameOR] using extend v _ _ rawAgree (y 0 || y 2)
    have result := propagate gs v reads _ _ inputAgree
    apply failed
    refine ⟨x, y, different, fun i hi => ?_⟩
    rw [tail x, tail y]
    exact result.2 i (fun e => obs (e ▸ hi))
  have finish (x : Fin 9 → Bool) (v : Fin 9) (hx : f x = false)
      (hy : f (Function.update x v true) = true)
      (same : ∀ k ∈ S, (C.wires (List.ofFn x)).getD k false =
        (C.wires (List.ofFn (Function.update x v true))).getD k false) : False := by
    exact failed ⟨x, Function.update x v true, by rw [hx, hy]; decide, same⟩
  by_cases obs : 9 ∈ S
  · obtain ⟨x, v, _, hx, hy, same⟩ := seen C fan size positive first S range small obs need
    exact finish x v hx hy same
  by_cases helps : ∃ g ∈ C.gates.drop 1, 9 ∈ g.inputs
  · obtain ⟨x, v, _, hx, hy, same⟩ := readOnly C fan size positive first S range small obs helps need
    exact finish x v hx hy same
  let D : Circuit := ⟨gs, 0⟩
  have hD k (hk : k ∈ D.gates) : k ∈ C.gates := by
    rw [hgs]
    exact List.mem_cons_of_mem _ hk
  have skip : ∀ k ∈ D.gates, 9 ∉ k.inputs := fun k hk u => helps ⟨k, drop ▸ hk, u⟩
  have unusedWire (x : Fin 9 → Bool) (q : ℕ) (hq : q ≠ 9) :
      (C.wires (List.ofFn x)).getD q false = (D.wires (List.ofFn x ++ [false])).getD q false := by
    rw [tail x]
    have seed : agree 9 (List.ofFn x ++ [x 0 || x 2]) (List.ofFn x ++ [false]) := by
      refine ⟨by simp, fun j hj => ?_⟩
      by_cases lt : j < 9
      · rw [List.getD_append _ _ _ _ (by simpa using lt), List.getD_append _ _ _ _ (by simpa using lt)]
      · have gt : 10 ≤ j := by omega
        rw [List.getD_eq_default _ _ (by simpa using gt),
          List.getD_eq_default _ _ (by simpa using gt)]
    exact (propagate gs 9 skip _ _ seed).2 q hq
  obtain ⟨x, v, _, hx, hy, same⟩ := unused D (fun k hk => fan k (hD k hk)) glen
    (fun k hk => positive k (hD k hk)) skip S range small obs
  refine finish x v hx hy (fun k hk => ?_)
  have hq : k ≠ 9 := fun e => obs (e ▸ hk)
  rw [unusedWire x k hq, unusedWire _ k hq]
  exact same k hk
