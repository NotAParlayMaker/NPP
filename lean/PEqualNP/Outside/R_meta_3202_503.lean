import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3202_503
    (lower :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        (∀ (x3 : Fin (9 : ℕ) → Bool),
          x1.eval (List.ofFn x3 ++ [Bool.false]) =
            (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) ||
             x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) ||
             x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) ||
             x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) ||
             x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) ||
             x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) ||
             x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) ||
             x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) ||
             x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) ||
             x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) ||
             x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) ||
             x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) →
        (15 : ℕ) ≤ x1.size)
    (internal :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length),
          x3 < x4 ∧ ↑x3 = (7 : ℕ) ∧ (↑x4 : ℕ) < 14 ∧
          (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∀ (x5 : Fin x1.gates.length),
            (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) →
        (∀ (x4 : Fin (9 : ℕ) → Bool),
          (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) →
        (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 =
          fun (x5 : Fin (9 : ℕ) → Bool) =>
            x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) ||
            x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) ||
            x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) ||
            x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) ||
            x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) ||
            x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) ||
            x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) ||
            x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) ||
            x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) ||
            x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) ||
            x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) ||
            x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) →
        x1.size = 15 →
        x1.output = 23 →
        (16 : ℕ) ≤ x1.size)
    :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length),
          x3 < x4 ∧ ↑x3 = (7 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∀ (x5 : Fin x1.gates.length),
            (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) →
        (∀ (x4 : Fin (9 : ℕ) → Bool),
          (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) →
        (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 =
          fun (x5 : Fin (9 : ℕ) → Bool) =>
            x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) ||
            x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) ||
            x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) ||
            x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) ||
            x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) ||
            x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) ||
            x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) ||
            x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) ||
            x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) ||
            x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) ||
            x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) ||
            x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) →
        (16 : ℕ) ≤ x1.size := by
  let read (w : List Bool) (i : ℕ) : Bool := w.getD i false

  let gateVal (w : List Bool) (g : Gate) : Bool :=
    g.op.eval (g.inputs.map (read w))

  let step (w : List Bool) (g : Gate) : List Bool := w ++ [gateVal w g]

  have appendRead (w : List Bool) (b : Bool) (i : ℕ) :
      read (w ++ [b]) i = if i = w.length then b else read w i := by
    unfold read
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
    by_cases hlt : i < w.length
    · simp [hlt, show i ≠ w.length by omega]
    · by_cases heq : i = w.length
      · simp [heq]
      · have hs : i - w.length ≠ 0 := by omega
        simp [hlt, heq, hs]

  have stepLen (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
    simp [step]

  have foldLen (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons, ih, stepLen, List.length_cons]; omega

  have stable (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      read (gs.foldl step w) i = read w i := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by rw [stepLen]; omega)]
      simp [step, appendRead, show i ≠ w.length by omega]

  have valEq (g : Gate) (u v : List Bool) (h : ∀ i ∈ g.inputs, read u i = read v i) :
      gateVal u g = gateVal v g := by
    unfold gateVal
    rw [List.map_congr_left h]

  -- Trace the requested wire indices backward. Expanding a gate adds at most one index.
  have support (gs : List Gate) (n : ℕ) (S : Finset ℕ)
      (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      ∃ T : Finset ℕ, T.card ≤ S.card + gs.length ∧
        ∀ u v : List Bool, u.length = n → v.length = n →
          (∀ i ∈ T, read u i = read v i) →
          ∀ i ∈ S, read (gs.foldl step u) i = read (gs.foldl step v) i := by
    classical
    induction gs generalizing n S with
    | nil => exact ⟨S, by simp, fun _ _ _ _ h => h⟩
    | cons g gs ih =>
      obtain ⟨T, hT, hstep⟩ := ih (n + 1) S (fun a ha => hf a (List.mem_cons_of_mem _ ha))
      by_cases hn : n ∈ T
      · let U := T.erase n ∪ g.inputs.toFinset
        refine ⟨U, ?_, ?_⟩
        · have hu := Finset.card_union_le (T.erase n) g.inputs.toFinset
          rw [Finset.card_erase_of_mem hn] at hu
          have hl := List.toFinset_card_le g.inputs
          have hg := hf g (List.mem_cons_self ..)
          have hp : 0 < T.card := Finset.card_pos.mpr ⟨n, hn⟩
          change U.card ≤ S.card + (g :: gs).length
          simp only [U] at *
          simp only [List.length_cons]
          omega
        · intro u v hu hv heq
          apply hstep (step u g) (step v g) (by simp [stepLen, hu]) (by simp [stepLen, hv])
          intro i hi
          simp only [step, appendRead, hu, hv]
          by_cases hi' : i = n
          · simp only [hi', ite_true]
            exact valEq g u v fun j hj => heq j (Finset.mem_union_right _ (List.mem_toFinset.mpr hj))
          · simp only [hi', ite_false]
            exact heq i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hi', hi⟩))
      · refine ⟨T, by simp only [List.length_cons]; omega, ?_⟩
        intro u v hu hv heq
        apply hstep (step u g) (step v g) (by simp [stepLen, hu]) (by simp [stepLen, hv])
        intro i hi
        have hne : i ≠ n := fun he => hn (he ▸ hi)
        simpa [step, appendRead, hu, hv, hne] using heq i hi

  have readOfFn (x : Fin 9 → Bool) (i : ℕ) :
      read (List.ofFn x) i = if h : i < 9 then x ⟨i, h⟩ else false := by
    change (List.ofFn x).getD i false = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split <;> rfl

  let Below (u v : List Bool) : Prop :=
    ∀ i, read u i = true → read v i = true

  have appendBelow (u v : List Bool) (a b : Bool) (hlen : u.length = v.length)
      (h : Below u v) (hab : a = true → b = true) : Below (u ++ [a]) (v ++ [b]) := by
    intro i hi
    rw [appendRead] at hi ⊢
    rw [← hlen]
    by_cases heq : i = u.length
    · simpa only [heq, ite_true] using hab (by simpa only [heq, ite_true] using hi)
    · simpa only [heq, ite_false] using h i (by simpa only [heq, ite_false] using hi)

  have monoVal (g : Gate) (u v : List Bool) (h : Below u v)
      (hg : g.op = .and ∨ g.op = .or) : gateVal u g = true → gateVal v g = true := by
    change g.op.eval (g.inputs.map (read u)) = true → g.op.eval (g.inputs.map (read v)) = true
    rcases hg with hg | hg
    · rw [hg]
      change (g.inputs.map (read u)).all id = true → (g.inputs.map (read v)).all id = true
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro hh i hi
      exact h i (hh i hi)
    · rw [hg]
      change (g.inputs.map (read u)).any id = true → (g.inputs.map (read v)).any id = true
      simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i, hi, hh⟩
      exact ⟨i, hi, h i hh⟩

  have monoFold (gs : List Gate) (u v : List Bool) (he : u.length = v.length)
      (h : Below u v) (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      Below (gs.foldl step u) (gs.foldl step v) := by
    induction gs generalizing u v with
    | nil => exact h
    | cons g gs ih =>
      apply ih (step u g) (step v g) (by rw [stepLen, stepLen, he])
      · exact appendBelow u v _ _ he h (monoVal g u v h (hg g (List.mem_cons_self ..)))
      · exact fun a ha => hg a (List.mem_cons_of_mem _ ha)

  have notVal (g : Gate) (w : List Bool) (hg : g.op = .not) :
      gateVal w g = !(read w (g.inputs.headD w.length)) := by
    have h : read w w.length = false := by
      change w.getD w.length false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    change g.op.eval (g.inputs.map (read w)) = _
    rw [hg]
    change (!((g.inputs.map (read w)).headD false)) = _
    rw [← h, List.headD_map]

  let edge (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5

  let neighbor (i : Fin 9) : Fin 9 := ([1, 0, 1, 2, 3, 0, 1, 2, 3] : List (Fin 9)).getD i.val 0

  let low (i : Fin 9) (j : Fin 9) : Bool := decide (j = neighbor i)

  let high (i : Fin 9) (j : Fin 9) : Bool := decide (j = neighbor i ∨ j = i)

  have transitions : ∀ i : Fin 9, edge (low i) = false ∧ edge (high i) = true := by decide

  have existsMissing (T : Finset ℕ) (hT : T.card ≤ 8) :
      ∃ i : Fin 9, i.val ∉ T := by
    by_contra! h
    have hincl : Finset.range 9 ⊆ T := fun i hi => h ⟨i, Finset.mem_range.mp hi⟩
    have hc := Finset.card_le_card hincl
    simp only [Finset.card_range] at hc
    omega

  have lowBelow (i : Fin 9) : Below (List.ofFn (low i)) (List.ofFn (high i)) := by
    intro k hk
    simp only [readOfFn] at hk ⊢
    split at hk <;> rename_i hb
    · simp only [low, decide_eq_true_eq] at hk
      simp only [dite_eq_left hb, high, decide_eq_true_eq]
      exact Or.inl hk
    · contradiction

  have lowAgree (i : Fin 9) (k : ℕ) (hk : k ≠ i.val) :
      read (List.ofFn (low i)) k = read (List.ofFn (high i)) k := by
    rw [readOfFn, readOfFn]
    split <;> rename_i h
    · have hne : (⟨k, h⟩ : Fin 9) ≠ i := fun e => hk (congrArg Fin.val e)
      simp [low, high, hne]
    · rfl

  have readGate (C : Circuit) (x : Fin 9 → Bool) (i : Fin C.gates.length) :
      read (C.wires (List.ofFn x)) (9 + i.val) =
        gateVal ((C.gates.take i.val).foldl step (List.ofFn x)) (C.gates.get i) := by
    let w := (C.gates.take i.val).foldl step (List.ofFn x)
    have hw : w.length = 9 + i.val := by
      simp [w, foldLen]
    have htake : C.gates.take (i.val + 1) = C.gates.take i.val ++ [C.gates.get i] :=
      List.take_succ_eq_append_getElem i.isLt
    have hsplit : C.gates = (C.gates.take i.val ++ [C.gates.get i]) ++ C.gates.drop (i.val + 1) := by
      rw [← htake]
      exact (List.take_append_drop _ _).symm
    have hwire : C.wires (List.ofFn x) = (C.gates.drop (i.val + 1)).foldl step (step w (C.gates.get i)) := by
      calc
        C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
        _ = ((C.gates.take i.val ++ [C.gates.get i]) ++ C.gates.drop (i.val + 1)).foldl step (List.ofFn x) :=
          congrArg (fun gs => gs.foldl step (List.ofFn x)) hsplit
        _ = (C.gates.drop (i.val + 1)).foldl step (step w (C.gates.get i)) := by
          simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, w]
    rw [hwire, stable _ _ _ (by rw [stepLen, hw]; omega)]
    change read (w ++ [gateVal w (C.gates.get i)]) (9 + i.val) = _
    rw [appendRead, hw, ite_eq_left rfl]

  have onlyAndOr (C : Circuit) (h : FanInTwo C) (g : Gate) (hg : g ∈ C.gates)
      (hne : g.op ≠ .not) : g.op = .and ∨ g.op = .or := by
    have hm := (h g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hne hn).elim

  -- The first negation misses at least one input. On that input's rising pair,
  -- all wires before the second negation can only rise.
  have notOutputImpossible (C : Circuit) (hfan : FanInTwo C)
      (i j : Fin C.gates.length) (hi : i.val = 7) (hij : i < j)
      (hopi : (C.gates.get i).op = .not) (hopj : (C.gates.get j).op = .not)
      (honly : ∀ k : Fin C.gates.length, (C.gates.get k).op = .not → k = i ∨ k = j)
      (houtput : C.output = 9 + j.val) (hfunc : circuitFun 9 C = edge) : False := by
    let p := C.gates.take i.val
    have hp : p.length = 7 := by
      calc
        p.length = i.val := by simp [p]
        _ = 7 := hi
    let source := (C.gates.get i).inputs.headD 16
    obtain ⟨T, hT, hs⟩ := support p 9 {source} (fun g hg => (hfan g (List.mem_of_mem_take hg)).2)
    have hT' : T.card ≤ 8 := by simpa [hp] using hT
    obtain ⟨bit, hbit⟩ := existsMissing T hT'
    let u := List.ofFn (low bit)
    let v := List.ofFn (high bit)
    have hu : u.length = 9 := by simp [u]
    have hv : v.length = 9 := by simp [v]
    have heq : read (p.foldl step u) source = read (p.foldl step v) source := by
      apply hs u v hu hv _ source (Finset.mem_singleton_self _)
      intro k hk
      apply lowAgree
      intro hki
      exact hbit (hki ▸ hk)
    have hval : gateVal (p.foldl step u) (C.gates.get i) = gateVal (p.foldl step v) (C.gates.get i) := by
      rw [notVal _ _ hopi, notVal _ _ hopi, foldLen, foldLen, hu, hv, hp]
      exact congrArg Bool.not heq
    have hpre : ∀ g ∈ p, g.op = .and ∨ g.op = .or := by
      intro g hg
      apply onlyAndOr C hfan g (List.mem_of_mem_take hg)
      intro hgn
      obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp hg
      have hki : k < i.val := lt_of_lt_of_le hk (Nat.min_le_left _ _)
      let ki : Fin C.gates.length := ⟨k, lt_of_lt_of_le hk (Nat.min_le_right _ _)⟩
      rcases honly ki hgn with h | h
      · have he := congrArg Fin.val h
        change k = i.val at he
        omega
      · have he := congrArg Fin.val h
        change k = j.val at he
        have hj : i.val < j.val := hij
        omega
    have hmono := monoFold p u v (hu.trans hv.symm) (lowBelow bit) hpre
    have hmid : Below ((C.gates.take (i.val + 1)).foldl step u) ((C.gates.take (i.val + 1)).foldl step v) := by
      simp only [List.take_succ_eq_append_getElem i.isLt, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact appendBelow (p.foldl step u) (p.foldl step v) _ _
        (by rw [foldLen, foldLen, hu, hv]) hmono (fun h => hval ▸ h)
    let m := (C.gates.take j.val).drop (i.val + 1)
    have hm : ∀ g ∈ m, g.op = .and ∨ g.op = .or := by
      intro g hg
      apply onlyAndOr C hfan g (List.mem_of_mem_take (List.mem_of_mem_drop hg))
      intro hgn
      obtain ⟨offset, hoffset, eqg⟩ := List.mem_drop_iff_getElem.mp hg
      simp only [List.length_take] at hoffset
      let ki : Fin C.gates.length := ⟨i.val + 1 + offset, by omega⟩
      have he : (C.gates.get ki) = g := by
        change C.gates[i.val + 1 + offset] = g
        simpa only [List.getElem_take] using eqg
      rcases honly ki (he ▸ hgn) with h | h
      · have hk := congrArg Fin.val h
        change i.val + 1 + offset = i.val at hk
        omega
      · have hk := congrArg Fin.val h
        change i.val + 1 + offset = j.val at hk
        omega
    have hsplit : C.gates.take j.val = C.gates.take (i.val + 1) ++ m := by
      have hle : i.val + 1 ≤ j.val := hij
      conv_rhs => rw [← show (C.gates.take j.val).take (i.val + 1) = C.gates.take (i.val + 1) by
        rw [List.take_take, Nat.min_eq_left hle]]
      exact (List.take_append_drop _ _).symm
    have hbef : Below ((C.gates.take j.val).foldl step u) ((C.gates.take j.val).foldl step v) := by
      rw [hsplit, List.foldl_append, List.foldl_append]
      exact monoFold m _ _ (by rw [foldLen, foldLen, hu, hv]) hmid hm
    have hlo : circuitFun 9 C (low bit) = false := by rw [hfunc]; exact (transitions bit).1
    have hhi : circuitFun 9 C (high bit) = true := by rw [hfunc]; exact (transitions bit).2
    change read (C.wires (List.ofFn (low bit))) C.output = false at hlo
    change read (C.wires (List.ofFn (high bit))) C.output = true at hhi
    rw [houtput, readGate, notVal _ _ hopj] at hlo hhi
    change (!(read ((C.gates.take j.val).foldl step u) _)) = false at hlo
    change (!(read ((C.gates.take j.val).foldl step v) _)) = true at hhi
    have hlength : ((C.gates.take j.val).foldl step u).length = ((C.gates.take j.val).foldl step v).length := by
      rw [foldLen, foldLen, hu, hv]
    rw [← hlength] at hhi
    simp only [Bool.not_eq_false', Bool.not_eq_true'] at hlo hhi
    have habs := hbef _ hlo
    exact Bool.false_ne_true (hhi.symm.trans habs)

  -- An earlier output would survive deleting the last gate, violating the lower bound.
  have lastOutput (C : Circuit) (hfan : FanInTwo C) (hfunc : circuitFun 9 C = edge)
      (hsize : C.gates.length = 15)
      (hlower : ∀ D : Circuit, FanInTwo D → circuitFun 9 D = edge → 15 ≤ D.size) :
      C.output = 23 := by
    by_cases hhi : 23 < C.output
    · have h := congrFun hfunc (high 0)
      change read (C.wires (List.ofFn (high 0))) C.output = edge (high 0) at h
      have hlen : (C.wires (List.ofFn (high 0))).length = 24 := by
        change (C.gates.foldl step (List.ofFn (high 0))).length = 24
        rw [foldLen, List.length_ofFn, hsize]
      change (C.wires (List.ofFn (high 0))).getD C.output false = _ at h
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), (transitions 0).2] at h
      contradiction
    · by_contra hne
      have hlt : C.output < 23 := by omega
      let D : Circuit := ⟨C.gates.take 14, C.output⟩
      have hd : FanInTwo D := fun g hg => hfan g (List.mem_of_mem_take hg)
      have he : circuitFun 9 D = edge := by
        funext x
        rw [← hfunc]
        change read ((C.gates.take 14).foldl step (List.ofFn x)) C.output =
          read (C.gates.foldl step (List.ofFn x)) C.output
        let w := (C.gates.take 14).foldl step (List.ofFn x)
        have hn : C.output < w.length := by
          simpa [w, foldLen, hsize] using hlt
        have hs : C.gates.foldl step (List.ofFn x) = (C.gates.drop 14).foldl step w := by
          calc
            _ = ((C.gates.take 14) ++ C.gates.drop 14).foldl step (List.ofFn x) :=
              congrArg (fun gs => gs.foldl step (List.ofFn x)) (List.take_append_drop 14 C.gates).symm
            _ = (C.gates.drop 14).foldl step w := by simp only [List.foldl_append, w]
        rw [hs]
        exact (stable _ _ _ hn).symm
      have hh := hlower D hd he
      have hD : D.size = 14 := by
        change (C.gates.take 14).length = 14
        simp [hsize]
      omega

  let shiftWire (i : ℕ) : ℕ := if i < 9 then i else i + 1

  let liftGate (g : Gate) : Gate := ⟨g.op, g.inputs.map shiftWire⟩

  -- Inserting a false input shifts gate wires by one and leaves the first nine wires fixed.
  have foldLift (gs : List Gate) (u v : List Bool) (hu : 9 ≤ u.length)
      (hv : v.length = u.length + 1) (hread : ∀ i, read u i = read v (shiftWire i)) :
      ∀ i, read (gs.foldl step u) i = read ((gs.map liftGate).foldl step v) (shiftWire i) := by
    induction gs generalizing u v with
    | nil => exact hread
    | cons g gs ih =>
      simp only [List.foldl_cons, List.map_cons]
      apply ih (step u g) (step v (liftGate g))
      · rw [stepLen]; omega
      · rw [stepLen, stepLen, hv]
      · intro i
        have hc : gateVal u g = gateVal v (liftGate g) := by
          simp only [gateVal, liftGate, List.map_map]
          change g.op.eval (g.inputs.map (read u)) =
            g.op.eval (g.inputs.map (fun j => read v (shiftWire j)))
          rw [List.map_congr_left (fun j _ => hread j)]
        have hs : shiftWire i = v.length ↔ i = u.length := by
          unfold shiftWire
          split <;> omega
        simp only [step, appendRead, hs, hread, hc]

  have lowerFromPadded
      (padded : ∀ C : Circuit, FanInTwo C → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [false]) = edge x) →
        15 ≤ C.size)
      (C : Circuit) (hfan : FanInTwo C) (hfunc : circuitFun 9 C = edge) : 15 ≤ C.size := by
    let D : Circuit := ⟨C.gates.map liftGate, shiftWire C.output⟩
    have hD : FanInTwo D := by
      intro g hg
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
      simpa only [liftGate, List.length_map] using hfan f hf
    have he : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) = edge x := by
      intro x
      let u := List.ofFn x
      let v := u ++ [false]
      have hu : u.length = 9 := by simp [u]
      have hr : ∀ i, read u i = read v (shiftWire i) := by
        intro i
        by_cases hi : i < 9
        · have hn : i ≠ u.length := by omega
          simp only [shiftWire, ite_eq_left hi, v, appendRead, ite_eq_right hn]
        · have hs : shiftWire i ≠ u.length := by simp only [shiftWire, ite_eq_right hi]; omega
          change read u i = read (u ++ [false]) (shiftWire i)
          rw [appendRead, ite_eq_right hs]
          change u.getD i false = u.getD (shiftWire i) false
          simp only [shiftWire, ite_eq_right hi, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (show u.length ≤ i by omega),
            List.getElem?_eq_none (show u.length ≤ i + 1 by omega)]
      have hw := foldLift C.gates u v (by omega) (by simp [v]) hr C.output
      change read ((C.gates.map liftGate).foldl step v) (shiftWire C.output) = edge x
      rw [← hw]
      exact congrFun hfunc x
    have h := padded D hD he
    change 15 ≤ (C.gates.map liftGate).length at h
    change 15 ≤ C.gates.length
    simpa only [List.length_map] using h
  intro C hfan hnots hfirst hfunc
  have ordinary := lowerFromPadded lower
  have hmin := ordinary C hfan hfunc
  by_contra! hsize
  have hlen : C.gates.length = 15 := by
    change 15 ≤ C.gates.length at hmin
    change C.gates.length < 16 at hsize
    omega
  have hout := lastOutput C hfan hfunc hlen ordinary
  obtain ⟨i, j, hij, hi, hopi, hopj, honly⟩ := hnots
  have hjlt := j.isLt
  by_cases hj : j.val = 14
  · exact notOutputImpossible C hfan i j hi hij hopi hopj honly (by omega) hfunc
  · have hj' : j.val < 14 := by omega
    have h := internal C hfan ⟨i, j, hij, hi, hj', hopi, hopj, honly⟩ hfirst hfunc hlen hout
    omega
