import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5172_572
    (hZeroNot29 :
      let base : List ℕ := [503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608]
      ∀ (i j : Fin 9),
        9 * i.val + j.val ∈ ([1, 2, 3, 4, 6, 11, 12, 13, 14, 15, 16, 17, 21, 22, 24, 25, 26, 31, 33, 42, 61] : List ℕ) →
        let seed : List ℕ := [0, 536870911] ++ base ++ [33489407, base.getD i.val 0 ||| base.getD j.val 0]
        ∀ L : List ℕ, L.length ≤ 13 →
          (∀ t : Fin L.length, ∃ a ∈ seed ++ L.take t.val, ∃ b ∈ seed ++ L.take t.val,
            L.get t = (a &&& b) ∨ L.get t = (a ||| b)) →
          65535 ∉ seed ++ L)
    (hDeMorgan : ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (V : Fin n → Fin m → Bool), PEqualNP.MetaComplexity.FanInTwo C →
      let I := (fun _ : Fin m => false) :: List.ofFn V
      ∃ S : List (Fin m → Bool),
        S.length ≤ C.gates.countP (fun g => !(g.op.eval [false])) ∧
        (∀ (k : ℕ) (hk : k < S.length),
          ∃ a ∈ I ++ S.take k, ∃ b ∈ I ++ S.take k, ∃ u v : Bool,
            S[k] = fun r => (a r ^^ u) && (b r ^^ v)) ∧
        ∃ a ∈ I ++ S, ∃ u : Bool, ∀ r : Fin m,
          C.eval (List.ofFn (fun i => V i r)) = (a r ^^ u))
    (hSignedAnd13 : ∀ S : List (Fin 512 → Bool), S.length ≤ 13 →
      let I := (fun _ : Fin 512 => false) :: List.ofFn (fun (i : Fin 9) (r : Fin 512) =>
        ([1, 2, 4, 8, 16, 32, 64, 128, 256] : List ℕ).getD i.val 0 &&& r.val != 0)
      (∀ (k : ℕ) (hk : k < S.length),
        ∃ a ∈ I ++ S.take k, ∃ b ∈ I ++ S.take k, ∃ u v : Bool,
          S[k] = fun r => (a r ^^ u) && (b r ^^ v)) →
      ∀ a ∈ I ++ S, ∀ u : Bool, ∃ r : Fin 512,
        (a r ^^ u) ≠ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ).any (fun e => r.val &&& e == e)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; have x2 : Fin (9 : ℕ) → Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x5 ++ [!x5 (0 : Fin (9 : ℕ)), x5 x2 || x5 x3]) = x1 x5; ∀ (x3 x4 : Fin (9 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (9 : ℕ) * ↑x3 + ↑x4 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (11 : ℕ), (12 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (21 : ℕ), (22 : ℕ), (24 : ℕ), (25 : ℕ), (26 : ℕ), (31 : ℕ), (33 : ℕ), (42 : ℕ), (61 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) → (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x10 : ℕ) => Bool.false) Bool.false x9.op) x5.gates).length ≤ (1 : ℕ) → ¬x2 x3 x4 x5 := by
  dsimp only
  intro i j C hrep hfan hsz hnot hcomp
  let isNot : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
    PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op
  by_cases hz : (C.gates.filter isNot).length = 0
  · have hnoNot : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      have hprop := hfan g hg
      refine ⟨?_, hprop.2⟩
      rcases hprop.1 with ha | ho | hn
      · exact Or.inl ha
      · exact Or.inr ho
      · exfalso
        have hmem : g ∈ C.gates.filter isNot := by
          apply List.mem_filter.mpr
          refine ⟨hg, ?_⟩
          change PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op = true
          rw [hn]
        have hpos : 0 < (C.gates.filter isNot).length := List.length_pos_of_mem hmem
        omega
    let rows : List ℕ := [6, 12, 24, 66, 132, 160, 264, 288, 320, 3, 13, 17, 33, 133, 265, 321,
      42, 50, 104, 116, 138, 200, 208, 276, 402, 69, 201, 261, 385]
    let rowIn (k : Fin 29) : Fin 9 → Bool := fun v => (rows.getD k.val 0).testBit v.val
    let base : List ℕ := [503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608]
    let init : List ℕ := base ++ [33489407, base.getD i.val 0 ||| base.getD j.val 0]
    let c0 : List ℕ := [0, 536870911]
    have hbase_lt : ∀ v : Fin 9, base.getD v.val 0 < 2 ^ 29 := by decide
    have hnot0_lt : (33489407 : ℕ) < 2 ^ 29 := by decide
    have hor_lt : (base.getD i.val 0 ||| base.getD j.val 0) < 2 ^ 29 :=
      Nat.or_lt_two_pow (hbase_lt i) (hbase_lt j)
    have hinit_len : init.length = 11 := by simp [init, base]
    have hinit_lt : ∀ w ∈ init, w < 2 ^ 29 := by
      intro w hw
      simp only [init, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with hb | h0 | h1
      · have hall : ∀ x ∈ base, x < 2 ^ 29 := by decide
        exact hall w hb
      · rw [h0]; exact hnot0_lt
      · rw [h1]; exact hor_lt
    have hbase_bit : ∀ (k : Fin 29) (v : Fin 9), (base.getD v.val 0).testBit k.val = rowIn k v := by
      decide
    have hnot0_bit : ∀ k : Fin 29, (33489407 : ℕ).testBit k.val = !(rowIn k 0) := by
      decide
    have htarget_bit : ∀ k : Fin 29, (65535 : ℕ).testBit k.val =
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] :
          List (Fin 9 × Fin 9)).any (fun e => rowIn k e.1 && rowIn k e.2) := by
      decide
    have hor_bit : ∀ k : Fin 29,
        (base.getD i.val 0 ||| base.getD j.val 0).testBit k.val = (rowIn k i || rowIn k j) := by
      intro k
      rw [Nat.testBit_or, hbase_bit k i, hbase_bit k j]
    have hinit_bit : ∀ (k : Fin 29) (idx : ℕ),
        (init.getD idx 0).testBit k.val =
          (List.ofFn (rowIn k) ++ [!rowIn k 0, rowIn k i || rowIn k j]).getD idx false := by
      intro k idx
      by_cases h11 : idx < 11
      · by_cases h9 : idx < 9
        · have hl1 : idx < base.length := by simp [base]; exact h9
          have heq1 : init.getD idx 0 = base.getD idx 0 := by
            simp only [init]
            exact List.getD_append _ _ _ _ hl1
          have hlo : idx < (List.ofFn (rowIn k)).length := by simp [List.length_ofFn]; exact h9
          have heq2 : (List.ofFn (rowIn k) ++ [!rowIn k 0, rowIn k i || rowIn k j]).getD idx false =
              (List.ofFn (rowIn k)).getD idx false :=
            List.getD_append _ _ _ _ hlo
          rw [heq1, heq2, List.getD_eq_getElem _ _ hlo, List.getElem_ofFn]
          exact hbase_bit k ⟨idx, h9⟩
        · have hidx : idx = 9 ∨ idx = 10 := by omega
          rcases hidx with rfl | rfl
          · have h1 : init.getD 9 0 = 33489407 := by simp [init, base]
            have h2 : (List.ofFn (rowIn k) ++ [!rowIn k 0, rowIn k i || rowIn k j]).getD 9 false = !rowIn k 0 := by
              simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
            rw [h1, h2]
            exact hnot0_bit k
          · have h1 : init.getD 10 0 = (base.getD i.val 0 ||| base.getD j.val 0) := by
              simp [init, base]
            have h2 : (List.ofFn (rowIn k) ++ [!rowIn k 0, rowIn k i || rowIn k j]).getD 10 false =
                (rowIn k i || rowIn k j) := by
              simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
            rw [h1, h2]
            exact hor_bit k
      · have h1 : init.getD idx 0 = 0 := List.getD_eq_default _ _ (by rw [hinit_len]; omega)
        have h2 : (List.ofFn (rowIn k) ++ [!rowIn k 0, rowIn k i || rowIn k j]).getD idx false = false :=
          List.getD_eq_default _ _ (by simp; omega)
        rw [h1, h2, Nat.zero_testBit]
    let gateVal29 (W : List ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) : ℕ :=
      if g.inputs.length = 0 then (if g.op.eval [] = true then 536870911 else 0)
      else if g.inputs.length = 1 then W.getD (g.inputs.getD 0 0) 0
      else if g.op.eval [] = true then W.getD (g.inputs.getD 0 0) 0 &&& W.getD (g.inputs.getD 1 0) 0
      else W.getD (g.inputs.getD 0 0) 0 ||| W.getD (g.inputs.getD 1 0) 0
    have h511_all : ∀ k : Fin 29, (536870911 : ℕ).testBit k.val = true := by decide
    have hstep_sim : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
        (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
        ∀ (W : List ℕ) (ws : Fin 29 → List Bool),
        (∀ k : Fin 29, W.length = (ws k).length) →
        (∀ x ∈ W, x < 2 ^ 29) →
        (∀ (k : Fin 29) (idx : ℕ), (W.getD idx 0).testBit k.val = (ws k).getD idx false) →
        ∃ L : List ℕ, L.length = gs.length ∧
          (∀ w ∈ W ++ L, w < 2 ^ 29) ∧
          (∀ t : Fin L.length,
            ∃ a ∈ c0 ++ W ++ L.take t.val, ∃ b ∈ c0 ++ W ++ L.take t.val,
              L.get t = (a &&& b) ∨ L.get t = (a ||| b)) ∧
          (∀ (k : Fin 29) (idx : ℕ),
            ((W ++ L).getD idx 0).testBit k.val =
              (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun q => w.getD q false))]) (ws k)).getD idx false) := by
      intro gs
      induction gs with
      | nil =>
        intro _ W ws _ hltW hagree
        refine ⟨[], rfl, ?_, fun t => Fin.elim0 t, ?_⟩
        · simpa using hltW
        · simpa using hagree
      | cons g gs ih =>
        intro hlegal W ws hlenW hltW hagree
        have hg := hlegal g List.mem_cons_self
        have hgs := fun g' hg' => hlegal g' (List.mem_cons_of_mem g hg')
        let nw := gateVal29 W g
        have hgetD_mem : ∀ q : ℕ, W.getD q 0 ∈ c0 ++ W := by
          intro q
          by_cases hq : q < W.length
          · exact List.mem_append_right c0 (by rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem ..)
          · rw [List.getD_eq_default _ _ (by omega)]
            exact List.mem_append_left W (by simp [c0])
        have hgetD_lt : ∀ q : ℕ, W.getD q 0 < 2 ^ 29 := by
          intro q
          by_cases hq : q < W.length
          · exact hltW _ (by rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem ..)
          · rw [List.getD_eq_default _ _ (by omega)]
            decide
        have hnw_lt : nw < 2 ^ 29 := by
          dsimp [nw, gateVal29]
          split_ifs
          · decide
          · decide
          · exact hgetD_lt _
          · exact Nat.lt_of_le_of_lt Nat.and_le_left (hgetD_lt _)
          · exact Nat.or_lt_two_pow (hgetD_lt _) (hgetD_lt _)
        have hnw_build : ∃ a ∈ c0 ++ W, ∃ b ∈ c0 ++ W, nw = (a &&& b) ∨ nw = (a ||| b) := by
          dsimp [nw, gateVal29]
          split_ifs
          · refine ⟨536870911, List.mem_append_left W (by simp [c0]),
              536870911, List.mem_append_left W (by simp [c0]), Or.inl rfl⟩
          · refine ⟨0, List.mem_append_left W (by simp [c0]),
              0, List.mem_append_left W (by simp [c0]), Or.inl rfl⟩
          · exact ⟨W.getD (g.inputs.getD 0 0) 0, hgetD_mem _,
              W.getD (g.inputs.getD 0 0) 0, hgetD_mem _, Or.inl (Nat.and_self _).symm⟩
          · exact ⟨W.getD (g.inputs.getD 0 0) 0, hgetD_mem _,
              W.getD (g.inputs.getD 1 0) 0, hgetD_mem _, Or.inl rfl⟩
          · exact ⟨W.getD (g.inputs.getD 0 0) 0, hgetD_mem _,
              W.getD (g.inputs.getD 1 0) 0, hgetD_mem _, Or.inr rfl⟩
        have hnw_bit : ∀ k : Fin 29,
            nw.testBit k.val = g.op.eval (g.inputs.map (fun q => (ws k).getD q false)) := by
          intro k
          have h511 : (536870911 : ℕ).testBit k.val = true := h511_all k
          have hk0 : (0 : ℕ).testBit k.val = false := Nat.zero_testBit k.val
          have hm : ∀ q : ℕ, (W.getD q 0).testBit k.val = (ws k).getD q false := hagree k
          have h_and0 : PEqualNP.CircuitLowerBounds.GateOp.and.eval [] = true := rfl
          have h_or0 : PEqualNP.CircuitLowerBounds.GateOp.or.eval [] = false := rfl
          have h_and1 (u : Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval [u] = u := by
            cases u <;> rfl
          have h_or1 (u : Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval [u] = u := by
            cases u <;> rfl
          have h_and2 (u v : Bool) :
              PEqualNP.CircuitLowerBounds.GateOp.and.eval [u, v] = (u && v) := by
            cases u <;> cases v <;> rfl
          have h_or2 (u v : Bool) :
              PEqualNP.CircuitLowerBounds.GateOp.or.eval [u, v] = (u || v) := by
            cases u <;> cases v <;> rfl
          rcases hlen0 : g.inputs with _ | ⟨a, rest1⟩
          · dsimp [nw, gateVal29]
            rw [hlen0]
            simp only [List.length_nil, ↓reduceIte, List.map_nil]
            rcases hg.1 with hop | hop
            · rw [hop, h_and0]
              simp only [↓reduceIte, h511]
            · rw [hop, h_or0]
              simp only [Bool.false_eq_true, ↓reduceIte, hk0]
          · rcases hlen1 : rest1 with _ | ⟨b, rest2⟩
            · dsimp [nw, gateVal29]
              rw [hlen0, hlen1]
              simp only [List.length_cons, List.length_nil, Nat.reduceEqDiff, ↓reduceIte,
                List.getD_cons_zero, List.map_cons, List.map_nil]
              rw [hm a]
              rcases hg.1 with hop | hop
              · rw [hop, h_and1]
              · rw [hop, h_or1]
            · have hrem : rest2 = [] := by
                have hl := hg.2
                rw [hlen0, hlen1] at hl
                simp only [List.length_cons] at hl
                have : rest2.length = 0 := by omega
                exact List.length_eq_zero_iff.mp this
              subst hrem
              dsimp [nw, gateVal29]
              rw [hlen0, hlen1]
              simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceEqDiff,
                ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
              rcases hg.1 with hop | hop
              · rw [hop, h_and2]
                change (W.getD a 0 &&& W.getD b 0).testBit k.val =
                  ((ws k).getD a false && (ws k).getD b false)
                rw [Nat.testBit_and, hm a, hm b]
              · rw [hop, h_or2]
                change (W.getD a 0 ||| W.getD b 0).testBit k.val =
                  ((ws k).getD a false || (ws k).getD b false)
                rw [Nat.testBit_or, hm a, hm b]
        have hltW' : ∀ x ∈ W ++ [nw], x < 2 ^ 29 := by
          intro x hx
          rcases List.mem_append.mp hx with hxW | hxnw
          · exact hltW x hxW
          · rw [List.mem_singleton.mp hxnw]
            exact hnw_lt
        let ws' : Fin 29 → List Bool := fun k => ws k ++ [g.op.eval (g.inputs.map (fun q => (ws k).getD q false))]
        have hlenW' : ∀ k : Fin 29, (W ++ [nw]).length = (ws' k).length := by
          intro k
          simp [ws', hlenW k]
        have hagree' : ∀ (k : Fin 29) (idx : ℕ), ((W ++ [nw]).getD idx 0).testBit k.val = (ws' k).getD idx false := by
          intro k idx
          by_cases hlt : idx < W.length
          · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by rw [← hlenW k]; exact hlt)]
            exact hagree k idx
          · by_cases heq : idx = W.length
            · subst heq
              have hw1 : (W ++ [nw]).getD W.length 0 = nw := by
                simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
              have hw2 : (ws' k).getD W.length false = g.op.eval (g.inputs.map (fun q => (ws k).getD q false)) := by
                dsimp [ws']
                simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlenW k]), hlenW k]
              rw [hw1, hw2]
              exact hnw_bit k
            · have h1 : (W ++ [nw]).getD idx 0 = 0 := List.getD_eq_default _ _ (by simp; omega)
              have h2 : (ws' k).getD idx false = false :=
                List.getD_eq_default _ _ (by dsimp [ws']; rw [List.length_append, List.length_singleton, ← hlenW k]; omega)
              rw [h1, h2, Nat.zero_testBit]
        obtain ⟨L', hLlen, hLlt, hLbuild, hLagree⟩ := ih hgs (W ++ [nw]) ws' hlenW' hltW' hagree'
        refine ⟨nw :: L', by simp [hLlen], ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using hLlt
        · intro t
          refine Fin.cases ?_ (fun t' => ?_) t
          · simpa [List.take_zero] using hnw_build
          · simpa [List.append_assoc, List.take_succ_cons] using hLbuild t'
        · intro k idx
          simpa [ws', List.foldl_cons, List.append_assoc] using hLagree k idx
    let ws0 : Fin 29 → List Bool := fun k => List.ofFn (rowIn k) ++ [!rowIn k 0, rowIn k i || rowIn k j]
    have hlen0 : ∀ k : Fin 29, init.length = (ws0 k).length := by
      intro k
      simp [ws0, hinit_len]
    obtain ⟨L, hLlen, hLlt, hLbuild, hLagree⟩ :=
      hstep_sim C.gates hnoNot init ws0 hlen0 hinit_lt hinit_bit
    let outVal := (init ++ L).getD C.output 0
    have hout_lt : outVal < 2 ^ 29 := by
      by_cases hco : C.output < (init ++ L).length
      · exact hLlt _ (by dsimp [outVal]; rw [List.getD_eq_getElem _ _ hco]; exact List.getElem_mem ..)
      · have : outVal = 0 := List.getD_eq_default _ _ (by omega)
        rw [this]
        decide
    have hout_mem : outVal ∈ c0 ++ init ++ L := by
      by_cases hco : C.output < (init ++ L).length
      · have hm : outVal ∈ init ++ L := by
          dsimp [outVal]; rw [List.getD_eq_getElem _ _ hco]; exact List.getElem_mem ..
        rw [List.append_assoc]
        exact List.mem_append_right c0 hm
      · have : outVal = 0 := List.getD_eq_default _ _ (by omega)
        rw [this]
        exact List.mem_append_left L (List.mem_append_left init (by simp [c0]))
    have hout_eq : outVal = 65535 := by
      apply Nat.eq_of_testBit_eq
      intro m
      by_cases hm : m < 29
      · let k : Fin 29 := ⟨m, hm⟩
        have ha := hLagree k C.output
        have heval : (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun q => w.getD q false))])
            (ws0 k)).getD C.output false = C.eval (ws0 k) := rfl
        rw [heval, hcomp (rowIn k)] at ha
        exact ha.trans (htarget_bit k).symm
      · have h1 : outVal.testBit m = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hout_lt (Nat.pow_le_pow_right (by omega) (by omega)))
        have h65 : (65535 : ℕ) < 2 ^ m :=
          lt_of_lt_of_le (by decide : 65535 < 2 ^ 29) (Nat.pow_le_pow_right (by omega) (by omega))
        have h2 : (65535 : ℕ).testBit m = false := Nat.testBit_eq_false_of_lt h65
        rw [h1, h2]
    have hLsz : L.length ≤ 13 := by
      change C.gates.length ≤ 13 at hsz
      omega
    have hseed_eq : c0 ++ init =
        [0, 536870911] ++ base ++ [33489407, base.getD i.val 0 ||| base.getD j.val 0] := by
      simp only [c0, init, List.append_assoc]
    have hforb := hZeroNot29 i j hrep L hLsz (by
      intro t
      rw [← hseed_eq]
      exact hLbuild t)
    rw [← hout_eq] at hforb
    apply hforb
    rw [← hseed_eq]
    exact hout_mem
  · have hnot_pos : 1 ≤ (C.gates.filter isNot).length := by omega
    have hcount_add : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
        (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        gs.countP (fun g => !(g.op.eval [false])) + (gs.filter isNot).length = gs.length := by
      intro gs
      induction gs with
      | nil => intro _; rfl
      | cons g gs ih =>
        intro hgs
        have hg := hgs g List.mem_cons_self
        have ih' := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
        rcases hg with ha | ho | hn
        · have h1 : (!(g.op.eval [false])) = true := by rw [ha]; rfl
          have h2 : isNot g = false := by dsimp [isNot]; rw [ha]
          have hc : (g :: gs).countP (fun g => !(g.op.eval [false])) =
              gs.countP (fun g => !(g.op.eval [false])) + 1 := by
            simp only [List.countP_cons, h1, ↓reduceIte]
          have hf : ((g :: gs).filter isNot).length = (gs.filter isNot).length := by
            simp only [List.filter_cons, h2, Bool.false_eq_true, ↓reduceIte]
          rw [List.length_cons]
          omega
        · have h1 : (!(g.op.eval [false])) = true := by rw [ho]; rfl
          have h2 : isNot g = false := by dsimp [isNot]; rw [ho]
          have hc : (g :: gs).countP (fun g => !(g.op.eval [false])) =
              gs.countP (fun g => !(g.op.eval [false])) + 1 := by
            simp only [List.countP_cons, h1, ↓reduceIte]
          have hf : ((g :: gs).filter isNot).length = (gs.filter isNot).length := by
            simp only [List.filter_cons, h2, Bool.false_eq_true, ↓reduceIte]
          rw [List.length_cons]
          omega
        · have h1 : (!(g.op.eval [false])) = false := by rw [hn]; rfl
          have h2 : isNot g = true := by dsimp [isNot]; rw [hn]
          have hc : (g :: gs).countP (fun g => !(g.op.eval [false])) =
              gs.countP (fun g => !(g.op.eval [false])) := by
            simp only [List.countP_cons, h1, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          have hf : ((g :: gs).filter isNot).length = (gs.filter isNot).length + 1 := by
            simp only [List.filter_cons, h2, ↓reduceIte, List.length_cons]
          rw [List.length_cons]
          omega
    have hCops : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro g hg
      exact (hfan g hg).1
    have hCsum := hcount_add C.gates hCops
    have hCcnt : C.gates.countP (fun g => !(g.op.eval [false])) ≤ 12 := by
      change C.gates.length ≤ 13 at hsz
      omega
    let C' : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [i.val, j.val]⟩] ++ C.gates, C.output⟩
    have hfan' : PEqualNP.MetaComplexity.FanInTwo C' := by
      intro g hg
      change g ∈ [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [i.val, j.val]⟩] ++ C.gates at hg
      rcases List.mem_append.mp hg with hpre | hrest
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpre
        rcases hpre with rfl | rfl <;> simp
      · exact hfan g hrest
    have hcnt' : C'.gates.countP (fun g => !(g.op.eval [false])) ≤ 13 := by
      dsimp only [C']
      rw [List.countP_append]
      have hpre : ([⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩,
          ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [i.val, j.val]⟩] :
            List PEqualNP.CircuitLowerBounds.Gate).countP (fun g => !(g.op.eval [false])) = 1 := rfl
      rw [hpre]
      omega
    have heval' : ∀ x : Fin 9 → Bool,
        C'.eval (List.ofFn x) = C.eval (List.ofFn x ++ [!x 0, x i || x j]) := by
      intro x
      change (C'.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun idx => w.getD idx false))])
        (List.ofFn x)).getD C'.output false =
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun idx => w.getD idx false))])
          (List.ofFn x ++ [!x 0, x i || x j])).getD C.output false
      dsimp only [C']
      rw [List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
      have h0 : (List.ofFn x).getD 0 false = x 0 := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        rfl
      have hstep1 : [0].map (fun idx => (List.ofFn x).getD idx false) = [x 0] := by
        simp only [List.map_cons, List.map_nil, h0]
      have hg1 : PEqualNP.CircuitLowerBounds.GateOp.not.eval
          ([0].map (fun idx => (List.ofFn x).getD idx false)) = !x 0 := by
        rw [hstep1]; rfl
      rw [hg1]
      have hi : ((List.ofFn x ++ [!x 0]).getD i.val false) = x i := by
        rw [List.getD_append _ _ _ _ (by simp [i.isLt]), List.getD_eq_getElem _ _ (by simp [i.isLt]),
          List.getElem_ofFn]
      have hj : ((List.ofFn x ++ [!x 0]).getD j.val false) = x j := by
        rw [List.getD_append _ _ _ _ (by simp [j.isLt]), List.getD_eq_getElem _ _ (by simp [j.isLt]),
          List.getElem_ofFn]
      have hstep2 : [i.val, j.val].map (fun idx => (List.ofFn x ++ [!x 0]).getD idx false) = [x i, x j] := by
        simp only [List.map_cons, List.map_nil, hi, hj]
      have hg2 : PEqualNP.CircuitLowerBounds.GateOp.or.eval
          ([i.val, j.val].map (fun idx => (List.ofFn x ++ [!x 0]).getD idx false)) = (x i || x j) := by
        rw [hstep2]
        cases x i <;> cases x j <;> rfl
      rw [hg2, List.append_assoc]
      rfl
    obtain ⟨S, hSlen, hSbuild, a, ha, u, heval⟩ :=
      hDeMorgan 9 512 C' (fun (v : Fin 9) (r : Fin 512) =>
        ([1, 2, 4, 8, 16, 32, 64, 128, 256] : List ℕ).getD v.val 0 &&& r.val != 0) hfan'
    obtain ⟨r, hr⟩ := hSignedAnd13 S (hSlen.trans hcnt') hSbuild a ha u
    have hmask : ∀ r : Fin 512,
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] :
          List (Fin 9 × Fin 9)).any (fun e =>
            (([1, 2, 4, 8, 16, 32, 64, 128, 256] : List ℕ).getD e.1.val 0 &&& r.val != 0) &&
            (([1, 2, 4, 8, 16, 32, 64, 128, 256] : List ℕ).getD e.2.val 0 &&& r.val != 0)) =
        ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ).any
          (fun e => r.val &&& e == e) := by
      decide +kernel
    apply hr
    rw [← heval r, heval', hcomp (fun v : Fin 9 =>
      ([1, 2, 4, 8, 16, 32, 64, 128, 256] : List ℕ).getD v.val 0 &&& r.val != 0), hmask r]
