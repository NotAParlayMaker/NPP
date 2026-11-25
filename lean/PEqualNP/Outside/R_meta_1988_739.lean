import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves PEqualNP.HeptadCover PEqualNP.GenericRejection

-- An ordinary output may miss one flag. Otherwise both factors must have false positives,
-- and every dominated-wire bypass must destroy at least two flags.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 450000 in
theorem PEqualNP.Outside.R_meta_1988_739
    (single :
      let S := fun l : Fin 13 => Finset.univ.filter fun p : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      ∀ C : Circuit, Monotone2 C →
        ((incidences S).filter fun e => !C.eval (incidenceInput {e.1} {e.2})).card ≤ 1 →
        (∀ P L, C.eval (incidenceInput P L) = true → incidenceFun S P L = true) → 63 ≤ C.size)
    (pivotal :
      let S := fun l : Fin 13 => Finset.univ.filter fun p : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      ∀ (C : Circuit) (a b : ℕ), Monotone2 C →
        let W := fun k P L => (C.wires (incidenceInput P L)).getD k false
        let D : Circuit := ⟨C.gates ++ [⟨.and,[a,b]⟩], 26 + C.size⟩
        (∀ P L, (W a P L && W b P L) = incidenceFun S P L) →
        (∀ k ∈ [a,b], ∃ P L, W k P L = true ∧ incidenceFun S P L = false) →
        (∀ j < C.size, ∀ p, (p < 26 + j ∨ p = 26 + D.size + 1) →
          WireBelowOutput 26 ⟨D.gates, 26 + j⟩ p → let T := eraseGate 26 D j p
          2 ≤ ((incidences S).filter fun e => !T.eval (incidenceInput {e.1} {e.2})).card) → 63 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (63 : ℕ) ≤ x1.size := by

  have geometry (S : Finset (Fin 13)) (hS : 4 ≤ S.card) :
      (Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ S, ¬ ((p.val + l.val) % 13 ∈ [0,1,3,9]))).card ≤ 3 := by
    clear single pivotal
    let N (p : Fin 13) := Finset.univ.filter (fun l : Fin 13 => (p.val + l.val) % 13 ∈ [0,1,3,9])
    have degree : ∀ p, (N p).card = 4 := by unfold N; decide +kernel
    have pair : ∀ p q, p ≠ q → (N p ∩ N q).card ≤ 1 := by unfold N; decide +kernel
    obtain ⟨Q, hQS, hQ⟩ := Finset.exists_subset_card_eq hS
    obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := Finset.card_eq_four.mp hQ
    have subadd (X Y Z : Finset (Fin 13)) : ((X ∪ Y) ∩ Z).card ≤
        (X ∩ Z).card + (Y ∩ Z).card := by
      rw [Finset.union_inter_distrib_right]
      apply Finset.card_union_le
    let U := N a ∪ N b ∪ N c ∪ N d
    have size : 10 ≤ U.card := by
      have e1 := Finset.card_union_add_card_inter (N a) (N b)
      have e2 := Finset.card_union_add_card_inter (N a ∪ N b) (N c)
      have e3 := Finset.card_union_add_card_inter (N a ∪ N b ∪ N c) (N d)
      simp only [degree] at e1 e2 e3
      dsimp only [U]
      have := subadd (N a) (N b) (N c)
      have := subadd (N a) (N b) (N d)
      have := subadd (N a ∪ N b) (N c) (N d)
      have := pair a b hab
      have := pair a c hac
      have := pair a d had
      have := pair b c hbc
      have := pair b d hbd
      have := pair c d hcd
      omega
    have sub : Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ S, ¬ ((p.val+l.val)%13 ∈ [0,1,3,9])) ⊆ Uᶜ := by
      intro l hl
      have miss (p : Fin 13) (hp : p ∈ ({a,b,c,d} : Finset (Fin 13))) : l ∉ N p :=
        fun hn => (Finset.mem_filter.mp hl).2 p (hQS hp) (Finset.mem_filter.mp hn).2
      simp only [Finset.mem_compl, U, Finset.mem_union]
      exact fun h => h.elim (fun h => h.elim (fun h => h.elim (miss a (by simp)) (miss b (by simp)))
        (miss c (by simp))) (miss d (by simp))
    have h := Finset.card_le_card sub
    rw [Finset.card_compl, Fintype.card_fin] at h
    omega

  have bridge
      (hgeom : ∀ S : Finset (Fin 13), 4 ≤ S.card →
        (Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ S, ¬ ((p.val + l.val) % 13 ∈ [0,1,3,9]))).card ≤ 3)
      (C : Circuit) (outs : List ℕ) (hC : Monotone2 C)
      (htests : let inc := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
        let enc := fun (P L : Finset (Fin 13)) (i : Fin 26) =>
          if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P) else decide (Fin.ofNat 13 i.val ∈ L)
        let avoid := fun P : Finset (Fin 13) => Finset.univ.filter (fun l => ∀ p ∈ P, ¬ inc p l)
        let out := fun P L => GateOp.and.eval (outs.map fun k => (C.wires (List.ofFn (enc P L))).getD k false)
        (∀ p l, inc p l → out {p} {l} = true) ∧
          ∀ P, P.card ≤ 3 → out P (avoid P) = false ∧ out (avoid P) P = false) :
      let S := fun l : Fin 13 => Finset.univ.filter (fun p : Fin 13 =>
        (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ))
      ∀ P L, GateOp.and.eval (outs.map fun k => (C.wires (incidenceInput P L)).getD k false) =
        incidenceFun S P L := by
    clear single pivotal geometry
    have eval_and (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := rfl
    have eval_or (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := rfl
    let inc (p l : Fin 13) : Prop := (p.val + l.val) % 13 ∈ [0,1,3,9]
    let _ : DecidableRel inc := by intro p l; unfold inc; infer_instance
    let avoid (P : Finset (Fin 13)) : Finset (Fin 13) :=
      Finset.univ.filter (fun l => ∀ p ∈ P, ¬ inc p l)

    have inc_symm (p l : Fin 13) : inc p l ↔ inc l p := by
      simp only [inc, Nat.add_comm]

    have large_avoid (P : Finset (Fin 13)) (h : 4 ≤ P.card) : (avoid P).card ≤ 3 := by
      exact hgeom P h

    have no_edge_subsets (P L : Finset (Fin 13))
        (h : ¬ ∃ p ∈ P, ∃ l ∈ L, inc p l) : L ⊆ avoid P ∧ P ⊆ avoid L := by
      constructor
      · intro l hl
        simp only [avoid, Finset.mem_filter, Finset.mem_univ, true_and]
        intro p hp hi
        exact h ⟨p, hp, l, hl, hi⟩
      · intro p hp
        simp only [avoid, Finset.mem_filter, Finset.mem_univ, true_and]
        intro l hl hi
        exact h ⟨p, hp, l, hl, (inc_symm l p).mp hi⟩

    have tests_force_function
        (B : Finset (Fin 13) → Finset (Fin 13) → Bool)
        (hmono : ∀ P P' L L', P ⊆ P' → L ⊆ L' → B P L = true → B P' L' = true)
        (hpositive : ∀ p l, inc p l → B {p} {l} = true)
        (hnegative : ∀ S, S.card ≤ 3 → B S (avoid S) = false ∧ B (avoid S) S = false)
        (P L : Finset (Fin 13)) : B P L = true ↔ ∃ p ∈ P, ∃ l ∈ L, inc p l := by
      constructor
      · intro hB
        by_contra hn
        obtain ⟨hL, hP⟩ := no_edge_subsets P L hn
        by_cases hsmall : P.card ≤ 3
        · have hb := hmono P P L (avoid P) (Finset.Subset.refl _) hL hB
          rw [(hnegative P hsmall).1] at hb
          cases hb
        · have hlarge : 4 ≤ P.card := by omega
          have hsmallL : L.card ≤ 3 :=
            (Finset.card_le_card hL).trans (large_avoid P hlarge)
          have hb := hmono P (avoid L) L L hP (Finset.Subset.refl _) hB
          rw [(hnegative L hsmallL).2] at hb
          cases hb
      · rintro ⟨p, hp, l, hl, hi⟩
        exact hmono {p} P {l} L (Finset.singleton_subset_iff.mpr hp)
          (Finset.singleton_subset_iff.mpr hl) (hpositive p l hi)


    let encode (P L : Finset (Fin 13)) (i : Fin 26) : Bool :=
      if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P)
      else decide (Fin.ofNat 13 i.val ∈ L)

    let out (C : PEqualNP.CircuitLowerBounds.Circuit) (outs : List ℕ) (P L : Finset (Fin 13)) : Bool :=
      PEqualNP.CircuitLowerBounds.GateOp.and.eval (outs.map fun k => (C.wires (List.ofFn (encode P L))).getD k false)

    have encode_mono {P Q L M : Finset (Fin 13)} (hp : P ⊆ Q) (hl : L ⊆ M) :
        ∀ i, encode P L i = true → encode Q M i = true := by
      intro i hi
      unfold encode at hi ⊢
      split_ifs at hi ⊢ with h
      · exact decide_eq_true (hp (of_decide_eq_true hi))
      · exact decide_eq_true (hl (of_decide_eq_true hi))

    have getD_snoc (xs : List Bool) (a : Bool) (k : ℕ) :
        (xs ++ [a]).getD k false =
          if k < xs.length then xs.getD k false else if k = xs.length then a else false := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      split_ifs with h1 h2
      · rw [List.getElem?_append_left h1]
      · subst h2; simp
      · rw [List.getElem?_append_right (by omega)]
        rw [List.getElem?_eq_none (by simp; omega)]
        simp

    have wires_mono (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (xs ys : List Bool)
        (hlen : xs.length = ys.length)
        (hxy : ∀ k, xs.getD k false = true → ys.getD k false = true) :
        ∀ k, (C.wires xs).getD k false = true → (C.wires ys).getD k false = true := by
      obtain ⟨gs, o⟩ := C
      unfold PEqualNP.CircuitLowerBounds.Circuit.wires
      induction gs generalizing xs ys with
      | nil => simpa using hxy
      | cons g gs ih =>
        simp only [List.foldl_cons]
        apply ih
        · simpa only [List.length_append, List.length_singleton] using congrArg (fun n => n + 1) hlen
        · intro k hk
          simp only [getD_snoc, hlen] at hk ⊢
          split_ifs at hk ⊢ with h1 h2
          · exact hxy k hk
          · have hop := (hC g List.mem_cons_self).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with hop | hop
            · simp only [hop, eval_and, List.all_map, Function.comp_apply, id,
                List.all_eq_true] at hk ⊢
              exact fun j hj => hxy j (hk j hj)
            · simp only [hop, eval_or, List.any_map, Function.comp_apply, id,
                List.any_eq_true] at hk ⊢
              obtain ⟨j, hj, hjv⟩ := hk
              exact ⟨j, hj, hxy j hjv⟩
        · intro g' hg'
          exact hC g' (List.mem_cons_of_mem _ hg')

    have out_mono (C : PEqualNP.CircuitLowerBounds.Circuit) (outs : List ℕ) (hC : PEqualNP.MetaComplexity.Monotone2 C)
        {P Q L M : Finset (Fin 13)} (hp : P ⊆ Q) (hl : L ⊆ M) :
        out C outs P L = true → out C outs Q M = true := by
      intro h
      have hm := wires_mono C hC (List.ofFn (encode P L)) (List.ofFn (encode Q M))
        (by simp) (by
          intro k hk
          by_cases hkn : k < 26
          · rw [List.getD_eq_getElem _ _ (by simpa using hkn)] at hk ⊢
            simp only [List.getElem_ofFn] at hk ⊢
            exact encode_mono hp hl ⟨k, hkn⟩ hk
          · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hkn)] at hk
            cases hk)
      simp only [out, eval_and, List.all_map, Function.comp_apply, id, List.all_eq_true] at h ⊢
      exact fun k hk => hm k (h k hk)

    have circuit_tests_force_function (C : PEqualNP.CircuitLowerBounds.Circuit) (outs : List ℕ) (hC : PEqualNP.MetaComplexity.Monotone2 C)
        (hpositive : ∀ p l, inc p l → out C outs {p} {l} = true)
        (hnegative : ∀ S, S.card ≤ 3 →
          out C outs S (avoid S) = false ∧ out C outs (avoid S) S = false) :
        ∀ P L, out C outs P L = true ↔ ∃ p ∈ P, ∃ l ∈ L, inc p l := by
      exact tests_force_function (out C outs)
        (fun _ _ _ _ hp hl => out_mono C outs hC hp hl) hpositive hnegative

    change (∀ p l, inc p l → out C outs {p} {l} = true) ∧
      (∀ S, S.card ≤ 3 → out C outs S (avoid S) = false ∧ out C outs (avoid S) S = false) at htests
    have encode_input (P L : Finset (Fin 13)) : List.ofFn (encode P L) = incidenceInput P L := by
      delta incidenceInput
      rw [List.ofFn_add (n := 13) (m := 13)]
      apply congrArg₂ List.append
      · apply congrArg List.ofFn
        funext i
        simp [encode, i.isLt]
      · apply congrArg List.ofFn
        funext i
        have hi : ∀ j : Fin 13, ¬(j.natAdd 13).val < 13 ∧ Fin.ofNat 13 (j.natAdd 13).val = j := by decide
        simp only [encode, ite_eq_right (hi i).1, (hi i).2]
    intro S P L
    dsimp only [S]
    rw [← encode_input P L]
    apply Bool.eq_iff_iff.mpr
    delta incidenceFun
    simpa only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and]
      using circuit_tests_force_function C outs hC htests.1 htests.2 P L

  have bypassSem (n : ℕ) (C : Circuit) (hM : Monotone2 C) (j p : ℕ)
      (hj : j < C.gates.length) (hwidth : p < n + j ∨ n + C.size ≤ p) (x : Fin n → Bool)
      (hdom : (C.wires (List.ofFn x)).getD p false = true →
        (C.wires (List.ofFn x)).getD (n + j) false = true) :
      let D := eraseGate n C j p
      (D.eval (List.ofFn x) = true → C.eval (List.ofFn x) = true) ∧
        ((C.wires (List.ofFn x)).getD p false = (C.wires (List.ofFn x)).getD (n + j) false →
          D.eval (List.ofFn x) = C.eval (List.ofFn x)) := by
    clear single pivotal geometry bridge
    let y := List.ofFn x
    let red := eraseRedirect n j p
    let ren (g : Gate) : Gate := ⟨g.op, g.inputs.map red⟩
    let val (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun r => w.getD r false)
    let step (w : List Bool) (g : Gate) := w ++ [val w g]
    let D := eraseGate n C j p
    let z := (C.wires y).getD p false = (C.wires y).getD (n + j) false
    -- Reverse simulation also holds when the replacement agrees with the removed wire.
    let R (a b : Bool) := (a = true → b = true) ∧ (z → b = true → a = true)
    have reflR (a : Bool) : R a a := ⟨id, fun _ => id⟩
    have runPrefix (gs : List Gate) (w : List Bool) :
        ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
      induction gs generalizing w with
      | nil => exact ⟨[], by simp⟩
      | cons g gs ih =>
        obtain ⟨t, ht, hl⟩ := ih (step w g)
        refine ⟨val w g :: t, ?_, by simp [hl]⟩
        rw [List.foldl_cons, ht]
        simp [step]
    have snoc (w : List Bool) (b : Bool) (r : ℕ) :
        (w ++ [b]).getD r false = if r = w.length then b else w.getD r false := by
      rcases lt_trichotomy r w.length with h | h | h
      · rw [ite_eq_right (by omega), List.getD_append _ _ _ _ h]
      · subst r; simp [List.getD_eq_getElem?_getD]
      · rw [ite_eq_right (by omega)]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    have gateMono (g : Gate) (f f' : ℕ → Bool) (hm : g.op = GateOp.and ∨ g.op = GateOp.or)
        (hf : ∀ r, f r = true → f' r = true) :
        g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
      rcases hm with ha | ho
      · have hand (φ : ℕ → Bool) : g.op.eval (g.inputs.map φ) = true ↔
            ∀ r ∈ g.inputs, φ r = true := by
          rw [ha]
          change (g.inputs.map φ).all id = true ↔ _
          simp
        rw [hand, hand]
        exact fun h r hr => hf r (h r hr)
      · have hor (φ : ℕ → Bool) : g.op.eval (g.inputs.map φ) = true ↔
            ∃ r ∈ g.inputs, φ r = true := by
          rw [ho]
          change (g.inputs.map φ).any id = true ↔ _
          simp
        rw [hor, hor]
        rintro ⟨r, hr, hv⟩
        exact ⟨r, hr, hf r hv⟩
    have sim (gs : List Gate) (U V : List Bool) (hk : n + j ≤ U.length)
        (hl : V.length = U.length + 1) (hp : p < n + j ∨ U.length + gs.length < p)
        (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
        (hr : ∀ i, R (U.getD (red i) false) (V.getD i false)) :
        ∀ i, R (((gs.map ren).foldl step U).getD (red i) false)
          ((gs.foldl step V).getD i false) := by
      induction gs generalizing U V with
      | nil => exact hr
      | cons g gs ih =>
        simp only [List.length_cons] at hp
        simp only [List.map_cons, List.foldl_cons]
        apply ih (step U (ren g)) (step V g) (by simp [step]; omega)
          (by simp [step, hl]) (by simp [step]; omega)
          (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
        intro i
        have hi : red i = U.length ↔ i = V.length := by
          change (if i = n+j then p else if n+j < i then i-1 else i) = U.length ↔ _
          split_ifs <;> omega
        simp only [step, snoc]
        by_cases he : i = V.length
        · rw [ite_eq_left (hi.mpr he), ite_eq_left he]
          change R (g.op.eval ((g.inputs.map red).map fun r => U.getD r false))
            (g.op.eval (g.inputs.map fun r => V.getD r false))
          rw [List.map_map]
          have hg := hm g (List.mem_cons_self ..)
          exact ⟨gateMono g _ _ hg (fun r => (hr r).1),
            fun hz => gateMono g _ _ hg (fun r => (hr r).2 hz)⟩
        · rw [ite_eq_right (fun h => he (hi.mp h)), ite_eq_right he]
          exact hr i
    let A := (C.gates.take j).foldl step y
    let b := val A C.gates[j]
    let rest := C.gates.drop (j + 1)
    have hA : A.length = n + j := by
      obtain ⟨t, ht, htl⟩ := runPrefix (C.gates.take j) y
      change ((C.gates.take j).foldl step y).length = _
      rw [ht, List.length_append, htl, List.length_take]
      simp [y, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
      rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
    have hW : C.wires y = rest.foldl step (A ++ [b]) := by
      change C.gates.foldl step y = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hD : D.wires y = (rest.map ren).foldl step A := by
      change D.gates.foldl step y = _
      dsimp only [D]
      delta eraseGate
      simp only [ite_eq_left hj, List.foldl_append]; rfl
    have hOut : D.output = red C.output := by
      dsimp only [D]
      delta eraseGate
      simp [hj, red]
    have hrest : rest.length = C.gates.length - (j+1) := List.length_drop
    change p < n + j ∨ n + C.gates.length ≤ p at hwidth
    obtain ⟨t, ht, htl⟩ := runPrefix rest (A ++ [b])
    have hgate : (C.wires y).getD (n+j) false = b := by
      rw [hW, ht, List.getD_append _ _ _ _ (by simp [hA]), snoc, ite_eq_left hA.symm]
    have hpval : (C.wires y).getD p false = A.getD p false := by
      rw [hW, ht]
      rcases hwidth with h | h
      · rw [List.getD_append _ _ _ _ (by simp [hA]; omega),
            List.getD_append _ _ _ _ (by omega)]
      · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega),
            List.getD_eq_default _ _ (by omega)]
    have hsim := sim rest A (A ++ [b]) (by omega) (by simp)
      (by omega) (fun g hg => (hM g (List.mem_of_mem_drop hg)).1) (by
        intro i
        rw [snoc]
        by_cases he : i = n + j
        · have hr : red i = p := by dsimp only [red]; delta eraseRedirect; simp [he]
          rw [hr, ite_eq_left (he.trans hA.symm), ← hpval, ← hgate]
          exact ⟨hdom, fun hz hv => hz.trans hv⟩
        · rw [ite_eq_right (fun e => he (e.trans hA))]
          by_cases hlt : n + j < i
          · have hr : red i = i - 1 := by dsimp only [red]; delta eraseRedirect; simp [he, hlt]
            rw [hr, List.getD_eq_default _ _ (show A.length ≤ i - 1 by omega),
              List.getD_eq_default _ _ (show A.length ≤ i by omega)]
            exact reflR false
          · have hr : red i = i := by dsimp only [red]; delta eraseRedirect; simp [he, hlt]
            rw [hr]; exact reflR _)
    have result : R (D.eval y) (C.eval y) := by
      unfold Circuit.eval
      rw [hOut, hD, hW]
      exact hsim C.output
    change (D.eval y = true → C.eval y = true) ∧ (z → D.eval y = C.eval y)
    refine ⟨result.1, fun hz => ?_⟩
    exact Bool.eq_iff_iff.mpr ⟨result.1, result.2 hz⟩

  have accounting (n : ℕ) (C : Circuit) (pins : List ℕ) (hC : Monotone2 C) (hpins : pins.length ≤ 2) :
      let D : Circuit := ⟨C.gates ++ [⟨.and, pins⟩], n + C.gates.length⟩
      Monotone2 D ∧ D.size = C.size + 1 ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = GateOp.and.eval
        (pins.map fun k => (C.wires (List.ofFn x)).getD k false)) ∧
      (∀ j p : ℕ, j < C.gates.length →
        let E := eraseGate n D j p
        Monotone2 E ∧ E.size = C.size) := by
    clear single pivotal geometry bridge bypassSem
    let D : Circuit := ⟨C.gates ++ [⟨.and, pins⟩], n + C.gates.length⟩
    have hDmono : Monotone2 D := by
      intro g hg
      change g ∈ C.gates ++ [⟨.and, pins⟩] at hg
      rcases List.mem_append.mp hg with hc | ha
      · exact hC g hc
      · obtain rfl := List.mem_singleton.mp ha
        exact ⟨by simp, hpins⟩
    have hDsize : D.size = C.size + 1 := by delta Circuit.size; simp [D]
    have hDeval (x : Fin n → Bool) : D.eval (List.ofFn x) = GateOp.and.eval
        (pins.map fun k => (C.wires (List.ofFn x)).getD k false) := by
      let step := fun (w : List Bool) (g : Gate) =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have hlen (gs : List Gate) (w : List Bool) :
          (gs.foldl step w).length = w.length + gs.length := by
        induction gs generalizing w with
        | nil => simp
        | cons g gs ih =>
          rw [List.foldl_cons, ih]
          simp [step, Nat.add_comm, Nat.add_left_comm]
      let w := C.wires (List.ofFn x)
      have hw : w.length = n + C.gates.length := by
        change (C.gates.foldl step (List.ofFn x)).length = _
        simpa only [List.length_ofFn] using hlen C.gates (List.ofFn x)
      change ((C.gates ++ [(⟨.and, pins⟩ : Gate)]).foldl step (List.ofFn x)).getD
        (n + C.gates.length) false = _
      rw [List.foldl_append]
      change (w ++ [GateOp.and.eval (pins.map fun k => w.getD k false)]).getD
        (n + C.gates.length) false = _
      rw [List.getD_eq_getElem?_getD, ← hw, List.getElem?_concat_length] <;> rfl
    have hE (j p : ℕ) (hj : j < C.gates.length) :
        Monotone2 (eraseGate n D j p) ∧ (eraseGate n D j p).size = C.size := by
      have hlen : D.gates.length = C.gates.length + 1 := hDsize
      have hjD : j < D.gates.length := by omega
      constructor
      · intro g hg
        delta eraseGate at hg
        simp only [ite_eq_left hjD, List.mem_append, List.mem_map] at hg
        rcases hg with hg | ⟨g', hg', rfl⟩
        · exact hDmono g (List.mem_of_mem_take hg)
        · obtain ⟨hop, hfan⟩ := hDmono g' (List.mem_of_mem_drop hg')
          exact ⟨hop, by simpa only [List.length_map] using hfan⟩
      · delta Circuit.size eraseGate
        simp only [ite_eq_left hjD, List.length_append, List.length_take,
          List.length_map, List.length_drop, Nat.min_eq_left (Nat.le_of_lt hjD)]
        omega
    exact ⟨hDmono, hDsize, hDeval, hE⟩

  have word (P L : Finset (Fin 13)) : ∃ x : Fin 26 → Bool, List.ofFn x = incidenceInput P L := by
    clear single pivotal geometry bridge bypassSem accounting
    let w := incidenceInput P L
    have h : w.length = 26 := by dsimp only [w]; delta incidenceInput; simp
    refine ⟨fun i => w.get (Fin.cast h.symm i), ?_⟩
    change List.ofFn _ = w
    apply List.ext_getElem (by rw [List.length_ofFn,h])
    intro i hi hj
    rw [List.getElem_ofFn]
    rfl

  intro C pins hm hlen htests
  let S := fun l : Fin 13 => Finset.univ.filter fun p : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let D : Circuit := ⟨C.gates ++ [⟨.and,pins⟩], 26 + C.size⟩
  let W := fun k (P L : Finset (Fin 13)) => (C.wires (incidenceInput P L)).getD k false
  have hrows (P L : Finset (Fin 13)) : GateOp.and.eval (pins.map fun k => W k P L) = incidenceFun S P L :=
    bridge geometry C pins hm htests P L
  obtain ⟨hDm,hDs,heval,hcount⟩ := accounting 26 C pins hm hlen
  change D.size = C.size + 1 at hDs
  have hd (P L : Finset (Fin 13)) : D.eval (incidenceInput P L) = incidenceFun S P L := by
    obtain ⟨x,hx⟩ := word P L
    rw [← hx]
    exact (heval x).trans (by rw [hx]; exact hrows P L)
  have ht (j : ℕ) (hj : j < C.size) (p : ℕ) (hp : p < 26+j ∨ p = 26+D.size+1)
      (hdom : WireBelowOutput 26 ⟨D.gates,26+j⟩ p) :
      let T := eraseGate 26 D j p
      Monotone2 T ∧ T.size = C.size ∧ ∀ P L : Finset (Fin 13), T.eval (incidenceInput P L) = true → D.eval (incidenceInput P L) = true := by
    obtain ⟨hM,hSize⟩ := hcount j p hj
    refine ⟨hM,hSize,?_⟩
    intro P L
    obtain ⟨x,hx⟩ := word P L
    rw [← hx]
    have hj' : j < D.gates.length := Nat.lt_trans hj (show C.size < D.size by rw [hDs]; omega)
    exact (bypassSem 26 D hDm j p hj' (by omega) x (hdom x)).1
  clear geometry bridge bypassSem accounting word hDm hDs heval hcount htests
  classical
  let lost (B : Circuit) := ((incidences S).filter fun e => !B.eval (incidenceInput {e.1} {e.2})).card
  let trim j p := eraseGate 26 D j p
  by_cases hirr : ∀ j < C.size, ∀ p, (p < 26 + j ∨ p = 26 + D.size + 1) →
      WireBelowOutput 26 ⟨D.gates, 26 + j⟩ p → 2 ≤ lost (trim j p)
  · have hpos (e : Fin 13 × Fin 13) (he : e ∈ incidences S) : incidenceFun S {e.1} {e.2} = true := by
      have hs : e.1 ∈ S e.2 := (Finset.mem_filter.mp he).2
      delta incidenceFun
      simpa using hs
    have positives (k : ℕ) (hk : k ∈ pins) (e : Fin 13 × Fin 13) (he : e ∈ incidences S) : W k {e.1} {e.2} = true := by
      have h := (hrows {e.1} {e.2}).trans (hpos e he)
      change (pins.map fun i => W i {e.1} {e.2}).all id = true at h
      exact List.all_eq_true.mp h _ (List.mem_map.mpr ⟨k,hk,rfl⟩)
    by_cases hex : ∀ k ∈ pins, ∃ P L, W k P L = true ∧ incidenceFun S P L = false
    · cases pins with
      | nil =>
        have h := hrows ∅ ∅
        change true = incidenceFun S ∅ ∅ at h
        delta incidenceFun at h
        simp at h
      | cons a tail =>
        cases tail with
        | nil =>
          obtain ⟨P,L,ha,hn⟩ := hex a (by simp)
          have h := hrows P L
          change (W a P L && true) = _ at h
          simp [ha,hn] at h
        | cons b rest =>
          cases rest with
          | nil =>
            refine pivotal C a b hm ?_ hex hirr
            intro P L
            have h := hrows P L
            change (W a P L && (W b P L && true)) = _ at h
            simpa only [Bool.and_true] using h
          | cons c cs => simp at hlen
    · push Not at hex
      obtain ⟨k,hk,hkfalse⟩ := hex
      let B : Circuit := ⟨C.gates,k⟩
      apply single B hm
      · have hz : ((incidences S).filter fun e => !B.eval (incidenceInput {e.1} {e.2})) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro e he
          obtain ⟨hm',hv⟩ := Finset.mem_filter.mp he
          change (!W k {e.1} {e.2}) = true at hv
          rw [positives k hk e hm'] at hv
          contradiction
        rw [hz]; decide
      · intro P L hv
        exact Bool.eq_true_of_not_eq_false (hkfalse P L hv)
  · push Not at hirr
    obtain ⟨j,hj,p,hp,hdom,hl⟩ := hirr
    obtain ⟨hm',hs,hsound⟩ := ht j hj p hp hdom
    have h := single (trim j p) hm' (by change lost (trim j p) ≤ 1; omega) (fun P L h => (hd P L).symm.trans (hsound P L h))
    exact hs ▸ h
