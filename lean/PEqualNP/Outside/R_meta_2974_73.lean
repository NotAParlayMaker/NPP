import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2974_73
    (finite : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)), (∀ p p' l l' : Fin n, p ≠ p' → l ≠ l' → ¬((p,l) ∈ E ∧ (p',l) ∈ E ∧ (p,l') ∈ E ∧ (p',l') ∈ E)) → min (E.image Prod.fst).card (E.image Prod.snd).card ≤ 2256 → E.card ≤ 24 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1))
    (dense : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit) (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p t : Fin N, p ≠ t → ∃! l : Fin N, I p l ∧ I t l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      (∀ e ∈ E, I e.1 e.2 ∧
        PEqualNP.MetaComplexity.circuitFun (N + N) C
          (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i))
          e.1.val (N + e.2.val) = false ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N))
          e.1.val (N + e.2.val) = false) →
      2257 ≤ min (E.image Prod.fst).card (E.image Prod.snd).card →
      E.card ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size := by
  have cone : ∀ (N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (E : Finset (Fin N × Fin N)), PEqualNP.TopForm.IsAO2 (N+N) C → (∀ e ∈ E, PEqualNP.MetaComplexity.circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true) → (∀ v : Fin (N+N), PEqualNP.MetaComplexity.circuitFun (N+N) C (fun i => decide (i=v))=false) → (E.image Prod.fst).card + (E.image Prod.snd).card ≤ C.size+1 := by
    classical
    intro N C E hAO hacc hsingle
    let n := N + N
    let runW : List Gate → List Bool → List Bool := fun gs x =>
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
    have hrun_nil : ∀ x, runW [] x = x := fun _ => rfl
    have hrun_snoc : ∀ gs g x, runW (gs ++ [g]) x =
        runW gs x ++ [g.op.eval (g.inputs.map fun i => (runW gs x).getD i false)] := by
      intro gs g x
      simp [runW]
    have hrun_len : ∀ gs x, (runW gs x).length = x.length + gs.length := by
      intro gs x
      induction gs using List.reverseRecOn with
      | nil => simp [runW]
      | append_singleton gs g ih =>
        rw [hrun_snoc, List.length_append, List.length_singleton, ih,
          List.length_append, List.length_singleton]
        omega
    have hrun_prefix : ∀ g1 g2 x i, i < x.length + g1.length →
        (runW (g1 ++ g2) x).getD i false = (runW g1 x).getD i false := by
      intro g1 g2 x i hi
      induction g2 using List.reverseRecOn with
      | nil => simp
      | append_singleton g2 g ih =>
        rw [← List.append_assoc, hrun_snoc, List.getD_eq_getElem?_getD,
          List.getElem?_append_left]
        · rw [← List.getD_eq_getElem?_getD]
          exact ih
        · rw [hrun_len, List.length_append]
          omega
    have hrun_gate : ∀ gs x k (hk : k < gs.length),
        (runW gs x).getD (x.length + k) false =
          (gs[k]'hk).op.eval
            ((gs[k]'hk).inputs.map fun i => (runW (gs.take k) x).getD i false) := by
      intro gs x k hk
      have hsplit : gs = gs.take k ++ [gs[k]'hk] ++ gs.drop (k + 1) := by
        rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop,
          List.take_append_drop]
      conv_lhs => rw [hsplit]
      have hlenk : (gs.take k).length = k := List.length_take_of_le hk.le
      rw [hrun_prefix (gs.take k ++ [gs[k]'hk]) (gs.drop (k + 1)) x
        (x.length + k) (by simp; omega)]
      rw [hrun_snoc]
      have hlenw : (runW (gs.take k) x).length = x.length + k := by
        rw [hrun_len, hlenk]
      rw [← hlenw, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
      rfl
    have hread : ∀ k (hk : k < C.gates.length) i,
        i ∈ (C.gates[k]'hk).inputs → i < n + k := by
      intro k hk i hi
      have h := hAO.2.1 k hk i
      change i ∈ (C.gates.getD k ⟨GateOp.or, []⟩).inputs → i < n + k at h
      rw [List.getD_eq_getElem C.gates _ hk] at h
      exact h hi
    have htwo : ∀ k (hk : k < C.gates.length), (C.gates[k]'hk).inputs.length = 2 := by
      intro k hk
      exact hAO.2.2 _ (List.getElem_mem hk)
    let val : (Fin n → Bool) → ℕ → Bool := fun z w =>
      (runW C.gates (List.ofFn z)).getD w false
    have hval_input : ∀ z : Fin n → Bool, ∀ i (hi : i < n),
        val z i = z ⟨i, hi⟩ := by
      intro z i hi
      have hp := hrun_prefix [] C.gates (List.ofFn z) i (by simp; exact hi)
      change (runW C.gates (List.ofFn z)).getD i false = _
      rw [show C.gates = [] ++ C.gates from rfl, hp, hrun_nil]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi,
        ↓reduceDIte, Option.getD_some]
    have hval_gate : ∀ k (hk : k < C.gates.length) (z : Fin n → Bool),
        val z (n + k) = (C.gates[k]'hk).op.eval
          ((C.gates[k]'hk).inputs.map fun i => val z i) := by
      intro k hk z
      have hg := hrun_gate C.gates (List.ofFn z) k hk
      rw [List.length_ofFn] at hg
      change (runW C.gates (List.ofFn z)).getD (n + k) false = _
      rw [hg]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hp := hrun_prefix (C.gates.take k) (C.gates.drop k) (List.ofFn z) i
        (by rw [List.length_ofFn, List.length_take_of_le hk.le]; exact hread k hk i hi)
      rw [List.take_append_drop] at hp
      exact hp.symm
    have hdep : ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ,
        (∀ w ∈ W, w < n + k) →
        ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
          ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
            ∀ w ∈ W, val x w = val y w := by
      intro k
      induction k with
      | zero =>
        intro _ W hW
        refine ⟨Finset.univ.filter (fun i : Fin n => i.val ∈ W), ?_, ?_⟩
        · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
          apply Finset.card_le_card
          intro a ha
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
          exact (Finset.mem_filter.mp hi).2
        · intro x y h w hw
          have hw' : w < n := by have := hW w hw; omega
          rw [hval_input x w hw', hval_input y w hw']
          exact h ⟨w, hw'⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)
      | succ k ih =>
        intro hk W hW
        have hk' : k < C.gates.length := by omega
        by_cases hmem : n + k ∈ W
        · let W2 := W.erase (n + k) ∪ (C.gates[k]'hk').inputs.toFinset
          have hlt2 : ∀ w ∈ W2, w < n + k := by
            intro w hw
            rcases Finset.mem_union.mp hw with hw | hw
            · have h1 := hW w (Finset.mem_of_mem_erase hw)
              have h2 := Finset.ne_of_mem_erase hw
              omega
            · exact hread k hk' w (List.mem_toFinset.mp hw)
          have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
            intro w hw hne
            exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
          have hs2 : ∀ i ∈ (C.gates[k]'hk').inputs, i ∈ W2 := by
            intro i hi
            exact Finset.mem_union_right _ (List.mem_toFinset.mpr hi)
          have hc : W2.card + 1 ≤ W.card + 2 := by
            have h1 := Finset.card_union_le (W.erase (n + k))
              (C.gates[k]'hk').inputs.toFinset
            have h2 : (C.gates[k]'hk').inputs.toFinset.card ≤ 2 := by
              exact (List.toFinset_card_le _).trans (htwo k hk').le
            have h3 := Finset.card_erase_of_mem hmem
            have hpos : 0 < W.card := Finset.card_pos.mpr ⟨n + k, hmem⟩
            change W2.card ≤ (W.erase (n + k)).card +
              (C.gates[k]'hk').inputs.toFinset.card at h1
            omega
          obtain ⟨T, hT, hxy⟩ := ih (by omega) W2 hlt2
          refine ⟨T, by omega, ?_⟩
          intro x y h w hw
          by_cases hwk : w = n + k
          · rw [hwk, hval_gate k hk' x, hval_gate k hk' y]
            congr 1
            apply List.map_congr_left
            intro i hi
            exact hxy x y h i (hs2 i hi)
          · exact hxy x y h w (hs1 w hw hwk)
        · obtain ⟨T, hT, hxy⟩ := ih (by omega) W (by
            intro w hw
            have h1 := hW w hw
            have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
            omega)
          exact ⟨T, by omega, hxy⟩
    obtain ⟨T, hT, hxy⟩ : ∃ T : Finset (Fin n), T.card ≤ C.gates.length + 1 ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
          val x C.output = val y C.output := by
      by_cases ho : C.output < n + C.gates.length
      · obtain ⟨T, hT, hxy⟩ := hdep C.gates.length le_rfl {C.output}
          (by
            intro w hw
            rcases Finset.mem_singleton.mp hw with rfl
            exact ho)
        exact ⟨T, by simpa using hT, fun x y h => hxy x y h _ (by simp)⟩
      · refine ⟨∅, by simp, ?_⟩
        intro x y _
        have hx : (runW C.gates (List.ofFn x)).length ≤ C.output := by
          rw [hrun_len, List.length_ofFn]
          omega
        have hy : (runW C.gates (List.ofFn y)).length ≤ C.output := by
          rw [hrun_len, List.length_ofFn]
          omega
        change (runW C.gates (List.ofFn x)).getD C.output false =
          (runW C.gates (List.ofFn y)).getD C.output false
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hx,
          List.getD_eq_getElem?_getD, List.getElem?_eq_none hy]
    have hleft : ∀ e ∈ E, Fin.castAdd N e.1 ∈ T := by
      intro e he
      by_contra hnot
      have h := hxy
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2))
        (fun i => decide (i = Fin.natAdd N e.2)) (by
          intro i hi
          have hne : i ≠ Fin.castAdd N e.1 := fun h => hnot (h ▸ hi)
          simp only [hne, false_or])
      change circuitFun (N + N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) =
        circuitFun (N + N) C (fun i => decide (i = Fin.natAdd N e.2)) at h
      rw [hacc e he, hsingle (Fin.natAdd N e.2)] at h
      cases h
    have hright : ∀ e ∈ E, Fin.natAdd N e.2 ∈ T := by
      intro e he
      by_contra hnot
      have h := hxy
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2))
        (fun i => decide (i = Fin.castAdd N e.1)) (by
          intro i hi
          have hne : i ≠ Fin.natAdd N e.2 := fun h => hnot (h ▸ hi)
          simp only [hne, or_false])
      change circuitFun (N + N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) =
        circuitFun (N + N) C (fun i => decide (i = Fin.castAdd N e.1)) at h
      rw [hacc e he, hsingle (Fin.castAdd N e.1)] at h
      cases h
    let P := E.image Prod.fst
    let L := E.image Prod.snd
    let SP := P.image (Fin.castAdd N)
    let SL := L.image (Fin.natAdd N)
    have hSP : SP ⊆ T := by
      intro i hi
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
      exact hleft e he
    have hSL : SL ⊆ T := by
      intro i hi
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hl
      exact hright e he
    have hdisj : Disjoint SP SL := by
      rw [Finset.disjoint_left]
      intro i hp hl
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨l, _, heq⟩ := Finset.mem_image.mp hl
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      have := p.isLt
      omega
    have hSPcard : SP.card = P.card :=
      Finset.card_image_of_injective _ (Fin.castAdd_injective N N)
    have hSLcard : SL.card = L.card := by
      apply Finset.card_image_of_injective
      intro a b h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      exact Fin.ext (by omega)
    have hc := Finset.card_le_card (Finset.union_subset hSP hSL)
    rw [Finset.card_union_of_disjoint hdisj, hSPcard, hSLcard] at hc
    change P.card + L.card ≤ C.gates.length + 1
    exact hc.trans hT
  intro q N I inst C hq hN hcol huniq hao hsound
  let pair := fun (e : Fin N × Fin N) (i : Fin (N+N)) =>
    decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)
  let single := fun (v i : Fin (N+N)) => decide (i=v)
  let E : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
    I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C (pair e)=true ∧
    PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
    PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false
  have selected : ∀ e ∈ E, I e.1 e.2 ∧
      PEqualNP.MetaComplexity.circuitFun (N+N) C (pair e)=true ∧
      PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
      PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have separate (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro eq
    have := congrArg Fin.val eq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := p.isLt
    omega
  have off (v : Fin (N+N)) :
      PEqualNP.MetaComplexity.circuitFun (N+N) C (single v)=false := by
    apply hsound
    · rw [Fintype.card_subtype]
      apply Nat.le_trans (Finset.card_le_one.mpr ?_) (by omega)
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, single, decide_eq_true_eq] at ha hb
      exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (ha.trans hb.symm)))
    · rintro ⟨p,l,_,hp,hl⟩
      exact separate p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  rw [Fintype.card_subtype]
  change E.card ≤ 24*C.size
  by_cases small : min (E.image Prod.fst).card (E.image Prod.snd).card ≤ 2256
  · have rect : ∀ p p' l l' : Fin N, p≠p' → l≠l' →
        ¬((p,l)∈E ∧ (p',l)∈E ∧ (p,l')∈E ∧ (p',l')∈E) := by
      intro p p' l l' pp ll hh
      obtain ⟨_,_,unique⟩ := huniq p p' pp
      have first := unique l ⟨(selected _ hh.1).1, (selected _ hh.2.1).1⟩
      have second := unique l' ⟨(selected _ hh.2.2.1).1, (selected _ hh.2.2.2).1⟩
      exact ll (first.trans second.symm)
    have geometry := finite N E rect small
    have leaves := cone N C E hao (fun e he => (selected e he).2.1) off
    exact geometry.trans (Nat.mul_le_mul_left 24 (by omega))
  · exact dense q N I C E hq hN hcol huniq hao hsound selected (by omega)
