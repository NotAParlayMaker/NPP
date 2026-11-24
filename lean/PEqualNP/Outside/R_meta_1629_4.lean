import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1629_4 (h1 : ∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k) (h2 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → 2 * N ≤ C.size + 1) (h3 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) M ∧ (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, (M.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∧ M.size ≤ 14 * C.size + 4 * N ∧ ∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (N + N) M z = PEqualNP.MetaComplexity.circuitFun (N + N) C z) : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * q ≤ 100 * C.size := by
  have h4 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C := by
      intro n C0 hC
      classical
      have hevA : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.and l = l.all id := fun _ => rfl
      have hevO : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or l = l.any id := fun _ => rfl
      let fx : ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun j g =>
        if g.op = PEqualNP.CircuitLowerBounds.GateOp.and then (if ∀ i ∈ g.inputs, i < n + j then g else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
        else ⟨g.op, g.inputs.filter (fun i => decide (i < n + j))⟩
      have hfx_eval : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), w.length = n + j → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
          (fx j g).op.eval ((fx j g).inputs.map fun i => w.getD i false) = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        intro j g w hw hop
        have hfw : ∀ i, n + j ≤ i → w.getD i false = false := by
          intro i hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          rfl
        rcases hop with hop | hop
        · by_cases hall : ∀ i ∈ g.inputs, i < n + j
          · simp only [fx, hop, if_pos hall, ite_true]
          · simp only [fx, hop, if_neg hall, ite_true]
            push_neg at hall
            obtain ⟨i, hi, hge⟩ := hall
            simp only [hevA, hevO, List.map_nil, List.any_nil]
            symm
            rw [List.all_eq_false]
            exact ⟨false, List.mem_map.mpr ⟨i, hi, hfw i hge⟩, by simp⟩
        · have hne : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and := by rw [hop]; intro h; cases h
          simp only [fx, if_neg hne, hop, hevO]
          rw [Bool.eq_iff_iff]
          simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id]
          constructor
          · rintro ⟨b, ⟨i, ⟨hi, _⟩, rfl⟩, hb⟩
            exact ⟨_, ⟨i, hi, rfl⟩, hb⟩
          · rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
            by_cases hlt : i < n + j
            · exact ⟨_, ⟨i, ⟨hi, hlt⟩, rfl⟩, hb⟩
            · rw [hfw i (by omega)] at hb
              exact absurd hb (by simp)
      have hop : ∀ g ∈ C0.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
        intro g hg
        have := (hC g hg).1
        simpa using this
      have key : ∀ G : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ G, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ x : List Bool, x.length = n →
          (G.mapIdx fx).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
            = G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x ∧
          (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length = n + G.length := by
        intro G
        induction G using List.reverseRecOn with
        | nil => intro _ x hx; simp [hx]
        | append_singleton G g ih =>
          intro hG x hx
          obtain ⟨ih1, ih2⟩ := ih (fun g' hg' => hG g' (List.mem_append_left _ hg')) x hx
          have hg := hG g (by simp)
          rw [List.mapIdx_append, List.foldl_append, List.foldl_append, ih1]
          simp only [List.mapIdx_cons, List.mapIdx_nil, List.foldl_cons, List.foldl_nil, zero_add]
          refine ⟨?_, by rw [List.length_append, ih2]; simp; omega⟩
          rw [hfx_eval G.length g _ ih2 hg]
      refine ⟨⟨C0.gates.mapIdx fx, C0.output⟩, ?_, ?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp hg
        have hm := hC _ (List.getElem_mem hj)
        have ho := hop _ (List.getElem_mem hj)
        by_cases ha : (C0.gates[j]).op = PEqualNP.CircuitLowerBounds.GateOp.and
        · by_cases hall : ∀ i ∈ (C0.gates[j]).inputs, i < n + j
          · simp only [fx, ha, if_pos hall, ite_true]
            exact ⟨by simp, hm.2⟩
          · simp only [fx, ha, if_neg hall, ite_true]
            exact ⟨by simp, by simp⟩
        · simp only [fx, if_neg ha]
          exact ⟨hm.1, le_trans (List.length_filter_le _ _) hm.2⟩
      · intro j hj i hi
        simp only [List.length_mapIdx] at hj
        have hgd : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨C0.gates.mapIdx fx, C0.output⟩ j = fx j (C0.gates[j]) := by
          show (C0.gates.mapIdx fx).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = fx j (C0.gates[j])
          simp [List.getD_eq_getElem?_getD, hj]
        rw [hgd] at hi
        by_cases ha : (C0.gates[j]).op = PEqualNP.CircuitLowerBounds.GateOp.and
        · by_cases hall : ∀ i ∈ (C0.gates[j]).inputs, i < n + j
          · simp only [fx, ha, if_pos hall, ite_true] at hi
            exact hall i hi
          · simp only [fx, ha, if_neg hall, ite_true] at hi
            simp at hi
        · simp only [fx, if_neg ha, List.mem_filter, decide_eq_true_eq] at hi
          exact hi.2
      · show (C0.gates.mapIdx fx).length ≤ C0.gates.length
        simp
      · funext x
        show ((C0.gates.mapIdx fx).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C0.output false = (C0.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C0.output false
        rw [(key C0.gates hop (List.ofFn x) (by simp)).1]
  intro q N I _ C hq hN hline huniq hmono hacc hsound
  have hlin := h2 q N I C hq hN hline huniq hmono hacc hsound
  obtain ⟨D, hDm, hDr, hDs, hDf⟩ := h4 (N + N) C hmono
  obtain ⟨M, hMm, hMr, hMx, hMs0, hMa0⟩ := h3 q N I D hq hN hline huniq hDm hDr
    (fun p l h => by rw [hDf]; exact hacc p l h) (fun z hz hn => by rw [hDf]; exact hsound z hz hn)
  have hMa : ∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (N + N) M z = PEqualNP.MetaComplexity.circuitFun (N + N) C z :=
    fun z hz => (hMa0 z hz).trans (congrFun hDf z)
  have hMs : M.size ≤ 14 * C.size + 4 * N := by omega
  have hL : ∀ i j : Fin N, i ≠ j → ((Finset.univ.filter (fun p => I p i)) ∩ (Finset.univ.filter (fun p => I p j))).card ≤ 1 := by
    intro i j hij
    by_contra hc
    rw [not_le] at hc
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨l, _, hl⟩ := huniq a b hab
    exact hij ((hl i ⟨ha.1, hb.1⟩).trans (hl j ⟨ha.2, hb.2⟩).symm)
  have hX : Set.ncard {j : ℕ | j < M.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, 0 < (M.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0} ≤ 0 := by
    apply Nat.le_of_eq
    convert Set.ncard_empty ℕ using 2
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hj, hop, hlen, hpos⟩
    obtain ⟨i, hi, h0⟩ := hMx j hj hop hlen
    have := hpos i hi
    omega
  have hS : ∀ (x : Fin N → Bool) (Y : Finset (Fin N)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (N + N) M (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ Finset.univ.filter (fun p => I p j), x p = true := by
    intro x Y hY hM
    by_contra hno
    have hset : Finset.univ.filter (fun l : Fin N => (Fin.append x (fun l => decide (l ∈ Y)) : Fin (N + N) → Bool) (Fin.natAdd N l) = true) = Y := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.append_right, decide_eq_true_eq]
    have hcard : (Finset.univ.filter (fun l : Fin N => (Fin.append x (fun l => decide (l ∈ Y)) : Fin (N + N) → Bool) (Fin.natAdd N l) = true)).card ≤ 1 := by
      rw [hset]
      exact hY
    rw [hMa _ hcard] at hM
    have hC := hsound _ (le_trans hcard (by omega)) (by
      rintro ⟨p, l, hI, hp, hl⟩
      apply hno
      simp only [Fin.append_left, Fin.append_right, decide_eq_true_eq] at hp hl
      exact ⟨l, hl, p, by simp [hI], hp⟩)
    rw [hC] at hM
    exact Bool.false_ne_true hM
  have hA : ∀ e : Fin N × Fin N, I e.1 e.2 → PEqualNP.MetaComplexity.circuitFun (N + N) M (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true := by
    rintro ⟨p, l⟩ hI
    have hz : (Fin.append (fun i => decide (i = p)) (fun l' => decide (l' = l)) : Fin (N + N) → Bool) = fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l) := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left, decide_eq_decide]
        constructor
        · intro h
          exact Or.inl (by rw [h])
        · rintro (h | h)
          · exact Fin.castAdd_injective N N h
          · have hi := i.isLt
            have := congrArg Fin.val h
            simp only [Fin.val_castAdd, Fin.val_natAdd] at this
            omega
      · rw [Fin.append_right, decide_eq_decide]
        constructor
        · intro h
          exact Or.inr (by rw [h])
        · rintro (h | h)
          · have hp := p.isLt
            have := congrArg Fin.val h
            simp only [Fin.val_castAdd, Fin.val_natAdd] at this
            omega
          · exact Fin.natAdd_injective N N h
    have hcard : (Finset.univ.filter (fun l' : Fin N => (Fin.append (fun i => decide (i = p)) (fun l' => decide (l' = l)) : Fin (N + N) → Bool) (Fin.natAdd N l') = true)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.append_right, decide_eq_true_eq] at ha hb
      rw [ha, hb]
    show PEqualNP.MetaComplexity.circuitFun (N + N) M (Fin.append (fun i => decide (i = p)) (fun l' => decide (l' = l))) = true
    rw [hMa _ hcard, hz]
    exact hacc p l hI
  have hK := h1 N N M.size 0 (fun j => Finset.univ.filter (fun p => I p j)) M hL hMm hMr le_rfl hX hS
  have hset : (Finset.univ.filter (fun e : Fin N × Fin N => e.1 ∈ Finset.univ.filter (fun p => I p e.2) ∧ PEqualNP.MetaComplexity.circuitFun (N + N) M (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)) = Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2) := by
    apply Finset.filter_congr
    intro e _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.1, fun h => ⟨h, hA e h⟩⟩
  have hcount : (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card = N * (q + 1) := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    have hl : ∀ l : Fin N, (∑ p : Fin N, if I p l then 1 else 0) = q + 1 := by
      intro l
      rw [← Finset.card_filter]
      exact hline l
    simp only [hl, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hK' : N * (q + 1) ≤ (6 * 0 + 6) * M.size + (12 * 0 ^ 2 + 13 * 0 + 2) * N + 6 * 0 ^ 2 + 5 * 0 := by
    rw [← hcount, ← hset]
    exact hK
  have hN7 : 7 ≤ N := by
    subst hN
    nlinarith
  have e1 : N * (q + 1) = N * q + N := by ring
  rw [e1] at hK'
  norm_num at hK'
  generalize N * q = A at *
  omega

-- Re-check request: the run on 8b77914 ended with FAULT (runner lost); this file is unchanged apart from this line.
