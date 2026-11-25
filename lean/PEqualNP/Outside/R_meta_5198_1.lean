import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.EdgeOwnership

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5198_1
    (normalize :
      let P := PEqualNP.HeptadCover.singerLines3
      let X := fun (T L : Finset (Fin 13)) =>
        (List.ofFn fun p : Fin 13 => decide (p ∈ T)) ++
        (List.ofFn fun l : Fin 13 => decide (l ∈ L))
      let W := fun (C : Circuit) (r : ℕ) (x : List Bool) => (C.wires x).getD r false
      let good := fun (C : Circuit) (a b : ℕ) =>
        (∀ p l : Fin 13, p ∈ P l → W C a (X {p} {l}) = true ∨ W C b (X {p} {l}) = true) ∧
        (∀ Q, PEqualNP.HeptadCover.IsQuadrangle P Q →
          W C a (X Q (PEqualNP.HeptadCover.missLines P Q)) = false ∧
          W C b (X Q (PEqualNP.HeptadCover.missLines P Q)) = false)
      let aa := fun (C : Circuit) (j : ℕ) =>
        (gateAt C j).op = GateOp.and ∧ ∃ i ∈ (gateAt C j).inputs,
          26 ≤ i ∧ (gateAt C (i - 26)).op = GateOp.and
      ∀ C a b, Monotone2 C → ReadsBack 26 C → good C a b →
        (∀ j ∈ Finset.range C.size, ∀ k ∈ Finset.range C.size, aa C j → aa C k → j = k) →
        ∃ D u v, Monotone2 D ∧ ReadsBack 26 D ∧
          PEqualNP.MetaComplexity.SingleLevel.IsSingleLevel 26 D ∧ D.size ≤ C.size ∧ good D u v)
    (geometry :
      let P := PEqualNP.HeptadCover.singerLines3
      let X := fun (T L : Finset (Fin 13)) =>
        (List.ofFn fun p : Fin 13 => decide (p ∈ T)) ++
        (List.ofFn fun l : Fin 13 => decide (l ∈ L))
      let G := PEqualNP.EdgeOwnership.edgeGraph 26
        ((List.finRange 13).flatMap fun p =>
          ((List.finRange 13).filter fun l => decide (p ∈ P l)).map fun l => (p.val, 13 + l.val))
      PEqualNP.TopForm.NoFourCycle G ∧ G.edgeFinset.card = 52 ∧
        (∀ T : Finset (Fin 26), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → 13 ≤ T.card) ∧
        ∀ u v : Fin 26, ¬ G.Adj u v → ∃ Q, PEqualNP.HeptadCover.IsQuadrangle P Q ∧
          (X Q (PEqualNP.HeptadCover.missLines P Q)).getD u.val false = true ∧
          (X Q (PEqualNP.HeptadCover.missLines P Q)).getD v.val false = true)
    (count :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ),
        PEqualNP.TopForm.NoFourCycle G →
        (∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
        ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack n C →
          PEqualNP.MetaComplexity.SingleLevel.IsSingleLevel n C →
          let W := fun r u v => (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD r false
          (∀ u v, G.Adj u v → W a u v = true ∨ W b u v = true) →
          (∀ u v, ¬ G.Adj u v → W a u v = false ∧ W b u v = false) →
          G.edgeFinset.card + k ≤ C.size + 2)
    : have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x8 < (26 : ℕ) + x7.size → x9 < (26 : ℕ) + x7.size → (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 → x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 → x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧ x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧ x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧ x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) → (∀ x18 ∈ Finset.range x7.size, ∀ x20 ∈ Finset.range x7.size, x6 x7 x18 → x6 x7 x20 → x18 = x20) → (63 : ℕ) ≤ x7.size := by
  dsimp only
  intro C a b hm hr _ _ hpos hneg _ _ haa
  let P := singerLines3
  let X := fun (T L : Finset (Fin 13)) =>
    (List.ofFn fun p : Fin 13 => decide (p ∈ T)) ++
    (List.ofFn fun l : Fin 13 => decide (l ∈ L))
  let G := edgeGraph 26 ((List.finRange 13).flatMap fun p =>
    ((List.finRange 13).filter fun l => decide (p ∈ P l)).map
      fun l => (p.val, 13 + l.val))
  let run (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

  have snoc (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    simp

  have op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
      (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
      op.eval l₁ = true → op.eval l₂ = true := by
    rcases hop with rfl | rfl
    · change l₁.all id = true → l₂.all id = true
      simp only [List.all_eq_true, id_eq]
      intro h b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        have hi1 : i < l₁.length := by omega
        rw [List.getD_eq_getElem _ _ hi1]
        exact h _ (List.getElem_mem hi1)
      have h2 := hle i h1
      rwa [List.getD_eq_getElem _ _ hi] at h2
    · change l₁.any id = true → l₂.any id = true
      simp only [List.any_eq_true, id_eq]
      rintro ⟨b, hb, rfl⟩
      obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        rw [List.getD_eq_getElem _ _ hi]
        exact hbi
      have h2 := hle i h1
      have hi2 : i < l₂.length := by omega
      rw [List.getD_eq_getElem _ _ hi2] at h2
      exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

  have run_mono (gs : List Gate)
      (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
        (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
        ∀ i, (run gs w₁).getD i false = true → (run gs w₂).getD i false = true := by
    induction gs with
    | nil =>
      intro w₁ w₂ _ hle i hi
      exact hle i hi
    | cons g gs ih =>
      intro w₁ w₂ hlen hle i hi
      have hstep1 : run (g :: gs) w₁ =
          run gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
      have hstep2 : run (g :: gs) w₂ =
          run gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
      rw [hstep1] at hi
      rw [hstep2]
      apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
      intro j hj
      by_cases hlt : j < w₁.length
      · rw [List.getD_append _ _ _ _ hlt] at hj
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle j hj
      · by_cases heq : j = w₁.length
        · subst heq
          rw [snoc] at hj
          rw [hlen, snoc]
          exact op_mono g.op (hmono g List.mem_cons_self)
            (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
            (by simp) (by
              intro t ht
              by_cases ht_lt : t < g.inputs.length
              · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
                rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
                simp only [List.getElem_map] at ht ⊢
                exact hle _ ht
              · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
                exact Bool.noConfusion ht) hj
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
          exact Bool.noConfusion hj

  have wires_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool)
      (hlen : x.length = y.length)
      (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
      ∀ i, (C.wires x).getD i false = true → (C.wires y).getD i false = true := by
    apply run_mono C.gates ?_ x y hlen hle
    intro g hg
    have hop := (hm g hg).1
    simpa using hop

  have hpair {n : ℕ} (u v : Fin n) :
      pairInput u v = (fun w => decide (w = u ∨ w = v)) := rfl

  have pair_le {n : ℕ} (u v : Fin n) (y : List Bool)
      (hu : y.getD u.val false = true) (hv : y.getD v.val false = true) :
      ∀ i, (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)).getD i false = true →
        y.getD i false = true := by
    intro i ht
    by_cases hi : i < n
    · have hj : (⟨i, hi⟩ : Fin n) = u ∨ (⟨i, hi⟩ : Fin n) = v := by
        simpa [List.getD_eq_getElem, hi, hpair] using ht
      rcases hj with h | h
      · have he : i = u.val := congrArg Fin.val h
        rw [he]
        exact hu
      · have he : i = v.val := congrArg Fin.val h
        rw [he]
        exact hv
    · rw [List.getD_eq_default _ _ (by simp; omega)] at ht
      exact Bool.noConfusion ht

  have reject_pair {n : ℕ} (C : Circuit) (hm : Monotone2 C) (u v : Fin n)
      (y : List Bool) (hlen : y.length = n)
      (hu : y.getD u.val false = true) (hv : y.getD v.val false = true)
      (r : ℕ) (hr : (C.wires y).getD r false = false) :
      (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD r false = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hot := wires_mono C hm _ y (by simp [hlen]) (pair_le u v y hu hv) r ht
    rw [hr] at hot
    exact Bool.noConfusion hot

  have pair_split (p l : Fin 13) :
      List.ofFn (pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)) = X {p} {l} := by
    rw [List.ofFn_add (n := 13) (m := 13)]
    apply congrArg₂ List.append
    · congr 1
      funext q
      simp [hpair, Fin.ext_iff]; omega
    · congr 1
      funext q
      simp [hpair, Fin.ext_iff]; omega

  have pair_swap {n : ℕ} (u v : Fin n) :
      List.ofFn (pairInput u v) = List.ofFn (pairInput v u) := by
    congr 1
    funext i
    simp [hpair, or_comm]

  have adjacent (x y : Fin 26) (h : G.Adj x y) :
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧
        ((x = Fin.castAdd 13 p ∧ y = Fin.natAdd 13 l) ∨
          (y = Fin.castAdd 13 p ∧ x = Fin.natAdd 13 l)) := by
    have orient (u v : Fin 26)
        (hmem : (u.val, v.val) ∈ (List.finRange 13).flatMap (fun p =>
          ((List.finRange 13).filter fun l => decide (p ∈ singerLines3 l)).map
            fun l => (p.val, 13 + l.val))) :
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧
          u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l := by
      obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hmem
      obtain ⟨l, hl, heq⟩ := List.mem_map.mp hp
      refine ⟨p, l, of_decide_eq_true (List.mem_filter.mp hl).2, ?_, ?_⟩
      · apply Fin.ext
        exact (congrArg Prod.fst heq).symm
      · apply Fin.ext
        exact (congrArg Prod.snd heq).symm
    rcases h.2 with hxy | hyx
    · obtain ⟨p, l, hp, hx, hy⟩ := orient x y hxy
      exact ⟨p, l, hp, Or.inl ⟨hx, hy⟩⟩
    · obtain ⟨p, l, hp, hy, hx⟩ := orient y x hyx
      exact ⟨p, l, hp, Or.inr ⟨hy, hx⟩⟩

  obtain ⟨D, u, v, hDM, hDB, hSL, hsize, hgood⟩ :=
    normalize C a b hm hr ⟨hpos, hneg⟩ haa
  obtain ⟨hNo4, hEdge, hCover, hExtend⟩ := geometry
  have bound : G.edgeFinset.card + 13 ≤ D.size + 2 := by
    apply count 26 G 13 hNo4 hCover D u v hDM hDB hSL
    · intro x y hxy
      obtain ⟨p, l, hpl, horder⟩ := adjacent x y hxy
      rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa only [pair_split] using hgood.1 p l hpl
      · simpa only [pair_swap (Fin.natAdd 13 l) (Fin.castAdd 13 p), pair_split] using hgood.1 p l hpl
    · intro x y hxy
      obtain ⟨Q, hQ, hx, hy⟩ := hExtend x y hxy
      obtain ⟨hU, hV⟩ := hgood.2 Q hQ
      exact ⟨reject_pair D hDM x y (X Q (missLines P Q)) (by simp [X]) hx hy u hU,
        reject_pair D hDM x y (X Q (missLines P Q)) (by simp [X]) hx hy v hV⟩
  have hE : G.edgeFinset.card = 52 := hEdge
  rw [hE] at bound
  omega
