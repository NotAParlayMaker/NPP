import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1031_4
    (hNoJunk :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.edgeFinset.Nonempty →
        (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
        NoFourCycle G →
        ∃ C : Circuit, IsLeastAO G C ∧ TopForm G C ∧ junk G C = ∅)
    (hAO2Min :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
        G.edgeFinset.Nonempty →
        Monotone2 D →
        circuitFun n D = graphFun G ∅ →
        ∃ E : Circuit, IsAO2 n E ∧ circuitFun n E = graphFun G ∅ ∧ E.size ≤ D.size) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  intro n G _ htri hc4
  by_cases hE : G.edgeFinset.Nonempty
  · have h4 : NoFourCycle G := by
      intro a b hab
      refine Finset.card_le_one.mpr ?_
      intro p hp q hq
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      exact (hc4 a p b q hp'.1 hp'.2.symm hq'.2 hq'.1.symm).resolve_left hab
    obtain ⟨C, hLeast, hTop, hNoJ⟩ := hNoJunk n G hE htri h4
    have hAO2 : IsAO2 n C := hLeast.1
    have hFun : circuitFun n C = graphFun G ∅ := hLeast.2.1
    have hMinAO : ∀ E : Circuit, IsAO2 n E → circuitFun n E = graphFun G ∅ → C.size ≤ E.size :=
      hLeast.2.2
    have graphFunEq (x : Fin n → Bool) :
        graphFun G ∅ x = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
      change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) = _
      simp
    have hMonoC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      refine ⟨hAO2.1 g hg, ?_⟩
      have hlen2 := hAO2.2.2 g hg
      omega
    have hEvalC (x : Fin n → Bool) :
        C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
      have hx := congrFun hFun x
      change C.eval (List.ofFn x) = graphFun G ∅ x at hx
      exact hx.trans (graphFunEq x)
    have hMinMono : ∀ D : Circuit,
        (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
        C.size ≤ D.size := by
      intro D hMD hED
      have hDF : circuitFun n D = graphFun G ∅ := by
        funext x
        change D.eval (List.ofFn x) = graphFun G ∅ x
        rw [hED x, graphFunEq x]
      obtain ⟨E, hEAO, hEF, hEsz⟩ := hAO2Min n G D hE hMD hDF
      exact le_trans (hMinAO E hEAO hEF) hEsz
    have allAndBelow : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j := by
      intro j hj hop
      intro x hgx
      by_contra hf
      have hfalse : graphFun G ∅ x = false := by
        cases hv : graphFun G ∅ x with
        | false => rfl
        | true => exact (hf hv).elim
      have hmem : j ∈ junk G C := by
        change j ∈ (Finset.range C.gates.length).filter (fun k => IsDirtyAnd n G C k)
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop, hj, x, hgx, hfalse⟩
      rw [hNoJ] at hmem
      exact Finset.notMem_empty j hmem
    have coneLen (gs : List Gate) (cs : List (List ℕ)) :
        (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
      induction gs generalizing cs with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        change (cs ++ [_]).length + gs.length = cs.length + (g :: gs).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    have coneKeep (gs : List Gate) (cs : List (List ℕ)) (m : ℕ) (hm : m < cs.length) :
        (gs.foldl (coneStep n) cs).getD m [] = cs.getD m [] := by
      induction gs generalizing cs with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons]
        have hm' : m < (coneStep n cs g).length := by
          change m < (cs ++ [_]).length
          rw [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [ih (coneStep n cs g) hm']
        exact List.getD_append _ _ _ _ hm
    have coneAt (k : ℕ) (hk : k < C.gates.length) :
        (cones n C).getD k [] =
          (((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
            (fun w => (w - n) :: (cones n C).getD (w - n) [])) := by
      have hsplit : C.gates = C.gates.take k ++ (gateAt C k :: C.gates.drop (k + 1)) := by
        have htake : C.gates.take k ++ C.gates.drop k = C.gates := List.take_append_drop k C.gates
        have hdrop : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
        have hgat : gateAt C k = C.gates[k] := by
          change C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k]
          exact List.getD_eq_getElem _ _ hk
        rw [hgat, ← hdrop, htake]
      let pref := (C.gates.take k).foldl (coneStep n) []
      have hplen : pref.length = k := by
        have hl := coneLen (C.gates.take k) []
        rw [List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hl
        exact hl
      have hprefEq (m : ℕ) (hm : m < k) : (cones n C).getD m [] = pref.getD m [] := by
        change (C.gates.foldl (coneStep n) []).getD m [] = pref.getD m []
        rw [hsplit, List.foldl_append]
        exact coneKeep _ pref m (by omega)
      have hstepK : (cones n C).getD k [] = (coneStep n pref (gateAt C k)).getD k [] := by
        change (C.gates.foldl (coneStep n) []).getD k [] = _
        rw [hsplit, List.foldl_append, List.foldl_cons]
        have hklt : k < (coneStep n pref (gateAt C k)).length := by
          change k < (pref ++ [_]).length
          rw [List.length_append, List.length_cons, List.length_nil, hplen]
          omega
        exact coneKeep _ (coneStep n pref (gateAt C k)) k hklt
      rw [hstepK]
      change (pref ++ [(((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pref.length))).flatMap
        (fun w => (w - n) :: pref.getD (w - n) []))]).getD k [] = _
      rw [List.getD_append_right _ _ _ _ (by omega), hplen, Nat.sub_self]
      change (((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: pref.getD (w - n) [])) = _
      refine List.flatMap_congr ?_
      intro w hw
      have hwf := (List.mem_filter.mp hw).2
      rw [decide_eq_true_eq] at hwf
      rw [hprefEq (w - n) (by omega)]
    have inConeDirect (i k : ℕ) (hi : i < k) (hk : k < C.gates.length)
        (hmem : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
      change i ∈ (cones n C).getD k []
      rw [coneAt k hk]
      refine List.mem_flatMap.mpr ⟨n + i, List.mem_filter.mpr ⟨hmem, decide_eq_true (by omega)⟩, ?_⟩
      simp only [Nat.add_sub_cancel_left, List.mem_cons, true_or]
    have inConeStep (j i k : ℕ) (hi : i < k) (hk : k < C.gates.length)
        (hmem : n + i ∈ (gateAt C k).inputs) (hji : InCone n C j i) : InCone n C j k := by
      change j ∈ (cones n C).getD k []
      rw [coneAt k hk]
      refine List.mem_flatMap.mpr ⟨n + i, List.mem_filter.mpr ⟨hmem, decide_eq_true (by omega)⟩, ?_⟩
      simp only [Nat.add_sub_cancel_left, List.mem_cons]
      exact Or.inr hji
    have rawToCone (a b : ℕ)
        (hr : Relation.TransGen (fun u v : ℕ => u < v ∧ ∃ (k : ℕ) (h : Gate), v = n + k ∧ C.gates[k]? = some h ∧ u ∈ h.inputs) a b) :
        ∀ i j : ℕ, a = n + i → b = n + j → InCone n C i j := by
      induction hr with
      | single hstep =>
        intro i j ha hb
        obtain ⟨hlt, k, g, hbk, hgk, hmem⟩ := hstep
        have hjk : j = k := by omega
        have hk : k < C.gates.length := by
          by_contra hge
          have hnone : C.gates[k]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hge)
          rw [hnone] at hgk
          cases hgk
        have hgat : gateAt C k = g := by
          change C.gates.getD k ⟨GateOp.or, []⟩ = g
          rw [List.getD_eq_getElem?_getD, hgk]
          rfl
        rw [← hgat, ha] at hmem
        rw [hjk]
        exact inConeDirect i k (by omega) hk hmem
      | @tail mid _ hpre hstep ih =>
        intro i j ha hb
        obtain ⟨hlt, k, g, hbk, hgk, hmem⟩ := hstep
        have hjk : j = k := by omega
        have hk : k < C.gates.length := by
          by_contra hge
          have hnone : C.gates[k]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hge)
          rw [hnone] at hgk
          cases hgk
        have hgat : gateAt C k = g := by
          change C.gates.getD k ⟨GateOp.or, []⟩ = g
          rw [List.getD_eq_getElem?_getD, hgk]
          rfl
        have hlt2 : a < mid := Relation.TransGen.trans_induction_on hpre (fun h => h.1) (fun _ _ h1 h2 => lt_trans h1 h2)
        let m := mid - n
        have hmid : mid = n + m := by omega
        have him : InCone n C i m := ih i m ha hmid
        rw [← hgat, hmid] at hmem
        rw [hjk]
        exact inConeStep i m k (by omega) hk hmem him
    let stepW : List Bool → Gate → List Bool :=
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have wiresLen (gs : List Gate) (w : List Bool) :
        (gs.foldl stepW w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp only [stepW, List.length_append, List.length_cons, List.length_nil]
        omega
    have wiresKeep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl stepW w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons]
        have hi' : i < (stepW w g).length := by
          simp only [stepW, List.length_append, List.length_cons, List.length_nil]
          omega
        rw [ih (stepW w g) hi']
        exact List.getD_append _ _ _ _ hi
    have wireInput (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
        (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
      change (C.gates.foldl stepW (List.ofFn x)).getD w false = x ⟨w, hw⟩
      rw [wiresKeep C.gates (List.ofFn x) w (by simpa only [List.length_ofFn] using hw)]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hw)]
      exact List.getElem_ofFn _
    have wireGate (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
        (C.wires (List.ofFn x)).getD (n + k) false =
          (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
      have hsplit : C.gates = C.gates.take k ++ (gateAt C k :: C.gates.drop (k + 1)) := by
        have htake : C.gates.take k ++ C.gates.drop k = C.gates := List.take_append_drop k C.gates
        have hdrop : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
        have hgat : gateAt C k = C.gates[k] := by
          change C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k]
          exact List.getD_eq_getElem _ _ hk
        rw [hgat, ← hdrop, htake]
      let pref := (C.gates.take k).foldl stepW (List.ofFn x)
      have hplen : pref.length = n + k := by
        have hl := wiresLen (C.gates.take k) (List.ofFn x)
        rw [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hl
        exact hl
      have hprefEq (i : ℕ) (hi : i < n + k) : (C.wires (List.ofFn x)).getD i false = pref.getD i false := by
        change (C.gates.foldl stepW (List.ofFn x)).getD i false = pref.getD i false
        rw [hsplit, List.foldl_append]
        exact wiresKeep _ pref i (by omega)
      have hstepK : (C.wires (List.ofFn x)).getD (n + k) false = (stepW pref (gateAt C k)).getD (n + k) false := by
        change (C.gates.foldl stepW (List.ofFn x)).getD (n + k) false = _
        rw [hsplit, List.foldl_append, List.foldl_cons]
        have hklt : n + k < (stepW pref (gateAt C k)).length := by
          simp only [stepW, List.length_append, List.length_cons, List.length_nil, hplen]
          omega
        exact wiresKeep _ (stepW pref (gateAt C k)) (n + k) hklt
      rw [hstepK]
      change (pref ++ [(gateAt C k).op.eval ((gateAt C k).inputs.map fun i => pref.getD i false)]).getD (n + k) false = _
      rw [List.getD_append_right _ _ _ _ (by omega), hplen, Nat.sub_self]
      change (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => pref.getD i false) = _
      congr 1
      refine List.map_congr_left ?_
      intro i hi
      exact (hprefEq i (hAO2.2.1 k hk i hi)).symm
    have pureOr : ∀ w : ℕ, w < n + C.gates.length →
        (∀ k : ℕ, w = n + k → (gateAt C k).op = GateOp.or ∧
          ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ¬ InCone n C j k) →
        ∃ S : Finset (Fin n), S.Nonempty ∧
          ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true ↔ ∃ u ∈ S, x u = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hcond
        by_cases hlt : w < n
        · refine ⟨{⟨w, hlt⟩}, Finset.singleton_nonempty _, ?_⟩
          intro x
          rw [wireInput x w hlt]
          constructor
          · intro h; exact ⟨⟨w, hlt⟩, Finset.mem_singleton_self _, h⟩
          · rintro ⟨u, hu, hxu⟩; rw [Finset.mem_singleton.mp hu] at hxu; exact hxu
        · let k := w - n
          have hwk : w = n + k := by omega
          have hk : k < C.gates.length := by omega
          obtain ⟨hop, hnoAnd⟩ := hcond k hwk
          have hlen2 : (gateAt C k).inputs.length = 2 := by
            have hmem : gateAt C k ∈ C.gates := by
              change C.gates.getD k ⟨GateOp.or, []⟩ ∈ C.gates
              rw [List.getD_eq_getElem _ _ hk]
              exact List.getElem_mem hk
            exact hAO2.2.2 (gateAt C k) hmem
          cases hin : (gateAt C k).inputs with
          | nil => rw [hin] at hlen2; cases hlen2
          | cons a rest =>
            cases rest with
            | nil => rw [hin] at hlen2; cases hlen2
            | cons b tail =>
              cases tail with
              | cons _ _ => rw [hin] at hlen2; cases hlen2
              | nil =>
                have ha_mem : a ∈ (gateAt C k).inputs := by rw [hin]; simp
                have hb_mem : b ∈ (gateAt C k).inputs := by rw [hin]; simp
                have ha_lt : a < n + k := hAO2.2.1 k hk a ha_mem
                have hb_lt : b < n + k := hAO2.2.1 k hk b hb_mem
                have childCond (u : ℕ) (hu_mem : u ∈ (gateAt C k).inputs) (hu_lt : u < n + k) :
                    ∀ m : ℕ, u = n + m → (gateAt C m).op = GateOp.or ∧
                      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ¬ InCone n C j m := by
                  intro m hum
                  have hm_lt : m < k := by omega
                  have hm_len : m < C.gates.length := by omega
                  have hmk : InCone n C m k := inConeDirect m k hm_lt hk (by rw [← hum]; exact hu_mem)
                  have hm_mem : gateAt C m ∈ C.gates := by
                    change C.gates.getD m ⟨GateOp.or, []⟩ ∈ C.gates
                    rw [List.getD_eq_getElem _ _ hm_len]
                    exact List.getElem_mem hm_len
                  have hm_or : (gateAt C m).op = GateOp.or := by
                    rcases hAO2.1 (gateAt C m) hm_mem with hand | hor
                    · exact (hnoAnd m hm_len hand hmk).elim
                    · exact hor
                  refine ⟨hm_or, ?_⟩
                  intro j hj hjand hjm
                  exact hnoAnd j hj hjand (inConeStep j m k hm_lt hk (by rw [← hum]; exact hu_mem) hjm)
                obtain ⟨Sa, hSa_ne, hSa⟩ := ih a (by omega) (by omega) (childCond a ha_mem ha_lt)
                obtain ⟨Sb, hSb_ne, hSb⟩ := ih b (by omega) (by omega) (childCond b hb_mem hb_lt)
                refine ⟨Sa ∪ Sb, hSa_ne.mono Finset.subset_union_left, ?_⟩
                intro x
                rw [hwk, wireGate x k hk, hop, hin]
                change (((C.wires (List.ofFn x)).getD a false ||
                  ((C.wires (List.ofFn x)).getD b false || false)) = true) ↔ _
                simp only [Bool.or_false, Bool.or_eq_true, hSa x, hSb x, Finset.mem_union]
                constructor
                · rintro (⟨u, hu, hxu⟩ | ⟨u, hu, hxu⟩)
                  · exact ⟨u, Or.inl hu, hxu⟩
                  · exact ⟨u, Or.inr hu, hxu⟩
                · rintro ⟨u, hu | hu, hxu⟩
                  · exact Or.inl ⟨u, hu, hxu⟩
                  · exact Or.inr ⟨u, hu, hxu⟩
    refine ⟨C, hMonoC, hEvalC, hMinMono, ?_⟩
    intro t g htg hgop
    have ht : t < C.gates.length := by
      by_contra hge
      have hnone : C.gates[t]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hge)
      rw [hnone] at htg
      cases htg
    have hgat : gateAt C t = g := by
      change C.gates.getD t ⟨GateOp.or, []⟩ = g
      rw [List.getD_eq_getElem?_getD, htg]
      rfl
    have htopT : (gateAt C t).op = GateOp.and := by rw [hgat]; exact hgop
    have hnoAndInT : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ¬ InCone n C j t := by
      intro j hj hjand
      exact hTop j hj t ht hjand (allAndBelow j hj hjand) htopT
    have hlen2 : (gateAt C t).inputs.length = 2 := by
      have hmem : gateAt C t ∈ C.gates := by
        change C.gates.getD t ⟨GateOp.or, []⟩ ∈ C.gates
        rw [List.getD_eq_getElem _ _ ht]
        exact List.getElem_mem ht
      exact hAO2.2.2 (gateAt C t) hmem
    cases hin : (gateAt C t).inputs with
    | nil => rw [hin] at hlen2; cases hlen2
    | cons a rest =>
      cases rest with
      | nil => rw [hin] at hlen2; cases hlen2
      | cons b tail =>
        cases tail with
        | cons _ _ => rw [hin] at hlen2; cases hlen2
        | nil =>
          have ha_mem : a ∈ (gateAt C t).inputs := by rw [hin]; simp
          have hb_mem : b ∈ (gateAt C t).inputs := by rw [hin]; simp
          have ha_lt : a < n + t := hAO2.2.1 t ht a ha_mem
          have hb_lt : b < n + t := hAO2.2.1 t ht b hb_mem
          have sideCond (u : ℕ) (hu_mem : u ∈ (gateAt C t).inputs) (hu_lt : u < n + t) :
              ∀ m : ℕ, u = n + m → (gateAt C m).op = GateOp.or ∧
                ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ¬ InCone n C j m := by
            intro m hum
            have hm_lt : m < t := by omega
            have hm_len : m < C.gates.length := by omega
            have hmt : InCone n C m t := inConeDirect m t hm_lt ht (by rw [← hum]; exact hu_mem)
            have hm_mem : gateAt C m ∈ C.gates := by
              change C.gates.getD m ⟨GateOp.or, []⟩ ∈ C.gates
              rw [List.getD_eq_getElem _ _ hm_len]
              exact List.getElem_mem hm_len
            have hm_or : (gateAt C m).op = GateOp.or := by
              rcases hAO2.1 (gateAt C m) hm_mem with hand | hor
              · exact (hnoAndInT m hm_len hand hmt).elim
              · exact hor
            refine ⟨hm_or, ?_⟩
            intro j hj hjand hjm
            exact hnoAndInT j hj hjand (inConeStep j m t hm_lt ht (by rw [← hum]; exact hu_mem) hjm)
          obtain ⟨Sa, hSa_ne, hSa⟩ := pureOr a (by omega) (sideCond a ha_mem ha_lt)
          obtain ⟨Sb, hSb_ne, hSb⟩ := pureOr b (by omega) (sideCond b hb_mem hb_lt)
          have hTeval (x : Fin n → Bool) :
              (C.wires (List.ofFn x)).getD (n + t) false = true ↔
                (∃ u ∈ Sa, x u = true) ∧ (∃ v ∈ Sb, x v = true) := by
            rw [wireGate x t ht, htopT, hin]
            change (((C.wires (List.ofFn x)).getD a false &&
              ((C.wires (List.ofFn x)).getD b false && true)) = true) ↔ _
            simp only [Bool.and_true, Bool.and_eq_true, hSa x, hSb x]
          have hCrossAdj : ∀ u ∈ Sa, ∀ v ∈ Sb, G.Adj u v := by
            intro u hu v hv
            have htval : gateVal n C t (pairInput u v) = true := by
              change (C.wires (List.ofFn (pairInput u v))).getD (n + t) false = true
              exact (hTeval (pairInput u v)).mpr
                ⟨⟨u, hu, by change decide (u = u ∨ u = v) = true; exact decide_eq_true (Or.inl rfl)⟩,
                 ⟨v, hv, by change decide (v = u ∨ v = v) = true; exact decide_eq_true (Or.inr rfl)⟩⟩
            have hfg : graphFun G ∅ (pairInput u v) = true := allAndBelow t ht htopT (pairInput u v) htval
            rw [graphFunEq, decide_eq_true_eq] at hfg
            obtain ⟨i, j, hij, hi, hj⟩ := hfg
            change decide (i = u ∨ i = v) = true at hi
            change decide (j = u ∨ j = v) = true at hj
            rw [decide_eq_true_eq] at hi hj
            have hne : i ≠ j := G.ne_of_adj hij
            rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
            · exact (hne rfl).elim
            · exact hij
            · exact hij.symm
            · exact (hne rfl).elim
          have hStarSides : Sa.card ≤ 1 ∨ Sb.card ≤ 1 := by
            by_contra hboth
            have hSa_gt : 1 < Sa.card := Nat.lt_of_not_ge (fun h => hboth (Or.inl h))
            have hSb_gt : 1 < Sb.card := Nat.lt_of_not_ge (fun h => hboth (Or.inr h))
            obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp hSa_gt
            obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp hSb_gt
            have hsub : ({v1, v2} : Finset (Fin n)) ⊆ Finset.univ.filter (fun w => G.Adj u1 w ∧ G.Adj u2 w) := by
              intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩
              rcases hw with hw1 | hw2
              · rw [hw1]; exact ⟨hCrossAdj u1 hu1 v1 hv1, hCrossAdj u2 hu2 v1 hv1⟩
              · rw [hw2]; exact ⟨hCrossAdj u1 hu1 v2 hv2, hCrossAdj u2 hu2 v2 hv2⟩
            have hle := Finset.card_le_card hsub
            rw [Finset.card_pair hv12] at hle
            have h4u := h4 u1 u2 hu12
            omega
          have hNoRaw (t' : ℕ) (g' : Gate) (htg' : C.gates[t']? = some g') (hgop' : g'.op = GateOp.and)
              (hr : Relation.TransGen (fun u v : ℕ => u < v ∧ ∃ (k : ℕ) (h : Gate), v = n + k ∧ C.gates[k]? = some h ∧ u ∈ h.inputs) (n + t') (n + t)) :
              False := by
            have ht' : t' < C.gates.length := by
              by_contra hge
              have hnone : C.gates[t']? = none := List.getElem?_eq_none (Nat.le_of_not_lt hge)
              rw [hnone] at htg'
              cases htg'
            have hgat' : gateAt C t' = g' := by
              change C.gates.getD t' ⟨GateOp.or, []⟩ = g'
              rw [List.getD_eq_getElem?_getD, htg']
              rfl
            have hop' : (gateAt C t').op = GateOp.and := by rw [hgat']; exact hgop'
            exact hnoAndInT t' ht' hop' (rawToCone (n + t') (n + t) hr t' t rfl rfl)
          obtain ⟨u0, hu0⟩ := hSa_ne
          obtain ⟨v0, hv0⟩ := hSb_ne
          have hOwns0 : G.Adj u0 v0 ∧
              ((C.wires (List.ofFn (fun k : Fin n => decide (k = u0 ∨ k = v0)))).getD (n + t) false = true ∧
               ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
                 Relation.TransGen (fun u v : ℕ => u < v ∧ ∃ (k : ℕ) (h : Gate), v = n + k ∧ C.gates[k]? = some h ∧ u ∈ h.inputs) (n + t') (n + t) →
                 (C.wires (List.ofFn (fun k : Fin n => decide (k = u0 ∨ k = v0)))).getD (n + t') false = false) := by
            refine ⟨hCrossAdj u0 hu0 v0 hv0, ?_, fun t' g' h1 h2 h3 => (hNoRaw t' g' h1 h2 h3).elim⟩
            exact (hTeval (fun k : Fin n => decide (k = u0 ∨ k = v0))).mpr
              ⟨⟨u0, hu0, decide_eq_true (Or.inl rfl)⟩, ⟨v0, hv0, decide_eq_true (Or.inr rfl)⟩⟩
          rcases hStarSides with hSa1 | hSb1
          · refine ⟨u0, ⟨u0, v0, hOwns0⟩, ?_⟩
            intro u v _ hown
            obtain ⟨⟨a0, ha0, ha0t⟩, _⟩ := (hTeval (fun k : Fin n => decide (k = u ∨ k = v))).mp hown.1
            have ha0eq : a0 = u0 := Finset.card_le_one.mp hSa1 a0 ha0 u0 hu0
            rw [ha0eq, decide_eq_true_eq] at ha0t
            rcases ha0t with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          · refine ⟨v0, ⟨u0, v0, hOwns0⟩, ?_⟩
            intro u v _ hown
            obtain ⟨_, ⟨b0, hb0, hb0t⟩⟩ := (hTeval (fun k : Fin n => decide (k = u ∨ k = v))).mp hown.1
            have hb0eq : b0 = v0 := Finset.card_le_one.mp hSb1 b0 hb0 v0 hv0
            rw [hb0eq, decide_eq_true_eq] at hb0t
            rcases hb0t with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
  · rw [Finset.not_nonempty_iff_eq_empty] at hE
    have hNoEdge : ∀ i j : Fin n, ¬ G.Adj i j := by
      intro i j hij
      have hmem : s(i, j) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hij
      rw [hE] at hmem
      exact Finset.notMem_empty _ hmem
    refine ⟨⟨[], n⟩, (by intro g hg; cases hg), ?_, ?_, ?_⟩
    · intro x
      change (List.ofFn x).getD n false = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
      have hl : (List.ofFn x).getD n false = false :=
        List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)
      have hr : decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) = false :=
        decide_eq_false (by rintro ⟨i, j, hij, _⟩; exact hNoEdge i j hij)
      rw [hl, hr]
    · intro D _ _; exact Nat.zero_le _
    · intro t g htg _; cases htg
