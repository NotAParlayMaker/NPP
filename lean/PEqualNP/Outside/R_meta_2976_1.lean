import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2976_1
    (hNoJunkBip :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool),
        (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
        NoFourCycle G →
        IsLeastAO G C →
        junk G C = ∅)
    (hTopForm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
        G.edgeFinset.Nonempty →
        IsLeastAO G C →
        ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size = C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x10 ∧ x16 ∈ x11 := by
  classical
  intro P L I instI C0 hNoC4 hAO0 hEval0
  let n := P + L
  by_cases hHasEdge : ∃ (p : Fin P) (l : Fin L), I p l
  · let G : SimpleGraph (Fin n) := {
      Adj := fun u v =>
        ∃ (p : Fin P) (l : Fin L), I p l ∧
          ((u = Fin.castAdd L p ∧ v = Fin.natAdd P l) ∨
           (u = Fin.natAdd P l ∧ v = Fin.castAdd L p))
      symm := ⟨fun u v h => by
        obtain ⟨p, l, hpl, h1 | h2⟩ := h
        · exact ⟨p, l, hpl, Or.inr ⟨h1.2, h1.1⟩⟩
        · exact ⟨p, l, hpl, Or.inl ⟨h2.2, h2.1⟩⟩⟩
      loopless := ⟨fun u h => by
        obtain ⟨p, l, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
        · have heq := congrArg Fin.val (h1.symm.trans h2)
          change p.val = P + l.val at heq
          omega
        · have heq := congrArg Fin.val (h1.symm.trans h2)
          change P + l.val = p.val at heq
          omega⟩
    }
    have hSideAdj : ∀ u v : Fin n, G.Adj u v → (u.val < P ↔ P ≤ v.val) := by
      intro u v h
      obtain ⟨p, l, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
      · constructor
        · intro _; change P ≤ P + l.val; omega
        · intro _; change p.val < P; exact p.isLt
      · constructor
        · intro hlt; change P + l.val < P at hlt; omega
        · intro hge; change P ≤ p.val at hge; omega
    let s : Fin n → Bool := fun u => decide (u.val < P)
    have hBip : ∀ u v : Fin n, G.Adj u v → s u ≠ s v := by
      intro u v huv
      have hs := hSideAdj u v huv
      change decide (u.val < P) ≠ decide (v.val < P)
      by_cases hu : u.val < P
      · have hv : ¬ v.val < P := Nat.not_lt.mpr (hs.mp hu)
        rw [decide_eq_true hu, decide_eq_false hv]
        decide
      · have hv : v.val < P := Nat.lt_of_not_ge (fun hge => hu (hs.mpr hge))
        rw [decide_eq_false hu, decide_eq_true hv]
        decide
    have hAdjCast : ∀ (p : Fin P) (l : Fin L), G.Adj (Fin.castAdd L p) (Fin.natAdd P l) ↔ I p l := by
      intro p l
      constructor
      · rintro ⟨p', l', hpl', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · have hp : p = p' := Fin.ext (by have := congrArg Fin.val h1; exact this)
          have hl : l = l' := Fin.ext (by have := congrArg Fin.val h2; change P + l.val = P + l'.val at this; omega)
          rw [hp, hl]; exact hpl'
        · have := congrArg Fin.val h1; change p.val = P + l'.val at this; omega
      · intro hpl; exact ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩
    have h4 : NoFourCycle G := by
      intro a b hab
      refine Finset.card_le_one.mpr ?_
      intro w1 hw1 w2 hw2
      have h1 := (Finset.mem_filter.mp hw1).2
      have h2 := (Finset.mem_filter.mp hw2).2
      by_contra hwne
      by_cases ha : a.val < P
      · have hw1_ge : P ≤ w1.val := (hSideAdj a w1 h1.1).mp ha
        have hw2_ge : P ≤ w2.val := (hSideAdj a w2 h2.1).mp ha
        have hb : b.val < P := (hSideAdj b w1 h1.2).mpr hw1_ge
        let pa : Fin P := ⟨a.val, ha⟩
        let pb : Fin P := ⟨b.val, hb⟩
        let l1 : Fin L := ⟨w1.val - P, by omega⟩
        let l2 : Fin L := ⟨w2.val - P, by omega⟩
        have hea : a = Fin.castAdd L pa := Fin.ext rfl
        have heb : b = Fin.castAdd L pb := Fin.ext rfl
        have he1 : w1 = Fin.natAdd P l1 := Fin.ext (by change w1.val = P + (w1.val - P); omega)
        have he2 : w2 = Fin.natAdd P l2 := Fin.ext (by change w2.val = P + (w2.val - P); omega)
        have hpne : pa ≠ pb := fun h => hab (by rw [hea, heb, h])
        have hlne : l1 ≠ l2 := fun h => hwne (by rw [he1, he2, h])
        have h1a : I pa l1 := (hAdjCast pa l1).mp (by rw [← hea, ← he1]; exact h1.1)
        have h1b : I pb l1 := (hAdjCast pb l1).mp (by rw [← heb, ← he1]; exact h1.2)
        have h2a : I pa l2 := (hAdjCast pa l2).mp (by rw [← hea, ← he2]; exact h2.1)
        have h2b : I pb l2 := (hAdjCast pb l2).mp (by rw [← heb, ← he2]; exact h2.2)
        exact hNoC4 pa pb l1 l2 hpne hlne ⟨h1a, h2a, h1b, h2b⟩
      · have ha_ge : P ≤ a.val := Nat.le_of_not_lt ha
        have hw1_lt : w1.val < P := (hSideAdj w1 a h1.1.symm).mpr ha_ge
        have hw2_lt : w2.val < P := (hSideAdj w2 a h2.1.symm).mpr ha_ge
        have hb_ge : P ≤ b.val := (hSideAdj w1 b h1.2.symm).mp hw1_lt
        let la : Fin L := ⟨a.val - P, by omega⟩
        let lb : Fin L := ⟨b.val - P, by omega⟩
        let p1 : Fin P := ⟨w1.val, hw1_lt⟩
        let p2 : Fin P := ⟨w2.val, hw2_lt⟩
        have hea : a = Fin.natAdd P la := Fin.ext (by change a.val = P + (a.val - P); omega)
        have heb : b = Fin.natAdd P lb := Fin.ext (by change b.val = P + (b.val - P); omega)
        have he1 : w1 = Fin.castAdd L p1 := Fin.ext rfl
        have he2 : w2 = Fin.castAdd L p2 := Fin.ext rfl
        have hlne : la ≠ lb := fun h => hab (by rw [hea, heb, h])
        have hpne : p1 ≠ p2 := fun h => hwne (by rw [he1, he2, h])
        have h1a : I p1 la := (hAdjCast p1 la).mp (by rw [← he1, ← hea]; exact h1.1.symm)
        have h1b : I p1 lb := (hAdjCast p1 lb).mp (by rw [← he1, ← heb]; exact h1.2.symm)
        have h2a : I p2 la := (hAdjCast p2 la).mp (by rw [← he2, ← hea]; exact h2.1.symm)
        have h2b : I p2 lb := (hAdjCast p2 lb).mp (by rw [← he2, ← heb]; exact h2.2.symm)
        exact hNoC4 p1 p2 la lb hpne hlne ⟨h1a, h1b, h2a, h2b⟩
    have hGraphFunEq (x : Fin n → Bool) :
        graphFun G ∅ x = decide (∃ (p : Fin P) (l : Fin L), I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
      change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) = _
      have hempty : decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) = false := by simp
      rw [hempty, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨u, v, huv, hxu, hxv⟩
        obtain ⟨p, l, hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := huv
        · exact ⟨p, l, hpl, hxu, hxv⟩
        · exact ⟨p, l, hpl, hxv, hxu⟩
      · rintro ⟨p, l, hpl, hxp, hxl⟩
        exact ⟨Fin.castAdd L p, Fin.natAdd P l, (hAdjCast p l).mpr hpl, hxp, hxl⟩
    have hEne : G.edgeFinset.Nonempty := by
      obtain ⟨p, l, hpl⟩ := hHasEdge
      exact ⟨s(Fin.castAdd L p, Fin.natAdd P l), SimpleGraph.mem_edgeFinset.mpr ((hAdjCast p l).mpr hpl)⟩
    have hFun0 : circuitFun n C0 = graphFun G ∅ := by
      funext x
      rw [hEval0 x, hGraphFunEq x]
    have hExMin : ∃ k : ℕ, ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = k :=
      ⟨C0.size, C0, hAO0, hFun0, rfl⟩
    let kMin := Nat.find hExMin
    obtain ⟨C1, hAO1, hFun1, hSz1⟩ := Nat.find_spec hExMin
    have hSz1Le : C1.size ≤ C0.size := by
      rw [hSz1]
      exact Nat.find_min' hExMin ⟨C0, hAO0, hFun0, rfl⟩
    have hLeast1 : IsLeastAO G C1 := by
      refine ⟨hAO1, hFun1, ?_⟩
      intro D hAOD hFunD
      rw [hSz1]
      exact Nat.find_min' hExMin ⟨D, hAOD, hFunD, rfl⟩
    obtain ⟨C, hLeast, hTop, hSzC⟩ := hTopForm n G C1 hEne hLeast1
    have hNoJ : junk G C = ∅ := hNoJunkBip n G C s hBip h4 hLeast
    have hAO : IsAO2 n C := hLeast.1
    have hFunC : circuitFun n C = graphFun G ∅ := hLeast.2.1
    have allAndBelow : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j := by
      intro j hj hop x hgx
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
      exact (hprefEq i (hAO.2.1 k hk i hi)).symm
    let growStep (acc : Finset ℕ) (k : ℕ) : Finset ℕ :=
      if (gateAt C k).op = GateOp.or ∧ ∀ u ∈ (gateAt C k).inputs, u ∈ acc then
        insert (n + k) acc
      else acc
    have growSub (ks : List ℕ) (acc : Finset ℕ) : acc ⊆ ks.foldl growStep acc := by
      induction ks generalizing acc with
      | nil => exact Finset.Subset.refl _
      | cons k ks ih =>
        rw [List.foldl_cons]
        refine Finset.Subset.trans ?_ (ih (growStep acc k))
        dsimp only [growStep]
        split
        · exact Finset.subset_insert _ _
        · exact Finset.Subset.refl _
    have growMem (ks : List ℕ) (acc : Finset ℕ) (w : ℕ) (hw : w ∈ ks.foldl growStep acc) :
        w ∈ acc ∨ ∃ k ∈ ks, w = n + k ∧ (gateAt C k).op = GateOp.or ∧
          ∀ u ∈ (gateAt C k).inputs, u ∈ ks.foldl growStep acc := by
      induction ks generalizing acc with
      | nil => exact Or.inl hw
      | cons k ks ih =>
        rw [List.foldl_cons] at hw ⊢
        rcases ih (growStep acc k) hw with h1 | ⟨m, hm, hwm, hop, hin⟩
        · dsimp only [growStep] at h1
          split at h1
          · rename_i hcond
            rcases Finset.mem_insert.mp h1 with rfl | h1'
            · refine Or.inr ⟨k, List.mem_cons_self, rfl, hcond.1, ?_⟩
              intro u hu
              have hgs : growStep acc k = insert (n + k) acc := by
                dsimp only [growStep]
                split
                · rfl
                · rename_i hn; exact (hn hcond).elim
              rw [hgs]
              exact growSub ks (insert (n + k) acc) (Finset.mem_insert_of_mem (hcond.2 u hu))
            · exact Or.inl h1'
          · exact Or.inl h1
        · exact Or.inr ⟨m, List.mem_cons_of_mem k hm, hwm, hop, hin⟩
    have growInsert (k : ℕ) (hk : k < C.gates.length) (acc0 : Finset ℕ)
        (hSub : ∀ u ∈ (gateAt C k).inputs, u ∈ ((List.range k).foldl growStep acc0))
        (hop : (gateAt C k).op = GateOp.or) :
        n + k ∈ (List.range C.gates.length).foldl growStep acc0 := by
      have hsplit : List.range C.gates.length = List.range k ++ (k :: (List.range (C.gates.length - (k + 1))).map (fun j => k + 1 + j)) := by
        have hlen : C.gates.length = k + 1 + (C.gates.length - (k + 1)) := by omega
        conv_lhs => rw [hlen, List.range_add, List.range_succ, List.append_assoc, List.singleton_append]
      rw [hsplit, List.foldl_append, List.foldl_cons]
      apply growSub
      dsimp only [growStep]
      split
      · exact Finset.mem_insert_self _ _
      · rename_i hn; exact (hn ⟨hop, hSub⟩).elim
    let P0 : Finset ℕ := Finset.range P
    let L0 : Finset ℕ := (Finset.range n).filter (fun w => P ≤ w)
    let Pset : Finset ℕ := (List.range C.gates.length).foldl growStep P0
    let Lset : Finset ℕ := (List.range C.gates.length).foldl growStep L0
    have growPref (m : ℕ) (acc0 : Finset ℕ) (w : ℕ)
        (hBound : ∀ x ∈ acc0, x < n)
        (hwlt : w < n + m) (hm : m ≤ C.gates.length)
        (hw : w ∈ (List.range C.gates.length).foldl growStep acc0) :
        w ∈ (List.range m).foldl growStep acc0 := by
      have hsplit : List.range C.gates.length = List.range m ++ (List.range (C.gates.length - m)).map (fun j => m + j) := by
        apply List.ext_getElem
        · simp only [List.length_range, List.length_append, List.length_map]; omega
        · intro i h1 h2
          simp only [List.getElem_range]
          by_cases him : i < m
          · rw [List.getElem_append_left (by simp only [List.length_range]; exact him)]
            simp only [List.getElem_range]
          · rw [List.getElem_append_right (by simp only [List.length_range]; omega)]
            simp only [List.length_range, List.getElem_map, List.getElem_range]
            omega
      rw [hsplit, List.foldl_append] at hw
      rcases growMem _ ((List.range m).foldl growStep acc0) w hw with hin | ⟨k, hk, hwk, _, _⟩
      · exact hin
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hk
        omega
    have pureOr : ∀ w : ℕ, w < n + C.gates.length →
        (∀ k : ℕ, w = n + k → (gateAt C k).op = GateOp.or ∧
          ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ¬ InCone n C j k) →
        ∃ S : Finset (Fin n), S.Nonempty ∧
          (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true ↔ ∃ u ∈ S, x u = true) ∧
          ((∀ u ∈ S, u.val < P) → w ∈ Pset) ∧
          ((∀ u ∈ S, P ≤ u.val) → w ∈ Lset) := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hcond
        by_cases hlt : w < n
        · refine ⟨{⟨w, hlt⟩}, Finset.singleton_nonempty _, ?_, ?_, ?_⟩
          · intro x
            rw [wireInput x w hlt]
            constructor
            · intro h; exact ⟨⟨w, hlt⟩, Finset.mem_singleton_self _, h⟩
            · rintro ⟨u, hu, hxu⟩; rw [Finset.mem_singleton.mp hu] at hxu; exact hxu
          · intro hP
            have hwP : w < P := hP ⟨w, hlt⟩ (Finset.mem_singleton_self _)
            exact growSub (List.range C.gates.length) P0 (Finset.mem_range.mpr hwP)
          · intro hL
            have hwL : P ≤ w := hL ⟨w, hlt⟩ (Finset.mem_singleton_self _)
            exact growSub (List.range C.gates.length) L0 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hwL⟩)
        · let k := w - n
          have hwk : w = n + k := by omega
          have hk : k < C.gates.length := by omega
          obtain ⟨hop, hnoAnd⟩ := hcond k hwk
          have hlen2 : (gateAt C k).inputs.length = 2 := by
            have hmem : gateAt C k ∈ C.gates := by
              change C.gates.getD k ⟨GateOp.or, []⟩ ∈ C.gates
              rw [List.getD_eq_getElem _ _ hk]
              exact List.getElem_mem hk
            exact hAO.2.2 (gateAt C k) hmem
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
                have ha_lt : a < n + k := hAO.2.1 k hk a ha_mem
                have hb_lt : b < n + k := hAO.2.1 k hk b hb_mem
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
                    rcases hAO.1 (gateAt C m) hm_mem with hand | hor
                    · exact (hnoAnd m hm_len hand hmk).elim
                    · exact hor
                  refine ⟨hm_or, ?_⟩
                  intro j hj hjand hjm
                  exact hnoAnd j hj hjand (inConeStep j m k hm_lt hk (by rw [← hum]; exact hu_mem) hjm)
                obtain ⟨Sa, hSa_ne, hSa, hSaP, hSaL⟩ := ih a (by omega) (by omega) (childCond a ha_mem ha_lt)
                obtain ⟨Sb, hSb_ne, hSb, hSbP, hSbL⟩ := ih b (by omega) (by omega) (childCond b hb_mem hb_lt)
                refine ⟨Sa ∪ Sb, hSa_ne.mono Finset.subset_union_left, ?_, ?_, ?_⟩
                · intro x
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
                · intro hP
                  have haP : a ∈ Pset := hSaP (fun u hu => hP u (Finset.mem_union_left _ hu))
                  have hbP : b ∈ Pset := hSbP (fun u hu => hP u (Finset.mem_union_right _ hu))
                  rw [hwk]
                  apply growInsert k hk P0 _ hop
                  intro u hu
                  rw [hin] at hu
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                  have hP0b : ∀ x ∈ P0, x < n := fun x hx => by
                    have := Finset.mem_range.mp hx; omega
                  rcases hu with hu1 | hu2
                  · rw [hu1]; exact growPref k P0 a hP0b ha_lt (Nat.le_of_lt hk) haP
                  · rw [hu2]; exact growPref k P0 b hP0b hb_lt (Nat.le_of_lt hk) hbP
                · intro hL
                  have haL : a ∈ Lset := hSaL (fun u hu => hL u (Finset.mem_union_left _ hu))
                  have hbL : b ∈ Lset := hSbL (fun u hu => hL u (Finset.mem_union_right _ hu))
                  rw [hwk]
                  apply growInsert k hk L0 _ hop
                  intro u hu
                  rw [hin] at hu
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                  have hL0b : ∀ x ∈ L0, x < n := fun x hx => Finset.mem_range.mp (Finset.mem_filter.mp hx).1
                  rcases hu with hu1 | hu2
                  · rw [hu1]; exact growPref k L0 a hL0b ha_lt (Nat.le_of_lt hk) haL
                  · rw [hu2]; exact growPref k L0 b hL0b hb_lt (Nat.le_of_lt hk) hbL
    have hAndSides : ∀ t < C.gates.length, (gateAt C t).op = GateOp.and →
        ∃ a b : ℕ, (gateAt C t).inputs = [a, b] ∧
          ((a ∈ Pset ∧ b ∈ Lset) ∨ (a ∈ Lset ∧ b ∈ Pset)) := by
      intro t ht htopT
      have hnoAndInT : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ¬ InCone n C j t := by
        intro j hj hjand
        exact hTop j hj t ht hjand (allAndBelow j hj hjand) htopT
      have hlen2 : (gateAt C t).inputs.length = 2 := by
        have hmem : gateAt C t ∈ C.gates := by
          change C.gates.getD t ⟨GateOp.or, []⟩ ∈ C.gates
          rw [List.getD_eq_getElem _ _ ht]
          exact List.getElem_mem ht
        exact hAO.2.2 (gateAt C t) hmem
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
            have ha_lt : a < n + t := hAO.2.1 t ht a ha_mem
            have hb_lt : b < n + t := hAO.2.1 t ht b hb_mem
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
                rcases hAO.1 (gateAt C m) hm_mem with hand | hor
                · exact (hnoAndInT m hm_len hand hmt).elim
                · exact hor
              refine ⟨hm_or, ?_⟩
              intro j hj hjand hjm
              exact hnoAndInT j hj hjand (inConeStep j m t hm_lt ht (by rw [← hum]; exact hu_mem) hjm)
            obtain ⟨Sa, hSa_ne, hSa, hSaP, hSaL⟩ := pureOr a (by omega) (sideCond a ha_mem ha_lt)
            obtain ⟨Sb, hSb_ne, hSb, hSbP, hSbL⟩ := pureOr b (by omega) (sideCond b hb_mem hb_lt)
            have hCrossAdj : ∀ u ∈ Sa, ∀ v ∈ Sb, G.Adj u v := by
              intro u hu v hv
              have htval : gateVal n C t (pairInput u v) = true := by
                change (C.wires (List.ofFn (pairInput u v))).getD (n + t) false = true
                rw [wireGate (pairInput u v) t ht, htopT, hin]
                change (((C.wires (List.ofFn (pairInput u v))).getD a false &&
                  ((C.wires (List.ofFn (pairInput u v))).getD b false && true)) = true)
                simp only [Bool.and_true, Bool.and_eq_true, hSa (pairInput u v), hSb (pairInput u v)]
                exact ⟨⟨u, hu, by change decide (u = u ∨ u = v) = true; exact decide_eq_true (Or.inl rfl)⟩,
                       ⟨v, hv, by change decide (v = u ∨ v = v) = true; exact decide_eq_true (Or.inr rfl)⟩⟩
              have hfg : graphFun G ∅ (pairInput u v) = true := allAndBelow t ht htopT (pairInput u v) htval
              change (decide (∃ z ∈ (∅ : Finset (Fin n)), pairInput u v z = true) ||
                decide (∃ i j : Fin n, G.Adj i j ∧ pairInput u v i = true ∧ pairInput u v j = true)) = true at hfg
              simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq] at hfg
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
            obtain ⟨u0, hu0⟩ := hSa_ne
            obtain ⟨v0, hv0⟩ := hSb_ne
            refine ⟨a, b, rfl, ?_⟩
            by_cases hu0P : u0.val < P
            · left
              have hvAll : ∀ v ∈ Sb, P ≤ v.val := fun v hv => (hSideAdj u0 v (hCrossAdj u0 hu0 v hv)).mp hu0P
              have huAll : ∀ u ∈ Sa, u.val < P := fun u hu => (hSideAdj u v0 (hCrossAdj u hu v0 hv0)).mpr (hvAll v0 hv0)
              exact ⟨hSaP huAll, hSbL hvAll⟩
            · right
              have hu0L : P ≤ u0.val := Nat.le_of_not_lt hu0P
              have hvAll : ∀ v ∈ Sb, v.val < P := fun v hv => (hSideAdj v u0 (hCrossAdj u0 hu0 v hv).symm).mpr hu0L
              have huAll : ∀ u ∈ Sa, P ≤ u.val := fun u hu => (hSideAdj v0 u (hCrossAdj u hu v0 hv0).symm).mp (hvAll v0 hv0)
              exact ⟨hSaL huAll, hSbP hvAll⟩
    let fixGate : Gate → Gate := fun g =>
      if g.op = GateOp.and ∧ g.inputs.getD 0 0 ∉ Pset then ⟨GateOp.and, g.inputs.reverse⟩ else g
    let C' : Circuit := ⟨C.gates.map fixGate, C.output⟩
    have hGateAt' (k : ℕ) (hk : k < C.gates.length) : gateAt C' k = fixGate (gateAt C k) := by
      change (C.gates.map fixGate).getD k ⟨GateOp.or, []⟩ = fixGate (C.gates.getD k ⟨GateOp.or, []⟩)
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_map]; exact hk),
          List.getD_eq_getElem _ _ hk, List.getElem_map]
    have hFixOr (g : Gate) (hor : g.op = GateOp.or) : fixGate g = g := by
      dsimp only [fixGate]
      split
      · rename_i h; rw [hor] at h; cases h.1
      · rfl
    have hAO' : IsAO2 n C' := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        dsimp only [fixGate]
        split
        · exact Or.inl rfl
        · exact hAO.1 g0 hg0
      · intro k hk i hi
        have hk0 : k < C.gates.length := by simpa only [C', List.length_map] using hk
        rw [hGateAt' k hk0] at hi
        dsimp only [fixGate] at hi
        split at hi
        · exact hAO.2.1 k hk0 i (List.mem_reverse.mp hi)
        · exact hAO.2.1 k hk0 i hi
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        dsimp only [fixGate]
        split
        · simp only [List.length_reverse]; exact hAO.2.2 g0 hg0
        · exact hAO.2.2 g0 hg0
    have hWiresEq (x : Fin n → Bool) :
        ∀ (gs : List Gate) (w : List Bool), (∀ g ∈ gs, g.inputs.length = 2) →
          (gs.map fixGate).foldl stepW w = gs.foldl stepW w := by
      intro gs
      induction gs with
      | nil => intro w _; rfl
      | cons g gs ih =>
        intro w hlen
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        have hstepEq : stepW w (fixGate g) = stepW w g := by
          dsimp only [fixGate]
          split
          · rename_i hc
            have hgl : g.inputs.length = 2 := hlen g List.mem_cons_self
            cases hin : g.inputs with
            | nil => rw [hin] at hgl; cases hgl
            | cons a rest =>
              cases rest with
              | nil => rw [hin] at hgl; cases hgl
              | cons b tail =>
                cases tail with
                | cons _ _ => rw [hin] at hgl; cases hgl
                | nil =>
                  dsimp only [stepW]
                  rw [hc.1, hin]
                  change w ++ [w.getD b false && (w.getD a false && true)] =
                    w ++ [w.getD a false && (w.getD b false && true)]
                  rw [Bool.and_true, Bool.and_true, Bool.and_comm]
          · rfl
        rw [hstepEq]
        exact ih (stepW w g) (fun g' hg' => hlen g' (List.mem_cons_of_mem _ hg'))
    have hEval' (x : Fin n → Bool) :
        circuitFun n C' x = decide (∃ (p : Fin P) (l : Fin L), I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
      have hw : C'.wires (List.ofFn x) = C.wires (List.ofFn x) :=
        hWiresEq x C.gates (List.ofFn x) hAO.2.2
      have hce : C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
        change (C'.wires (List.ofFn x)).getD C.output false = (C.wires (List.ofFn x)).getD C.output false
        rw [hw]
      change C'.eval (List.ofFn x) = _
      rw [hce]
      have hx := congrFun hFunC x
      change C.eval (List.ofFn x) = graphFun G ∅ x at hx
      rw [hx, hGraphFunEq x]
    have hSz' : C'.size ≤ C0.size := by
      have hlen : C'.size = C.size := by change (C.gates.map fixGate).length = C.gates.length; exact List.length_map _
      omega
    have hDisjPL : ∀ w : ℕ, w ∈ Pset → w ∉ Lset := by
      have hPbound : ∀ w ∈ Pset, w < P ∨ ∃ k < C.gates.length, w = n + k ∧ (gateAt C k).op = GateOp.or ∧
          ∀ u ∈ (gateAt C k).inputs, u ∈ Pset := by
        intro w hw
        rcases growMem (List.range C.gates.length) P0 w hw with h0 | ⟨k, hk, hwk, hop, hin⟩
        · exact Or.inl (Finset.mem_range.mp h0)
        · exact Or.inr ⟨k, List.mem_range.mp hk, hwk, hop, hin⟩
      have hLbound : ∀ w ∈ Lset, (P ≤ w ∧ w < n) ∨ ∃ k < C.gates.length, w = n + k ∧ (gateAt C k).op = GateOp.or ∧
          ∀ u ∈ (gateAt C k).inputs, u ∈ Lset := by
        intro w hw
        rcases growMem (List.range C.gates.length) L0 w hw with h0 | ⟨k, hk, hwk, hop, hin⟩
        · have hf := Finset.mem_filter.mp h0
          exact Or.inl ⟨hf.2, Finset.mem_range.mp hf.1⟩
        · exact Or.inr ⟨k, List.mem_range.mp hk, hwk, hop, hin⟩
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hwP hwL
        rcases hPbound w hwP with hP1 | ⟨k1, hk1, hw1, _, hin1⟩
        · rcases hLbound w hwL with ⟨hL1, _⟩ | ⟨k2, _, hw2, _, _⟩
          · omega
          · omega
        · rcases hLbound w hwL with ⟨_, hL2⟩ | ⟨k2, hk2, hw2, _, hin2⟩
          · omega
          · have hk12 : k1 = k2 := by omega
            subst hk12
            have hlen2 : (gateAt C k1).inputs.length = 2 := by
              have hmem : gateAt C k1 ∈ C.gates := by
                change C.gates.getD k1 ⟨GateOp.or, []⟩ ∈ C.gates
                rw [List.getD_eq_getElem _ _ hk1]
                exact List.getElem_mem hk1
              exact hAO.2.2 (gateAt C k1) hmem
            cases hin : (gateAt C k1).inputs with
            | nil => rw [hin] at hlen2; cases hlen2
            | cons a _ =>
              have ha_mem : a ∈ (gateAt C k1).inputs := by rw [hin]; simp
              have ha_lt : a < n + k1 := hAO.2.1 k1 hk1 a ha_mem
              exact ih a (by omega) (hin1 a ha_mem) (hin2 a ha_mem)
    refine ⟨C', Pset, Lset, hAO', hEval', hSz', ?_, ?_, ?_⟩
    · intro w hw
      rcases growMem (List.range C.gates.length) P0 w hw with h0 | ⟨k, hk, hwk, hop, hin⟩
      · exact Or.inl (Finset.mem_range.mp h0)
      · have hk' : k < C.gates.length := List.mem_range.mp hk
        refine Or.inr ⟨k, by simpa only [C', List.length_map] using hk', hwk, ?_, ?_⟩
        · rw [hGateAt' k hk', hFixOr _ hop]; exact hop
        · rw [hGateAt' k hk', hFixOr _ hop]; exact hin
    · intro w hw
      rcases growMem (List.range C.gates.length) L0 w hw with h0 | ⟨k, hk, hwk, hop, hin⟩
      · have hf := Finset.mem_filter.mp h0
        exact Or.inl ⟨hf.2, Finset.mem_range.mp hf.1⟩
      · have hk' : k < C.gates.length := List.mem_range.mp hk
        refine Or.inr ⟨k, by simpa only [C', List.length_map] using hk', hwk, ?_, ?_⟩
        · rw [hGateAt' k hk', hFixOr _ hop]; exact hop
        · rw [hGateAt' k hk', hFixOr _ hop]; exact hin
    · intro k hk hop'
      have hk0 : k < C.gates.length := by simpa only [C', List.length_map] using hk
      rw [hGateAt' k hk0] at hop' ⊢
      have hop0 : (gateAt C k).op = GateOp.and := by
        dsimp only [fixGate] at hop'
        split at hop'
        · rename_i hc; exact hc.1
        · exact hop'
      obtain ⟨a, b, hab, hSides⟩ := hAndSides k hk0 hop0
      rcases hSides with ⟨haP, hbL⟩ | ⟨haL, hbP⟩
      · refine ⟨a, b, ?_, haP, hbL⟩
        dsimp only [fixGate]
        split
        · rename_i hc
          exact (hc.2 (by rw [hab]; exact haP)).elim
        · exact hab
      · refine ⟨b, a, ?_, hbP, haL⟩
        dsimp only [fixGate]
        split
        · rw [hab]; rfl
        · rename_i hnot
          exact (hnot ⟨hop0, by rw [hab]; exact fun haP => hDisjPL a haP haL⟩).elim
  · refine ⟨⟨[], n⟩, ∅, ∅, ?_, ?_, Nat.zero_le _, ?_, ?_, ?_⟩
    · refine ⟨(by intro g hg; cases hg), (by intro j hj; cases hj), (by intro g hg; cases hg)⟩
    · intro x
      change (List.ofFn x).getD n false = decide (∃ (p : Fin P) (l : Fin L), I p l ∧
        x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)
      have hl : (List.ofFn x).getD n false = false :=
        List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)
      have hr : decide (∃ (p : Fin P) (l : Fin L), I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) = false :=
        decide_eq_false (by rintro ⟨p, l, hpl, _⟩; exact hHasEdge ⟨p, l, hpl⟩)
      rw [hl, hr]
    · intro w hw; exact (Finset.notMem_empty w hw).elim
    · intro w hw; exact (Finset.notMem_empty w hw).elim
    · intro k hk; cases hk
