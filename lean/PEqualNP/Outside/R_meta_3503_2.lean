import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3503_2
    (hTopForm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧ PEqualNP.TopForm.TopForm G C')
    (hOneJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B : Finset (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ),
      (∀ u v : Fin n, G.Adj u v → (u ∈ B ↔ v ∉ B)) →
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      PEqualNP.TopForm.junk G C = {g} →
      ∃ K : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
        G.edgeFinset.card + K.card ≤ C.size + 1)
    (hFlatJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B : Finset (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ u v : Fin n, G.Adj u v → (u ∈ B ↔ v ∉ B)) →
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      2 ≤ (PEqualNP.TopForm.junk G C).card →
      (∀ i ∈ PEqualNP.TopForm.junk G C, ∀ j ∈ PEqualNP.TopForm.junk G C,
        ¬ PEqualNP.EdgeOwnership.InCone n C i j) →
      ∃ K : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
        G.edgeFinset.card + K.card ≤ C.size + 1)
    (hNestedJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B : Finset (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ u v : Fin n, G.Adj u v → (u ∈ B ↔ v ∉ B)) →
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      2 ≤ (PEqualNP.TopForm.junk G C).card →
      (∃ i ∈ PEqualNP.TopForm.junk G C, ∃ j ∈ PEqualNP.TopForm.junk G C,
        PEqualNP.EdgeOwnership.InCone n C i j) →
      ∃ K : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
        G.edgeFinset.card + K.card ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ (x15 ∈ x10 ∧ x16 ∈ x11 ∨ x15 ∈ x11 ∧ x16 ∈ x10) := by
  classical
  intro Np Nl I _ C0 hNoC4 hAO0 hFun0
  let n : ℕ := Np + Nl
  let stepW : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [stepW]
      omega
  have foldl_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih]
      · simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [stepW]; omega
  have foldl_getD_last : ∀ (w : List Bool) (g : Gate),
      (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    intro w g
    simp [stepW, List.getD_eq_getElem?_getD]
  have foldl_at : ∀ (gs : List Gate) (w : List Bool) (j : ℕ),
      j < gs.length →
      (gs.foldl stepW w).getD (w.length + j) false =
        (gs.getD j ⟨GateOp.or, []⟩).op.eval
          ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
            ((gs.take j).foldl stepW w).getD i false) := by
    intro gs w j hj
    have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
      have h1 := (List.take_append_drop j gs).symm
      rw [List.drop_eq_getElem_cons hj] at h1
      exact h1
    have hgate : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := by
      simp [List.getD_eq_getElem?_getD, hj]
    rw [hgate]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    have hlen : ((gs.take j).foldl stepW w).length = w.length + j := by
      rw [foldl_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    rw [foldl_prefix (gs.drop (j + 1))]
    · rw [← hlen, foldl_getD_last]
    · show w.length + j < ((gs.take j).foldl stepW w ++ [_]).length
      rw [List.length_append, List.length_singleton, hlen]
      omega
  have wval_input : ∀ (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n),
      (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
    intro C x i hi
    change (C.gates.foldl stepW (List.ofFn x)).getD i false = x ⟨i, hi⟩
    rw [foldl_prefix C.gates (List.ofFn x) i (by simp [hi])]
    simp [List.getD_eq_getElem?_getD, hi]
  have wval_gate : ∀ (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool) (j : ℕ)
      (hj : j < C.gates.length),
      (C.wires (List.ofFn x)).getD (n + j) false =
        (gateAt C j).op.eval
          ((gateAt C j).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
    intro C hRB x j hj
    change (C.gates.foldl stepW (List.ofFn x)).getD (n + j) false = _
    have hlen_x : (List.ofFn x).length = n := by simp
    have h1 := foldl_at C.gates (List.ofFn x) j hj
    rw [hlen_x] at h1
    rw [h1]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hlt : i < n + j := hRB j hj i hi
    have htake_len : ((C.gates.take j).foldl stepW (List.ofFn x)).length = n + j := by
      rw [foldl_len, hlen_x, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    have hpref : (C.wires (List.ofFn x)).getD i false =
        ((C.gates.take j).foldl stepW (List.ofFn x)).getD i false := by
      change (C.gates.foldl stepW (List.ofFn x)).getD i false = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append]
      exact foldl_prefix (C.gates.drop j) _ i (htake_len.symm ▸ hlt)
    exact hpref.symm
  by_cases hHasEdge : ∃ (p : Fin Np) (l : Fin Nl), I p l
  · let G : SimpleGraph (Fin n) :=
      { Adj := fun u v =>
          (∃ (p : Fin Np) (l : Fin Nl), I p l ∧ u = Fin.castAdd Nl p ∧ v = Fin.natAdd Np l) ∨
          (∃ (p : Fin Np) (l : Fin Nl), I p l ∧ u = Fin.natAdd Np l ∧ v = Fin.castAdd Nl p)
        symm := ⟨fun u v h => by
          rcases h with ⟨p, l, hI, hu, hv⟩ | ⟨p, l, hI, hu, hv⟩
          · exact Or.inr ⟨p, l, hI, hv, hu⟩
          · exact Or.inl ⟨p, l, hI, hv, hu⟩⟩
        loopless := ⟨fun u h => by
          rcases h with ⟨p, l, _, hu1, hu2⟩ | ⟨p, l, _, hu1, hu2⟩
          · have h1 : u.val = p.val := congrArg Fin.val hu1
            have h2 : u.val = Np + l.val := congrArg Fin.val hu2
            omega
          · have h1 : u.val = Np + l.val := congrArg Fin.val hu1
            have h2 : u.val = p.val := congrArg Fin.val hu2
            omega⟩ }
    let B : Finset (Fin n) := Finset.univ.filter (fun u => u.val < Np)
    have hBip : ∀ u v : Fin n, G.Adj u v → (u ∈ B ↔ v ∉ B) := by
      intro u v huv
      rcases huv with ⟨p, l, _, rfl, rfl⟩ | ⟨p, l, _, rfl, rfl⟩
      · simp [B]
      · simp [B]
    have hGne : G.edgeFinset.Nonempty := by
      obtain ⟨p, l, hI⟩ := hHasEdge
      refine ⟨s(Fin.castAdd Nl p, Fin.natAdd Np l), ?_⟩
      rw [SimpleGraph.mem_edgeFinset]
      exact Or.inl ⟨p, l, hI, rfl, rfl⟩
    have hG4 : NoFourCycle G := by
      intro a b hab
      rw [Finset.card_le_one]
      intro w1 hw1 w2 hw2
      have h1 : G.Adj a w1 ∧ G.Adj b w1 := (Finset.mem_filter.mp hw1).2
      have h2 : G.Adj a w2 ∧ G.Adj b w2 := (Finset.mem_filter.mp hw2).2
      by_contra hne
      rcases h1.1 with ⟨p1, l1, hI1, ha1, hw1eq⟩ | ⟨p1, l1, hI1, ha1, hw1eq⟩
      · rcases h1.2 with ⟨p2, l1', hI2, hb1, hw1eq'⟩ | ⟨p2, l1', _, _, hw1eq'⟩
        · have hl1 : l1 = l1' := Fin.ext (by
            have := congrArg Fin.val (hw1eq.symm.trans hw1eq')
            simp at this; omega)
          subst hl1
          rcases h2.1 with ⟨p1', l2, hI3, ha2, hw2eq⟩ | ⟨_, _, _, ha2, _⟩
          · have hp1 : p1 = p1' := Fin.ext (by
              have := congrArg Fin.val (ha1.symm.trans ha2)
              simp at this; omega)
            subst hp1
            rcases h2.2 with ⟨p2', l2', hI4, hb2, hw2eq'⟩ | ⟨_, _, _, hb2, _⟩
            · have hp2 : p2 = p2' := Fin.ext (by
                have := congrArg Fin.val (hb1.symm.trans hb2)
                simp at this; omega)
              have hl2 : l2 = l2' := Fin.ext (by
                have := congrArg Fin.val (hw2eq.symm.trans hw2eq')
                simp at this; omega)
              subst hp2; subst hl2
              have hpne : p1 ≠ p2 := fun h => hab (by rw [ha1, hb1, h])
              have hlne : l1 ≠ l2 := fun h => hne (by rw [hw1eq, hw2eq, h])
              exact hNoC4 p1 p2 l1 l2 hpne hlne ⟨hI1, hI3, hI2, hI4⟩
            · have := congrArg Fin.val (hb1.symm.trans hb2); simp at this; omega
          · have := congrArg Fin.val (ha1.symm.trans ha2); simp at this; omega
        · have := congrArg Fin.val (hw1eq.symm.trans hw1eq'); simp at this; omega
      · rcases h1.2 with ⟨_, _, _, _, hw1eq'⟩ | ⟨p1', l2, hI2, hb1, hw1eq'⟩
        · have := congrArg Fin.val (hw1eq.symm.trans hw1eq'); simp at this; omega
        · have hp1 : p1 = p1' := Fin.ext (by
            have := congrArg Fin.val (hw1eq.symm.trans hw1eq')
            simp at this; omega)
          subst hp1
          rcases h2.1 with ⟨_, _, _, ha2, _⟩ | ⟨p2, l1', hI3, ha2, hw2eq⟩
          · have := congrArg Fin.val (ha1.symm.trans ha2); simp at this; omega
          · have hl1 : l1 = l1' := Fin.ext (by
              have := congrArg Fin.val (ha1.symm.trans ha2)
              simp at this; omega)
            subst hl1
            rcases h2.2 with ⟨_, _, _, hb2, _⟩ | ⟨p2', l2', hI4, hb2, hw2eq'⟩
            · have := congrArg Fin.val (hb1.symm.trans hb2); simp at this; omega
            · have hp2 : p2 = p2' := Fin.ext (by
                have := congrArg Fin.val (hw2eq.symm.trans hw2eq')
                simp at this; omega)
              have hl2 : l2 = l2' := Fin.ext (by
                have := congrArg Fin.val (hb1.symm.trans hb2)
                simp at this; omega)
              subst hp2; subst hl2
              have hpne : p1 ≠ p2 := fun h => hne (by rw [hw1eq, hw2eq, h])
              have hlne : l1 ≠ l2 := fun h => hab (by rw [ha1, hb1, h])
              exact hNoC4 p1 p2 l1 l2 hpne hlne ⟨hI1, hI2, hI3, hI4⟩
    have hGfun : ∀ z : Fin n → Bool,
        graphFun G ∅ z =
          Decidable.decide (∃ (p : Fin Np) (l : Fin Nl),
            I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) := by
      intro z
      change (decide (∃ a ∈ (∅ : Finset (Fin n)), z a = true) ||
        decide (∃ u v, G.Adj u v ∧ z u = true ∧ z v = true)) = _
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_iff]
      constructor
      · rintro ⟨u, v, huv, hu, hv⟩
        rcases huv with ⟨p, l, hI, rfl, rfl⟩ | ⟨p, l, hI, rfl, rfl⟩
        · exact ⟨p, l, hI, hu, hv⟩
        · exact ⟨p, l, hI, hv, hu⟩
      · rintro ⟨p, l, hI, hp, hl⟩
        exact ⟨Fin.castAdd Nl p, Fin.natAdd Np l, Or.inl ⟨p, l, hI, rfl, rfl⟩, hp, hl⟩
    have hFunG0 : circuitFun n C0 = graphFun G ∅ := by
      funext z
      rw [hFun0 z, hGfun z]
    have hExMin : ∃ k : ℕ, ∃ C : Circuit,
        IsAO2 n C ∧ circuitFun n C = graphFun G ∅ ∧ C.size = k :=
      ⟨C0.size, C0, hAO0, hFunG0, rfl⟩
    obtain ⟨Cmin, hAOmin, hFunmin, hSizemin⟩ := Nat.find_spec hExMin
    have hMinLe0 : Cmin.size ≤ C0.size := by
      rw [hSizemin]
      exact Nat.find_min' hExMin ⟨C0, hAO0, hFunG0, rfl⟩
    have hLeastMin : IsLeastAO G Cmin := by
      refine ⟨hAOmin, hFunmin, ?_⟩
      intro D hAOD hFunD
      rw [hSizemin]
      exact Nat.find_min' hExMin ⟨D, hAOD, hFunD, rfl⟩
    obtain ⟨C, hLeastC, hSizeCeq, hTFC⟩ := hTopForm n G Cmin hGne hLeastMin
    have hCLe0 : C.size ≤ C0.size := hSizeCeq.le.trans hMinLe0
    have hAOC : IsAO2 n C := hLeastC.1
    have hFunC : circuitFun n C = graphFun G ∅ := hLeastC.2.1
    by_cases hJ0 : junk G C = ∅
    · have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
          (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro cs; simp
        | cons g gs ih =>
          intro cs
          rw [List.foldl_cons, ih]
          change (cs ++ [_]).length + gs.length = cs.length + (gs.length + 1)
          simp; omega
      have cones_prefix : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ),
          j < cs.length → (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
        intro gs
        induction gs with
        | nil => intro cs j _; rfl
        | cons g gs ih =>
          intro cs j hj
          rw [List.foldl_cons, ih]
          · change (cs ++ [_]).getD j [] = cs.getD j []
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
          · change j < (cs ++ [_]).length
            simp; omega
      have cones_at : ∀ (j : ℕ), j < C.gates.length →
          (cones n C).getD j [] =
            (((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
              (fun w => (w - n) :: (cones n C).getD (w - n) [])) := by
        intro j hj
        change (C.gates.foldl (coneStep n) []).getD j [] =
          (((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
            (fun w => (w - n) :: (C.gates.foldl (coneStep n) []).getD (w - n) []))
        have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
          have h1 := (List.take_append_drop j C.gates).symm
          rw [List.drop_eq_getElem_cons hj] at h1
          exact h1
        have hgate : gateAt C j = C.gates[j] := by
          change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
          simp [List.getD_eq_getElem?_getD, hj]
        rw [hgate]
        have htake_len : ((C.gates.take j).foldl (coneStep n) []).length = j := by
          rw [cones_len, List.length_nil, Nat.zero_add, List.length_take,
            Nat.min_eq_left (Nat.le_of_lt hj)]
        have hstep_get :
            (C.gates.foldl (coneStep n) []).getD j [] =
              (((C.gates[j]).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
                (fun w => (w - n) :: ((C.gates.take j).foldl (coneStep n) []).getD (w - n) [])) := by
          conv_lhs => rw [hsplit]
          rw [List.foldl_append, List.foldl_cons]
          rw [cones_prefix (C.gates.drop (j + 1))]
          · change (((C.gates.take j).foldl (coneStep n) []) ++ [_]).getD j [] = _
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [htake_len])]
            simp [htake_len]
          · change j < (((C.gates.take j).foldl (coneStep n) []) ++ [_]).length
            simp [htake_len]
        rw [hstep_get]
        apply List.flatMap_congr
        intro w hw
        have hw' : n ≤ w ∧ w < n + j := by
          simpa using (List.mem_filter.mp hw).2
        have hwn : w - n < j := by omega
        have hpref : (C.gates.foldl (coneStep n) []).getD (w - n) [] =
            ((C.gates.take j).foldl (coneStep n) []).getD (w - n) [] := by
          have hsp : C.gates = C.gates.take j ++ C.gates.drop j :=
            (List.take_append_drop j C.gates).symm
          conv_lhs => rw [hsp]
          rw [List.foldl_append]
          exact cones_prefix (C.gates.drop j) _ (w - n) (htake_len.symm ▸ hwn)
        rw [hpref]
      have inCone_direct : ∀ (j u : ℕ), j < C.gates.length → u ∈ (gateAt C j).inputs →
          n ≤ u → u < n + j → InCone n C (u - n) j := by
        intro j u hj hu hnu hunj
        unfold InCone
        rw [cones_at j hj]
        rw [List.mem_flatMap]
        exact ⟨u, List.mem_filter.mpr ⟨hu, by simp [hnu, hunj]⟩, by simp⟩
      have inCone_trans : ∀ (j u k : ℕ), j < C.gates.length → u ∈ (gateAt C j).inputs →
          n ≤ u → u < n + j → InCone n C k (u - n) → InCone n C k j := by
        intro j u k hj hu hnu hunj hk
        unfold InCone at hk ⊢
        rw [cones_at j hj]
        rw [List.mem_flatMap]
        exact ⟨u, List.mem_filter.mpr ⟨hu, by simp [hnu, hunj]⟩, List.mem_cons_of_mem _ hk⟩
      have allAndBelow : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j := by
        intro j hj hop x hx
        by_contra hne
        have hf : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hne
        have hmem : j ∈ junk G C :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop, hj, x, hx, hf⟩
        rw [hJ0] at hmem
        exact Finset.notMem_empty j hmem
      let PureOr : ℕ → Prop := fun w =>
        w < n + C.gates.length ∧
          ∀ k < C.gates.length, (w = n + k ∨ (n ≤ w ∧ InCone n C k (w - n))) →
            (gateAt C k).op = GateOp.or
      have pure_down : ∀ (i u : ℕ), i < C.gates.length → PureOr (n + i) →
          u ∈ (gateAt C i).inputs → PureOr u := by
        intro i u hi hP hu
        have hlt : u < n + i := hAOC.2.1 i hi u hu
        refine ⟨by omega, ?_⟩
        intro k hk hku
        rcases hku with rfl | ⟨hnu, hck⟩
        · have hci : InCone n C k i := by
            have := inCone_direct i (n + k) hi hu (by omega) hlt
            simpa using this
          exact hP.2 k hk (Or.inr ⟨by omega, by simpa using hci⟩)
        · have hci : InCone n C k i := inCone_trans i u k hi hu hnu hlt hck
          exact hP.2 k hk (Or.inr ⟨by omega, by simpa using hci⟩)
      have pure_of_and : ∀ (j u : ℕ), j < C.gates.length → (gateAt C j).op = GateOp.and →
          u ∈ (gateAt C j).inputs → PureOr u := by
        intro j u hj hand hu
        have hlt : u < n + j := hAOC.2.1 j hj u hu
        refine ⟨by omega, ?_⟩
        intro k hk hku
        have hcj : InCone n C k j := by
          rcases hku with rfl | ⟨hnu, hck⟩
          · have := inCone_direct j (n + k) hj hu (by omega) hlt
            simpa using this
          · exact inCone_trans j u k hj hu hnu hlt hck
        have hgk : gateAt C k ∈ C.gates := by
          change C.gates.getD k ⟨GateOp.or, []⟩ ∈ C.gates
          simp [List.getD_eq_getElem?_getD, hk]
        rcases hAOC.1 (gateAt C k) hgk with handk | hork
        · exfalso
          exact hTFC k hk j hj handk (allAndBelow k hk handk) hand hcj
        · exact hork
      let S : ℕ → Finset (Fin n) := fun w =>
        Finset.univ.filter (fun p : Fin n =>
          (C.wires (List.ofFn (fun r : Fin n => decide (r = p)))).getD w false = true)
      have pure_sem : ∀ w : ℕ, PureOr w →
          (S w).Nonempty ∧
          ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true ↔
            ∃ p ∈ S w, x p = true := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hPw
          by_cases hw : w < n
          · have hmem : ⟨w, hw⟩ ∈ S w := by
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [wval_input C _ w hw]
              simp
            refine ⟨⟨⟨w, hw⟩, hmem⟩, ?_⟩
            intro x
            rw [wval_input C x w hw]
            constructor
            · intro hx
              exact ⟨⟨w, hw⟩, hmem, hx⟩
            · rintro ⟨p, hp, hxp⟩
              have hp' := (Finset.mem_filter.mp hp).2
              rw [wval_input C _ w hw] at hp'
              have heq : (⟨w, hw⟩ : Fin n) = p := by simpa using hp'
              rwa [heq]
          · have hnw : n ≤ w := Nat.le_of_not_lt hw
            let i : ℕ := w - n
            have hi : i < C.gates.length := by have := hPw.1; omega
            have hwi : w = n + i := by omega
            have hor : (gateAt C i).op = GateOp.or := hPw.2 i hi (Or.inl hwi)
            have hgi : gateAt C i ∈ C.gates := by
              change C.gates.getD i ⟨GateOp.or, []⟩ ∈ C.gates
              simp [List.getD_eq_getElem?_getD, hi]
            have hlen2 : (gateAt C i).inputs.length = 2 := hAOC.2.2 (gateAt C i) hgi
            rcases hlist : (gateAt C i).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · rw [hlist] at hlen2; simp at hlen2
            · rw [hlist] at hlen2; simp at hlen2
            · have ha_in : a ∈ (gateAt C i).inputs := by rw [hlist]; simp
              have hb_in : b ∈ (gateAt C i).inputs := by rw [hlist]; simp
              have ha_lt : a < w := by have := hAOC.2.1 i hi a ha_in; omega
              have hb_lt : b < w := by have := hAOC.2.1 i hi b hb_in; omega
              have hPa : PureOr a := pure_down i a hi (hwi ▸ hPw) ha_in
              have hPb : PureOr b := pure_down i b hi (hwi ▸ hPw) hb_in
              obtain ⟨hSa_ne, hSa_sem⟩ := ih a ha_lt hPa
              obtain ⟨_, hSb_sem⟩ := ih b hb_lt hPb
              have heval : ∀ x : Fin n → Bool,
                  (C.wires (List.ofFn x)).getD w false = true ↔
                    (C.wires (List.ofFn x)).getD a false = true ∨
                    (C.wires (List.ofFn x)).getD b false = true := by
                intro x
                rw [hwi, wval_gate C hAOC.2.1 x i hi, hor, hlist]
                change (List.map (fun w => (C.wires (List.ofFn x)).getD w false) [a, b]).any id = true ↔ _
                simp
              have hSiff : ∀ p : Fin n, p ∈ S w ↔ p ∈ S a ∨ p ∈ S b := by
                intro p
                simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
                exact heval (fun r => decide (r = p))
              refine ⟨?_, ?_⟩
              · obtain ⟨p, hp⟩ := hSa_ne
                exact ⟨p, (hSiff p).mpr (Or.inl hp)⟩
              · intro x
                rw [heval x, hSa_sem x, hSb_sem x]
                constructor
                · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
                  · exact ⟨p, (hSiff p).mpr (Or.inl hp), hx⟩
                  · exact ⟨p, (hSiff p).mpr (Or.inr hp), hx⟩
                · rintro ⟨p, hp, hx⟩
                  rcases (hSiff p).mp hp with hpa | hpb
                  · exact Or.inl ⟨p, hpa, hx⟩
                  · exact Or.inr ⟨p, hpb, hx⟩
            · rw [hlist] at hlen2; simp at hlen2
      let Pset : Finset ℕ := (Finset.range (n + C.gates.length)).filter
        (fun w => PureOr w ∧ ∀ p ∈ S w, p.val < Np)
      let Lset : Finset ℕ := (Finset.range (n + C.gates.length)).filter
        (fun w => PureOr w ∧ ∀ p ∈ S w, Np ≤ p.val)
      refine ⟨C, Pset, Lset, hAOC, ?_, hCLe0, ?_, ?_, ?_⟩
      · intro z
        have := congrFun hFunC z
        rw [this, hGfun z]
      · intro w hw
        have hwf := Finset.mem_filter.mp hw
        have hr : w ∈ Finset.range (n + C.gates.length) := hwf.1
        have hPw : PureOr w := hwf.2.1
        have hSp : ∀ p ∈ S w, p.val < Np := hwf.2.2
        by_cases hwn : w < n
        · left
          have hmem : ⟨w, hwn⟩ ∈ S w := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [wval_input C _ w hwn]
            simp
          exact hSp ⟨w, hwn⟩ hmem
        · right
          let i : ℕ := w - n
          have hi : i < C.gates.length := by
            have := Finset.mem_range.mp hr; omega
          have hwi : w = n + i := by omega
          have hor : (gateAt C i).op = GateOp.or := hPw.2 i hi (Or.inl hwi)
          refine ⟨i, hi, hwi, hor, ?_⟩
          intro u hu
          have hPu : PureOr u := pure_down i u hi (hwi ▸ hPw) hu
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hPu.1, hPu, ?_⟩
          intro p hp
          apply hSp p
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          rw [hwi, wval_gate C hAOC.2.1 _ i hi, hor]
          change (((gateAt C i).inputs.map fun w =>
            (C.wires (List.ofFn (fun r : Fin n => decide (r = p)))).getD w false).any id) = true
          simp only [List.any_eq_true, List.mem_map, id_eq]
          exact ⟨true, ⟨u, hu, hp⟩, rfl⟩
      · intro w hw
        have hwf := Finset.mem_filter.mp hw
        have hr : w ∈ Finset.range (n + C.gates.length) := hwf.1
        have hPw : PureOr w := hwf.2.1
        have hSl : ∀ p ∈ S w, Np ≤ p.val := hwf.2.2
        by_cases hwn : w < n
        · left
          have hmem : ⟨w, hwn⟩ ∈ S w := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [wval_input C _ w hwn]
            simp
          exact ⟨hSl ⟨w, hwn⟩ hmem, hwn⟩
        · right
          let i : ℕ := w - n
          have hi : i < C.gates.length := by
            have := Finset.mem_range.mp hr; omega
          have hwi : w = n + i := by omega
          have hor : (gateAt C i).op = GateOp.or := hPw.2 i hi (Or.inl hwi)
          refine ⟨i, hi, hwi, hor, ?_⟩
          intro u hu
          have hPu : PureOr u := pure_down i u hi (hwi ▸ hPw) hu
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hPu.1, hPu, ?_⟩
          intro p hp
          apply hSl p
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          rw [hwi, wval_gate C hAOC.2.1 _ i hi, hor]
          change (((gateAt C i).inputs.map fun w =>
            (C.wires (List.ofFn (fun r : Fin n => decide (r = p)))).getD w false).any id) = true
          simp only [List.any_eq_true, List.mem_map, id_eq]
          exact ⟨true, ⟨u, hu, hp⟩, rfl⟩
      · intro j hj hand
        have hgj : gateAt C j ∈ C.gates := by
          change C.gates.getD j ⟨GateOp.or, []⟩ ∈ C.gates
          simp [List.getD_eq_getElem?_getD, hj]
        have hlen2 : (gateAt C j).inputs.length = 2 := hAOC.2.2 (gateAt C j) hgj
        rcases hlist : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · rw [hlist] at hlen2; simp at hlen2
        · rw [hlist] at hlen2; simp at hlen2
        · have ha_in : a ∈ (gateAt C j).inputs := by rw [hlist]; simp
          have hb_in : b ∈ (gateAt C j).inputs := by rw [hlist]; simp
          have hPa : PureOr a := pure_of_and j a hj hand ha_in
          have hPb : PureOr b := pure_of_and j b hj hand hb_in
          obtain ⟨⟨u0, hu0⟩, hSa_sem⟩ := pure_sem a hPa
          obtain ⟨⟨v0, hv0⟩, hSb_sem⟩ := pure_sem b hPb
          have hAdj_ab : ∀ u ∈ S a, ∀ v ∈ S b, G.Adj u v := by
            intro u hu v hv
            have hgv : gateVal n C j (pairInput u v) = true := by
              change (C.wires (List.ofFn (pairInput u v))).getD (n + j) false = true
              rw [wval_gate C hAOC.2.1 (pairInput u v) j hj, hand, hlist]
              change (List.map (fun w => (C.wires (List.ofFn (pairInput u v))).getD w false) [a, b]).all id = true
              simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                Bool.and_true, Bool.and_eq_true]
              refine ⟨(hSa_sem (pairInput u v)).mpr ⟨u, hu, by change decide (u = u ∨ u = v) = true; simp⟩,
                (hSb_sem (pairInput u v)).mpr ⟨v, hv, by change decide (v = u ∨ v = v) = true; simp⟩⟩
            have hgf : graphFun G ∅ (pairInput u v) = true := allAndBelow j hj hand _ hgv
            change (decide (∃ a ∈ (∅ : Finset (Fin n)), pairInput u v a = true) ||
              decide (∃ r s, G.Adj r s ∧ pairInput u v r = true ∧ pairInput u v s = true)) = true at hgf
            simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
              Bool.false_or, decide_eq_true_iff] at hgf
            obtain ⟨r, s, hrs, hr, hs⟩ := hgf
            change decide (r = u ∨ r = v) = true at hr
            change decide (s = u ∨ s = v) = true at hs
            rw [decide_eq_true_iff] at hr hs
            rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
            · exact (G.loopless.irrefl _ hrs).elim
            · exact hrs
            · exact G.adj_symm hrs
            · exact (G.loopless.irrefl _ hrs).elim
          refine ⟨a, b, rfl, ?_⟩
          by_cases hu0p : u0.val < Np
          · left
            have hSbL : ∀ v ∈ S b, Np ≤ v.val := by
              intro v hv
              have := (hBip u0 v (hAdj_ab u0 hu0 v hv)).mp (by simp [B, hu0p])
              simp [B] at this
              exact this
            have hSaP : ∀ u ∈ S a, u.val < Np := by
              intro u hu
              have hnot := hSbL v0 hv0
              have := (hBip u v0 (hAdj_ab u hu v0 hv0)).mpr (by simp [B]; omega)
              simpa [B] using this
            exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hPa.1, hPa, hSaP⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hPb.1, hPb, hSbL⟩⟩
          · right
            have hSbP : ∀ v ∈ S b, v.val < Np := by
              intro v hv
              have := (hBip v u0 (G.adj_symm (hAdj_ab u0 hu0 v hv))).mpr (by simp [B]; omega)
              simpa [B] using this
            have hSaL : ∀ u ∈ S a, Np ≤ u.val := by
              intro u hu
              have hv0p := hSbP v0 hv0
              have := (hBip v0 u (G.adj_symm (hAdj_ab u hu v0 hv0))).mp (by simp [B, hv0p])
              simp [B] at this
              exact this
            exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hPa.1, hPa, hSaL⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hPb.1, hPb, hSbP⟩⟩
        · rw [hlist] at hlen2; simp at hlen2
    · have hCovEx : ∃ K : Finset (Fin n),
          (∀ u v : Fin n, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
          G.edgeFinset.card + K.card ≤ C.size + 1 := by
        have hJpos : 0 < (junk G C).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hJ0)
        by_cases hJ1 : (junk G C).card = 1
        · obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hJ1
          exact hOneJunk n G B C g hBip hG4 hGne hLeastC hTFC hg
        · have hJ2 : 2 ≤ (junk G C).card := by omega
          by_cases hNest : ∃ i ∈ junk G C, ∃ j ∈ junk G C, InCone n C i j
          · exact hNestedJunk n G B C hBip hG4 hGne hLeastC hTFC hJ2 hNest
          · refine hFlatJunk n G B C hBip hG4 hGne hLeastC hTFC hJ2 ?_
            intro i hi j hj hic
            exact hNest ⟨i, hi, j, hj, hic⟩
      obtain ⟨K, hKcov, hKbound⟩ := hCovEx
      let pLines : Fin Np → Finset (Fin Nl) := fun p =>
        Finset.univ.filter (fun l => I p l ∧ Fin.castAdd Nl p ∈ K)
      let lPoints : Fin Nl → Finset (Fin Np) := fun l =>
        Finset.univ.filter (fun p => I p l ∧ Fin.castAdd Nl p ∉ K)
      let KP : Finset (Fin Np) := Finset.univ.filter (fun p => (pLines p).Nonempty)
      let KL : Finset (Fin Nl) := Finset.univ.filter (fun l => (lPoints l).Nonempty)
      let blocksP : List (Bool × ℕ × List ℕ) :=
        KP.toList.map (fun p => (false, p.val, (pLines p).toList.map (fun l => Np + l.val)))
      let blocksL : List (Bool × ℕ × List ℕ) :=
        KL.toList.map (fun l => (true, Np + l.val, (lPoints l).toList.map (fun p => p.val)))
      let blocks : List (Bool × ℕ × List ℕ) := blocksP ++ blocksL
      have hBlocksCard : blocks.length ≤ K.card := by
        have hKlen : blocks.length = KP.card + KL.card := by
          simp [blocks, blocksP, blocksL]
        rw [hKlen]
        let fP : Fin Np → Fin n := Fin.castAdd Nl
        let fL : Fin Nl → Fin n := Fin.natAdd Np
        have hsubP : KP.image fP ⊆ K := by
          intro u hu
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hp).2
          exact (Finset.mem_filter.mp hl).2.2
        have hsubL : KL.image fL ⊆ K := by
          intro u hu
          obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hl).2
          have hIp := (Finset.mem_filter.mp hp).2
          have hadj : G.Adj (Fin.castAdd Nl p) (Fin.natAdd Np l) :=
            Or.inl ⟨p, l, hIp.1, rfl, rfl⟩
          exact (hKcov _ _ hadj).resolve_left hIp.2
        have hdisj : Disjoint (KP.image fP) (KL.image fL) := by
          rw [Finset.disjoint_left]
          intro u huP huL
          obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp huP
          obtain ⟨l, _, heq⟩ := Finset.mem_image.mp huL
          have := congrArg Fin.val heq
          simp [fP, fL] at this
          omega
        have hcardP : (KP.image fP).card = KP.card :=
          Finset.card_image_of_injective KP (fun a b h => Fin.ext (by simpa [fP] using congrArg Fin.val h))
        have hcardL : (KL.image fL).card = KL.card :=
          Finset.card_image_of_injective KL (fun a b h => Fin.ext (by
            have := congrArg Fin.val h; simp [fL] at this; omega))
        calc KP.card + KL.card = (KP.image fP).card + (KL.image fL).card := by rw [hcardP, hcardL]
          _ = (KP.image fP ∪ KL.image fL).card := (Finset.card_union_of_disjoint hdisj).symm
          _ ≤ K.card := Finset.card_le_card (Finset.union_subset hsubP hsubL)
      have hBlocksSum : (blocks.map (fun b => b.2.2.length)).sum = G.edgeFinset.card := by
        have hsumP : (blocksP.map (fun b => b.2.2.length)).sum = ∑ p : Fin Np, (pLines p).card := by
          simp only [blocksP, List.map_map, Function.comp_def, List.length_map, Finset.length_toList]
          have htoL : (KP.toList.map (fun p => (pLines p).card)).sum = ∑ p ∈ KP, (pLines p).card := by
            rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList KP]
            rfl
          rw [htoL]
          apply Finset.sum_subset (Finset.subset_univ KP)
          intro p _ hp
          simp only [KP, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.not_nonempty_iff_eq_empty] at hp
          simp [hp]
        have hsumL : (blocksL.map (fun b => b.2.2.length)).sum = ∑ l : Fin Nl, (lPoints l).card := by
          simp only [blocksL, List.map_map, Function.comp_def, List.length_map, Finset.length_toList]
          have htoL : (KL.toList.map (fun l => (lPoints l).card)).sum = ∑ l ∈ KL, (lPoints l).card := by
            rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList KL]
            rfl
          rw [htoL]
          apply Finset.sum_subset (Finset.subset_univ KL)
          intro l _ hl
          simp only [KL, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.not_nonempty_iff_eq_empty] at hl
          simp [hl]
        have hAllPairs :
            (∑ p : Fin Np, (pLines p).card) + (∑ l : Fin Nl, (lPoints l).card) =
              (Finset.univ.filter (fun pl : Fin Np × Fin Nl => I pl.1 pl.2)).card := by
          let E1 : Finset (Fin Np × Fin Nl) :=
            Finset.univ.filter (fun pl => I pl.1 pl.2 ∧ Fin.castAdd Nl pl.1 ∈ K)
          let E2 : Finset (Fin Np × Fin Nl) :=
            Finset.univ.filter (fun pl => I pl.1 pl.2 ∧ Fin.castAdd Nl pl.1 ∉ K)
          have hE1 : ∑ p : Fin Np, (pLines p).card = E1.card := by
            have : E1 = Finset.univ.biUnion (fun p : Fin Np => (pLines p).image (fun l => (p, l))) := by
              ext ⟨p, l⟩
              simp [E1, pLines]
            rw [this, Finset.card_biUnion]
            · apply Finset.sum_congr rfl
              intro p _
              exact (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)).symm
            · intro p1 _ p2 _ hne
              change Disjoint _ _
              rw [Finset.disjoint_left]
              intro x hx1 hx2
              obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx1
              obtain ⟨_, _, heq⟩ := Finset.mem_image.mp hx2
              exact hne (Prod.mk.inj heq).1.symm
          have hE2 : ∑ l : Fin Nl, (lPoints l).card = E2.card := by
            have : E2 = Finset.univ.biUnion (fun l : Fin Nl => (lPoints l).image (fun p => (p, l))) := by
              ext ⟨p, l⟩
              simp [E2, lPoints]
            rw [this, Finset.card_biUnion]
            · apply Finset.sum_congr rfl
              intro l _
              exact (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)).symm
            · intro l1 _ l2 _ hne
              change Disjoint _ _
              rw [Finset.disjoint_left]
              intro x hx1 hx2
              obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx1
              obtain ⟨_, _, heq⟩ := Finset.mem_image.mp hx2
              exact hne (Prod.mk.inj heq).2.symm
          have hdisjE : Disjoint E1 E2 := by
            rw [Finset.disjoint_left]
            intro pl h1 h2
            exact (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).2.2
          have hunionE : E1 ∪ E2 = Finset.univ.filter (fun pl : Fin Np × Fin Nl => I pl.1 pl.2) := by
            ext pl
            simp only [E1, E2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases hm : Fin.castAdd Nl pl.1 ∈ K <;> simp [hm]
          rw [hE1, hE2, ← Finset.card_union_of_disjoint hdisjE, hunionE]
        have hEdgeEq :
            (Finset.univ.filter (fun pl : Fin Np × Fin Nl => I pl.1 pl.2)).card =
              G.edgeFinset.card := by
          let emb : Fin Np × Fin Nl → Sym2 (Fin n) :=
            fun pl => s(Fin.castAdd Nl pl.1, Fin.natAdd Np pl.2)
          have hinj : Function.Injective emb := by
            rintro ⟨p1, l1⟩ ⟨p2, l2⟩ h
            rw [Sym2.eq_iff] at h
            rcases h with ⟨h1, h2⟩ | ⟨h1, _⟩
            · exact Prod.ext
                (Fin.ext (by simpa using congrArg Fin.val h1))
                (Fin.ext (by have := congrArg Fin.val h2; simp at this; omega))
            · have := congrArg Fin.val h1; simp at this; omega
          have himg : (Finset.univ.filter (fun pl : Fin Np × Fin Nl => I pl.1 pl.2)).image emb =
              G.edgeFinset := by
            ext e
            induction e using Sym2.ind with
            | _ u v =>
              simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
                SimpleGraph.mem_edgeFinset]
              constructor
              · rintro ⟨⟨p, l⟩, hI, he⟩
                rw [Sym2.eq_iff] at he
                rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Or.inl ⟨p, l, hI, rfl, rfl⟩
                · exact Or.inr ⟨p, l, hI, rfl, rfl⟩
              · intro huv
                rcases huv with ⟨p, l, hI, rfl, rfl⟩ | ⟨p, l, hI, rfl, rfl⟩
                · exact ⟨(p, l), hI, rfl⟩
                · exact ⟨(p, l), hI, Sym2.eq_swap⟩
          rw [← himg, Finset.card_image_of_injective _ hinj]
        rw [List.map_append, List.sum_append, hsumP, hsumL, hAllPairs, hEdgeEq]
      have hBlocksNe : blocks ≠ [] := by
        intro hnil
        have hpos : 0 < G.edgeFinset.card := Finset.card_pos.mpr hGne
        rw [← hBlocksSum, hnil] at hpos
        simp at hpos
      have hBlocksValid : ∀ b ∈ blocks,
          b.2.2 ≠ [] ∧
          ((b.1 = false ∧ b.2.1 < Np ∧ ∀ v ∈ b.2.2, Np ≤ v ∧ v < n) ∨
           (b.1 = true ∧ Np ≤ b.2.1 ∧ b.2.1 < n ∧ ∀ v ∈ b.2.2, v < Np)) := by
        intro b hb
        rw [List.mem_append] at hb
        rcases hb with hbP | hbL
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hbP
          have hp' : (pLines p).Nonempty := (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2
          refine ⟨?_, Or.inl ⟨rfl, p.isLt, ?_⟩⟩
          · intro hnil
            have : (pLines p).toList = [] := List.map_eq_nil_iff.mp hnil
            have := Finset.toList_eq_nil.mp this
            exact Finset.Nonempty.ne_empty hp' this
          · intro v hv
            obtain ⟨l, _, rfl⟩ := List.mem_map.mp hv
            exact ⟨by omega, by omega⟩
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hbL
          have hl' : (lPoints l).Nonempty := (Finset.mem_filter.mp (Finset.mem_toList.mp hl)).2
          refine ⟨?_, Or.inr ⟨rfl, by dsimp only; omega, by dsimp only; have := l.isLt; omega, ?_⟩⟩
          · intro hnil
            have : (lPoints l).toList = [] := List.map_eq_nil_iff.mp hnil
            have := Finset.toList_eq_nil.mp this
            exact Finset.Nonempty.ne_empty hl' this
          · intro v hv
            obtain ⟨p, _, rfl⟩ := List.mem_map.mp hv
            exact p.isLt
      have hBlocksSem : ∀ z : Fin n → Bool,
          (∃ b ∈ blocks, (List.ofFn z).getD b.2.1 false = true ∧
            ∃ v ∈ b.2.2, (List.ofFn z).getD v false = true) ↔
          (∃ (p : Fin Np) (l : Fin Nl),
            I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) := by
        intro z
        have hgetP : ∀ p : Fin Np, (List.ofFn z).getD p.val false = z (Fin.castAdd Nl p) := by
          intro p
          have hlt : p.val < n := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp [hlt]
          rfl
        have hgetL : ∀ l : Fin Nl, (List.ofFn z).getD (Np + l.val) false = z (Fin.natAdd Np l) := by
          intro l
          have hlt : Np + l.val < n := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp [hlt]
          rfl
        constructor
        · rintro ⟨b, hb, hcb, v, hvb, hzv⟩
          rw [List.mem_append] at hb
          rcases hb with hbP | hbL
          · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hbP
            obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hvb
            have hI : I p l := (Finset.mem_filter.mp (Finset.mem_toList.mp hl)).2.1
            exact ⟨p, l, hI, by rwa [← hgetP p], by rwa [← hgetL l]⟩
          · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hbL
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hvb
            have hI : I p l := (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2.1
            exact ⟨p, l, hI, by rwa [← hgetP p], by rwa [← hgetL l]⟩
        · rintro ⟨p, l, hI, hzp, hzl⟩
          by_cases hpK : Fin.castAdd Nl p ∈ K
          · have hlmem : l ∈ pLines p := Finset.mem_filter.mpr ⟨Finset.mem_univ l, hI, hpK⟩
            have hpmem : p ∈ KP := Finset.mem_filter.mpr ⟨Finset.mem_univ p, ⟨l, hlmem⟩⟩
            refine ⟨(false, p.val, (pLines p).toList.map (fun l' => Np + l'.val)),
              List.mem_append_left _ (List.mem_map.mpr ⟨p, Finset.mem_toList.mpr hpmem, rfl⟩),
              by rwa [hgetP p], Np + l.val,
              List.mem_map.mpr ⟨l, Finset.mem_toList.mpr hlmem, rfl⟩,
              by rwa [hgetL l]⟩
          · have hpmem : p ∈ lPoints l := Finset.mem_filter.mpr ⟨Finset.mem_univ p, hI, hpK⟩
            have hlmem : l ∈ KL := Finset.mem_filter.mpr ⟨Finset.mem_univ l, ⟨p, hpmem⟩⟩
            refine ⟨(true, Np + l.val, (lPoints l).toList.map (fun p' => p'.val)),
              List.mem_append_right _ (List.mem_map.mpr ⟨l, Finset.mem_toList.mpr hlmem, rfl⟩),
              by rwa [hgetL l], p.val,
              List.mem_map.mpr ⟨p, Finset.mem_toList.mpr hpmem, rfl⟩,
              by rwa [hgetP p]⟩
      let ValidState : List Gate → Finset ℕ → Finset ℕ → Prop := fun gs P L =>
        IsAO2 n ⟨gs, 0⟩ ∧
        (∀ w ∈ P, w < Np ∨ ∃ i < gs.length, w = n + i ∧
          (gateAt ⟨gs, 0⟩ i).op = GateOp.or ∧ ∀ u ∈ (gateAt ⟨gs, 0⟩ i).inputs, u ∈ P) ∧
        (∀ w ∈ L, (Np ≤ w ∧ w < n) ∨ ∃ i < gs.length, w = n + i ∧
          (gateAt ⟨gs, 0⟩ i).op = GateOp.or ∧ ∀ u ∈ (gateAt ⟨gs, 0⟩ i).inputs, u ∈ L) ∧
        (∀ i < gs.length, (gateAt ⟨gs, 0⟩ i).op = GateOp.and →
          ∃ a b : ℕ, (gateAt ⟨gs, 0⟩ i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)))
      have step_append_gate : ∀ (gs : List Gate) (P L : Finset ℕ) (op : GateOp) (a b : ℕ),
          ValidState gs P L → (op = GateOp.and ∨ op = GateOp.or) →
          a < n + gs.length → b < n + gs.length →
          (op = GateOp.and → (a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) →
          let gs' := gs ++ [⟨op, [a, b]⟩]
          let wNew := n + gs.length
          let P' := if op = GateOp.or ∧ a ∈ P ∧ b ∈ P then insert wNew P else P
          let L' := if op = GateOp.or ∧ a ∈ L ∧ b ∈ L then insert wNew L else L
          ValidState gs' P' L' ∧ gs'.length = gs.length + 1 ∧
          P ⊆ P' ∧ L ⊆ L' ∧
          (op = GateOp.or → a ∈ P → b ∈ P → wNew ∈ P') ∧
          (op = GateOp.or → a ∈ L → b ∈ L → wNew ∈ L') ∧
          (∀ z : Fin n → Bool, ∀ w < n + gs.length,
            (gs'.foldl stepW (List.ofFn z)).getD w false =
            (gs.foldl stepW (List.ofFn z)).getD w false) ∧
          (∀ z : Fin n → Bool,
            (gs'.foldl stepW (List.ofFn z)).getD wNew false =
              op.eval [(gs.foldl stepW (List.ofFn z)).getD a false,
                       (gs.foldl stepW (List.ofFn z)).getD b false]) := by
        intro gs P L op a b hVS hop ha hb hand
        let g : Gate := ⟨op, [a, b]⟩
        let gs' : List Gate := gs ++ [g]
        let wNew : ℕ := n + gs.length
        let P' : Finset ℕ := if op = GateOp.or ∧ a ∈ P ∧ b ∈ P then insert wNew P else P
        let L' : Finset ℕ := if op = GateOp.or ∧ a ∈ L ∧ b ∈ L then insert wNew L else L
        have hPsub : P ⊆ P' := by
          dsimp [P']; split_ifs <;> [exact Finset.subset_insert _ _; exact Finset.Subset.refl _]
        have hLsub : L ⊆ L' := by
          dsimp [L']; split_ifs <;> [exact Finset.subset_insert _ _; exact Finset.Subset.refl _]
        have hgate_old : ∀ i < gs.length, gateAt ⟨gs', 0⟩ i = gateAt ⟨gs, 0⟩ i := by
          intro i hi
          change gs'.getD i ⟨GateOp.or, []⟩ = gs.getD i ⟨GateOp.or, []⟩
          simp [gs', List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        have hgate_new : gateAt ⟨gs', 0⟩ gs.length = g := by
          change gs'.getD gs.length ⟨GateOp.or, []⟩ = g
          simp [gs', List.getD_eq_getElem?_getD]
        have hAO' : IsAO2 n ⟨gs', 0⟩ := by
          refine ⟨?_, ?_, ?_⟩
          · intro x hx
            rw [List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hVS.1.1 x hx
            · exact hop
          · intro j hj u hu
            have hj' : j < gs.length + 1 := by simpa [gs'] using hj
            by_cases hlt : j < gs.length
            · rw [hgate_old j hlt] at hu
              exact hVS.1.2.1 j hlt u hu
            · have heq : j = gs.length := by omega
              subst heq
              rw [hgate_new] at hu
              simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl <;> assumption
          · intro x hx
            rw [List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hVS.1.2.2 x hx
            · rfl
        have hP' : ∀ w ∈ P', w < Np ∨ ∃ i < gs'.length, w = n + i ∧
            (gateAt ⟨gs', 0⟩ i).op = GateOp.or ∧ ∀ u ∈ (gateAt ⟨gs', 0⟩ i).inputs, u ∈ P' := by
          intro w hw
          have hcase : w ∈ P ∨ (w = wNew ∧ op = GateOp.or ∧ a ∈ P ∧ b ∈ P) := by
            dsimp [P'] at hw
            split_ifs at hw with hcond
            · rcases Finset.mem_insert.mp hw with rfl | hwP
              · exact Or.inr ⟨rfl, hcond⟩
              · exact Or.inl hwP
            · exact Or.inl hw
          rcases hcase with hwP | ⟨rfl, hor, haP, hbP⟩
          · rcases hVS.2.1 w hwP with hlt | ⟨i, hi, hwi, hori, hini⟩
            · exact Or.inl hlt
            · exact Or.inr ⟨i, by simp [gs']; omega, hwi,
                by rw [hgate_old i hi]; exact hori,
                fun u hu => hPsub (hini u (by rwa [hgate_old i hi] at hu))⟩
          · refine Or.inr ⟨gs.length, by simp [gs'], rfl, ?_, ?_⟩
            · rw [hgate_new]; exact hor
            · rw [hgate_new]
              intro u hu
              simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl
              · exact hPsub haP
              · exact hPsub hbP
        have hL' : ∀ w ∈ L', (Np ≤ w ∧ w < n) ∨ ∃ i < gs'.length, w = n + i ∧
            (gateAt ⟨gs', 0⟩ i).op = GateOp.or ∧ ∀ u ∈ (gateAt ⟨gs', 0⟩ i).inputs, u ∈ L' := by
          intro w hw
          have hcase : w ∈ L ∨ (w = wNew ∧ op = GateOp.or ∧ a ∈ L ∧ b ∈ L) := by
            dsimp [L'] at hw
            split_ifs at hw with hcond
            · rcases Finset.mem_insert.mp hw with rfl | hwL
              · exact Or.inr ⟨rfl, hcond⟩
              · exact Or.inl hwL
            · exact Or.inl hw
          rcases hcase with hwL | ⟨rfl, hor, haL, hbL⟩
          · rcases hVS.2.2.1 w hwL with hlt | ⟨i, hi, hwi, hori, hini⟩
            · exact Or.inl hlt
            · exact Or.inr ⟨i, by simp [gs']; omega, hwi,
                by rw [hgate_old i hi]; exact hori,
                fun u hu => hLsub (hini u (by rwa [hgate_old i hi] at hu))⟩
          · refine Or.inr ⟨gs.length, by simp [gs'], rfl, ?_, ?_⟩
            · rw [hgate_new]; exact hor
            · rw [hgate_new]
              intro u hu
              simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl
              · exact hLsub haL
              · exact hLsub hbL
        have hAnd' : ∀ i < gs'.length, (gateAt ⟨gs', 0⟩ i).op = GateOp.and →
            ∃ u v : ℕ, (gateAt ⟨gs', 0⟩ i).inputs = [u, v] ∧
              ((u ∈ P' ∧ v ∈ L') ∨ (u ∈ L' ∧ v ∈ P')) := by
          intro i hi hopi
          have hi' : i < gs.length + 1 := by simpa [gs'] using hi
          by_cases hlt : i < gs.length
          · rw [hgate_old i hlt] at hopi ⊢
            obtain ⟨u, v, huv, hside⟩ := hVS.2.2.2 i hlt hopi
            exact ⟨u, v, huv, hside.imp (fun h => ⟨hPsub h.1, hLsub h.2⟩)
              (fun h => ⟨hLsub h.1, hPsub h.2⟩)⟩
          · have heq : i = gs.length := by omega
            subst heq
            rw [hgate_new] at hopi ⊢
            exact ⟨a, b, rfl, (hand hopi).imp (fun h => ⟨hPsub h.1, hLsub h.2⟩)
              (fun h => ⟨hLsub h.1, hPsub h.2⟩)⟩
        refine ⟨⟨hAO', hP', hL', hAnd'⟩, by simp, hPsub, hLsub, ?_, ?_, ?_, ?_⟩
        · intro hor haP hbP; simp [hor, haP, hbP]
        · intro hor haL hbL; simp [hor, haL, hbL]
        · intro z w hw
          rw [List.foldl_append]
          apply foldl_prefix [g]
          rw [foldl_len]; simp; omega
        · intro z
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
            rw [foldl_len]; simp
          rw [← hlen, foldl_getD_last]
          rfl
      have buildOrChain : ∀ (vs : List ℕ) (side : Bool) (gs : List Gate) (P L : Finset ℕ) (w0 : ℕ),
          ValidState gs P L → w0 < n + gs.length → (if side then w0 ∈ L else w0 ∈ P) →
          (∀ v ∈ vs, v < n + gs.length ∧ (if side then v ∈ L else v ∈ P)) →
          ∃ (gs' : List Gate) (P' L' : Finset ℕ) (wOut : ℕ),
            ValidState gs' P' L' ∧ gs'.length = gs.length + vs.length ∧
            P ⊆ P' ∧ L ⊆ L' ∧ wOut < n + gs'.length ∧ (if side then wOut ∈ L' else wOut ∈ P') ∧
            (∀ z : Fin n → Bool, ∀ w < n + gs.length,
              (gs'.foldl stepW (List.ofFn z)).getD w false =
              (gs.foldl stepW (List.ofFn z)).getD w false) ∧
            (∀ z : Fin n → Bool,
              (gs'.foldl stepW (List.ofFn z)).getD wOut false = true ↔
                (gs.foldl stepW (List.ofFn z)).getD w0 false = true ∨
                ∃ v ∈ vs, (gs.foldl stepW (List.ofFn z)).getD v false = true) := by
        intro vs
        induction vs with
        | nil =>
          intro side gs P L w0 hVS hw0 hmem _
          exact ⟨gs, P, L, w0, hVS, by simp, Finset.Subset.refl _, Finset.Subset.refl _,
            hw0, hmem, fun _ _ _ => rfl, fun _ => by simp⟩
        | cons v rest ih =>
          intro side gs P L w0 hVS hw0 hmem hvs
          have hv : v < n + gs.length ∧ (if side then v ∈ L else v ∈ P) :=
            hvs v (List.mem_cons_self ..)
          obtain ⟨hVS1, hlen1, hP1, hL1, hwP1, hwL1, hpres1, heval1⟩ :=
            step_append_gate gs P L GateOp.or w0 v hVS (Or.inr rfl) hw0 hv.1 (by simp)
          let gs1 := gs ++ [⟨GateOp.or, [w0, v]⟩]
          have hgs1len : gs1.length = gs.length + 1 := hlen1
          let w1 := n + gs.length
          let P1 := if GateOp.or = GateOp.or ∧ w0 ∈ P ∧ v ∈ P then insert w1 P else P
          let L1 := if GateOp.or = GateOp.or ∧ w0 ∈ L ∧ v ∈ L then insert w1 L else L
          have hw1_mem : if side then w1 ∈ L1 else w1 ∈ P1 := by
            cases side
            · exact hwP1 rfl hmem hv.2
            · exact hwL1 rfl hmem hv.2
          have hrest : ∀ u ∈ rest, u < n + gs1.length ∧ (if side then u ∈ L1 else u ∈ P1) := by
            intro u hu
            have hu0 := hvs u (List.mem_cons_of_mem _ hu)
            refine ⟨by omega, ?_⟩
            cases side
            · exact hP1 hu0.2
            · exact hL1 hu0.2
          obtain ⟨gs2, P2, L2, wOut, hVS2, hlen2, hP2, hL2, hwOut, hwOut_mem, hpres2, heval2⟩ :=
            ih side gs1 P1 L1 w1 hVS1 (by omega) hw1_mem hrest
          refine ⟨gs2, P2, L2, wOut, hVS2, by simp [hlen2]; omega,
            hP1.trans hP2, hL1.trans hL2, hwOut, hwOut_mem, ?_, ?_⟩
          · intro z w hw
            rw [hpres2 z w (by omega), hpres1 z w hw]
          · intro z
            rw [heval2 z]
            have hw1_eval : (gs1.foldl stepW (List.ofFn z)).getD w1 false = true ↔
                (gs.foldl stepW (List.ofFn z)).getD w0 false = true ∨
                (gs.foldl stepW (List.ofFn z)).getD v false = true := by
              rw [heval1 z]
              change ([(gs.foldl stepW (List.ofFn z)).getD w0 false,
                (gs.foldl stepW (List.ofFn z)).getD v false]).any id = true ↔ _
              simp
            rw [hw1_eval]
            constructor
            · rintro ((h0 | hv') | ⟨u, hu, hzu⟩)
              · exact Or.inl h0
              · exact Or.inr ⟨v, List.mem_cons_self .., hv'⟩
              · have hult := (hvs u (List.mem_cons_of_mem _ hu)).1
                rw [hpres1 z u hult] at hzu
                exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hzu⟩
            · rintro (h0 | ⟨u, hu, hzu⟩)
              · exact Or.inl (Or.inl h0)
              · rcases List.mem_cons.mp hu with rfl | hurest
                · exact Or.inl (Or.inr hzu)
                · have hult := (hvs u (List.mem_cons_of_mem _ hurest)).1
                  exact Or.inr ⟨u, hurest, by rwa [hpres1 z u hult]⟩
      have buildOneBlock : ∀ (b : Bool × ℕ × List ℕ) (gs : List Gate) (P L : Finset ℕ),
          ValidState gs P L →
          (∀ w < Np, w ∈ P) → (∀ w, Np ≤ w → w < n → w ∈ L) →
          b.2.2 ≠ [] →
          ((b.1 = false ∧ b.2.1 < Np ∧ ∀ v ∈ b.2.2, Np ≤ v ∧ v < n) ∨
           (b.1 = true ∧ Np ≤ b.2.1 ∧ b.2.1 < n ∧ ∀ v ∈ b.2.2, v < Np)) →
          ∃ (gs' : List Gate) (P' L' : Finset ℕ) (wAnd : ℕ),
            ValidState gs' P' L' ∧ gs'.length = gs.length + b.2.2.length ∧
            P ⊆ P' ∧ L ⊆ L' ∧ wAnd < n + gs'.length ∧
            (∀ z : Fin n → Bool, ∀ w < n + gs.length,
              (gs'.foldl stepW (List.ofFn z)).getD w false =
              (gs.foldl stepW (List.ofFn z)).getD w false) ∧
            (∀ z : Fin n → Bool,
              (gs'.foldl stepW (List.ofFn z)).getD wAnd false = true ↔
                (List.ofFn z).getD b.2.1 false = true ∧
                ∃ v ∈ b.2.2, (List.ofFn z).getD v false = true) := by
        rintro ⟨isLine, c, leaves⟩ gs P L hVS hPbase hLbase hne hside
        rcases leaves with _ | ⟨v0, vs⟩
        · exact (hne rfl).elim
        · have hv0_in : v0 ∈ v0 :: vs := List.mem_cons_self ..
          have hSideData : c < n ∧ (if isLine then c ∈ L else c ∈ P) ∧
              v0 < n ∧ (if !isLine then v0 ∈ L else v0 ∈ P) ∧
              ∀ v ∈ vs, v < n ∧ (if !isLine then v ∈ L else v ∈ P) := by
            rcases hside with ⟨rfl, hc, hvs⟩ | ⟨rfl, hc1, hc2, hvs⟩
            · dsimp only at hc hvs
              have hv0 := hvs v0 hv0_in
              refine ⟨by omega, hPbase c hc, hv0.2, hLbase v0 hv0.1 hv0.2, ?_⟩
              intro v hv
              have := hvs v (List.mem_cons_of_mem _ hv)
              exact ⟨this.2, hLbase v this.1 this.2⟩
            · dsimp only at hc1 hc2 hvs
              have hv0 := hvs v0 hv0_in
              refine ⟨hc2, hLbase c hc1 hc2, by omega, hPbase v0 hv0, ?_⟩
              intro v hv
              have := hvs v (List.mem_cons_of_mem _ hv)
              exact ⟨by omega, hPbase v this⟩
          obtain ⟨hc_lt, hc_mem, hv0_lt, hv0_mem, hvs_mem⟩ := hSideData
          obtain ⟨gs1, P1, L1, wOr, hVS1, hlen1, hP1, hL1, hwOr_lt, hwOr_mem, hpres1, heval1⟩ :=
            buildOrChain vs (!isLine) gs P L v0 hVS (by omega) hv0_mem
              (fun v hv => ⟨by have := (hvs_mem v hv).1; omega, (hvs_mem v hv).2⟩)
          have hAndSides : (c ∈ P1 ∧ wOr ∈ L1) ∨ (c ∈ L1 ∧ wOr ∈ P1) := by
            cases isLine
            · exact Or.inl ⟨hP1 hc_mem, hwOr_mem⟩
            · exact Or.inr ⟨hL1 hc_mem, hwOr_mem⟩
          obtain ⟨hVS2, hlen2, hP2, hL2, _, _, hpres2, heval2⟩ :=
            step_append_gate gs1 P1 L1 GateOp.and c wOr hVS1 (Or.inl rfl)
              (by omega) hwOr_lt (fun _ => hAndSides)
          let gs2 := gs1 ++ [⟨GateOp.and, [c, wOr]⟩]
          have hgs2len : gs2.length = gs1.length + 1 := hlen2
          let wAnd := n + gs1.length
          refine ⟨gs2,
            if GateOp.and = GateOp.or ∧ c ∈ P1 ∧ wOr ∈ P1 then insert wAnd P1 else P1,
            if GateOp.and = GateOp.or ∧ c ∈ L1 ∧ wOr ∈ L1 then insert wAnd L1 else L1,
            wAnd, hVS2, by simp; omega, hP1.trans hP2, hL1.trans hL2,
            by omega, ?_, ?_⟩
          · intro z w hw
            rw [hpres2 z w (by omega), hpres1 z w hw]
          · intro z
            rw [heval2 z]
            change ([(gs1.foldl stepW (List.ofFn z)).getD c false,
              (gs1.foldl stepW (List.ofFn z)).getD wOr false]).all id = true ↔ _
            simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true]
            rw [heval1 z]
            have hcz : (gs1.foldl stepW (List.ofFn z)).getD c false =
                (List.ofFn z).getD c false := by
              rw [hpres1 z c (by omega)]
              exact foldl_prefix gs (List.ofFn z) c (by simp [hc_lt])
            have hv0z : (gs.foldl stepW (List.ofFn z)).getD v0 false =
                (List.ofFn z).getD v0 false :=
              foldl_prefix gs (List.ofFn z) v0 (by simp [hv0_lt])
            rw [hcz, hv0z]
            constructor
            · rintro ⟨h1, h2 | ⟨v, hv, hzv⟩⟩
              · exact ⟨h1, v0, List.mem_cons_self .., h2⟩
              · have hvlt := (hvs_mem v hv).1
                rw [foldl_prefix gs (List.ofFn z) v (by simp [hvlt])] at hzv
                exact ⟨h1, v, List.mem_cons_of_mem _ hv, hzv⟩
            · rintro ⟨h1, v, hv, hzv⟩
              rcases List.mem_cons.mp hv with rfl | hvrest
              · exact ⟨h1, Or.inl hzv⟩
              · have hvlt := (hvs_mem v hvrest).1
                refine ⟨h1, Or.inr ⟨v, hvrest, ?_⟩⟩
                rwa [foldl_prefix gs (List.ofFn z) v (by simp [hvlt])]
      have buildTail : ∀ (bs : List (Bool × ℕ × List ℕ)) (gs : List Gate) (P L : Finset ℕ) (wAcc : ℕ),
          ValidState gs P L →
          (∀ w < Np, w ∈ P) → (∀ w, Np ≤ w → w < n → w ∈ L) →
          wAcc < n + gs.length →
          (∀ b ∈ bs, b.2.2 ≠ [] ∧
            ((b.1 = false ∧ b.2.1 < Np ∧ ∀ v ∈ b.2.2, Np ≤ v ∧ v < n) ∨
             (b.1 = true ∧ Np ≤ b.2.1 ∧ b.2.1 < n ∧ ∀ v ∈ b.2.2, v < Np))) →
          ∃ (gs' : List Gate) (P' L' : Finset ℕ) (wOut : ℕ),
            ValidState gs' P' L' ∧
            gs'.length = gs.length + (bs.map (fun b => b.2.2.length)).sum + bs.length ∧
            wOut < n + gs'.length ∧
            (∀ z : Fin n → Bool,
              (gs'.foldl stepW (List.ofFn z)).getD wOut false = true ↔
                (gs.foldl stepW (List.ofFn z)).getD wAcc false = true ∨
                ∃ b ∈ bs, (List.ofFn z).getD b.2.1 false = true ∧
                  ∃ v ∈ b.2.2, (List.ofFn z).getD v false = true) := by
        intro bs
        induction bs with
        | nil =>
          intro gs P L wAcc hVS _ _ hwAcc _
          exact ⟨gs, P, L, wAcc, hVS, by simp, hwAcc, fun _ => by simp⟩
        | cons b rest ih =>
          intro gs P L wAcc hVS hPbase hLbase hwAcc hbs
          have hb := hbs b (List.mem_cons_self ..)
          obtain ⟨gs1, P1, L1, wAnd, hVS1, hlen1, hP1, hL1, hwAnd, hpres1, heval1⟩ :=
            buildOneBlock b gs P L hVS hPbase hLbase hb.1 hb.2
          obtain ⟨hVS2, hlen2, hP2, hL2, _, _, hpres2, heval2⟩ :=
            step_append_gate gs1 P1 L1 GateOp.or wAcc wAnd hVS1 (Or.inr rfl)
              (by omega) hwAnd (by simp)
          let gs2 := gs1 ++ [⟨GateOp.or, [wAcc, wAnd]⟩]
          have hgs2len : gs2.length = gs1.length + 1 := hlen2
          let wOr := n + gs1.length
          let P2 := if GateOp.or = GateOp.or ∧ wAcc ∈ P1 ∧ wAnd ∈ P1 then insert wOr P1 else P1
          let L2 := if GateOp.or = GateOp.or ∧ wAcc ∈ L1 ∧ wAnd ∈ L1 then insert wOr L1 else L1
          obtain ⟨gs3, P3, L3, wOut, hVS3, hlen3, hwOut, heval3⟩ :=
            ih gs2 P2 L2 wOr hVS2
              (fun w hw => hP2 (hP1 (hPbase w hw)))
              (fun w h1 h2 => hL2 (hL1 (hLbase w h1 h2)))
              (by omega)
              (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb'))
          refine ⟨gs3, P3, L3, wOut, hVS3, ?_, hwOut, ?_⟩
          · simp only [List.map_cons, List.sum_cons, List.length_cons]
            omega
          · intro z
            rw [heval3 z, heval2 z]
            change (([(gs1.foldl stepW (List.ofFn z)).getD wAcc false,
              (gs1.foldl stepW (List.ofFn z)).getD wAnd false]).any id = true ∨ _) ↔ _
            simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
            rw [hpres1 z wAcc hwAcc, heval1 z]
            constructor
            · rintro ((hacc | hblk) | ⟨b', hb', hcb', hvb'⟩)
              · exact Or.inl hacc
              · exact Or.inr ⟨b, List.mem_cons_self .., hblk⟩
              · exact Or.inr ⟨b', List.mem_cons_of_mem _ hb', hcb', hvb'⟩
            · rintro (hacc | ⟨b', hb', hcb', hvb'⟩)
              · exact Or.inl (Or.inl hacc)
              · rcases List.mem_cons.mp hb' with rfl | hbrest
                · exact Or.inl (Or.inr ⟨hcb', hvb'⟩)
                · exact Or.inr ⟨b', hbrest, hcb', hvb'⟩
      rcases hbl : blocks with _ | ⟨b0, brest⟩
      · exact (hBlocksNe hbl).elim
      · let P0 : Finset ℕ := Finset.range Np
        let L0 : Finset ℕ := (Finset.range Nl).image (fun j => Np + j)
        have hVS0 : ValidState [] P0 L0 := by
          refine ⟨⟨fun g hg => by simp at hg, fun j hj => by simp at hj, by simp⟩, ?_, ?_, by simp⟩
          · intro w hw; exact Or.inl (Finset.mem_range.mp hw)
          · intro w hw
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
            have := Finset.mem_range.mp hj
            exact Or.inl ⟨by omega, by omega⟩
        have hP0 : ∀ w < Np, w ∈ P0 := fun w hw => Finset.mem_range.mpr hw
        have hL0 : ∀ w, Np ≤ w → w < n → w ∈ L0 := fun w h1 h2 =>
          Finset.mem_image.mpr ⟨w - Np, Finset.mem_range.mpr (by omega), by omega⟩
        have hb0 := hBlocksValid b0 (by rw [hbl]; exact List.mem_cons_self ..)
        obtain ⟨gs1, P1, L1, w1, hVS1, hlen1, hP1, hL1, hw1, _, heval1⟩ :=
          buildOneBlock b0 [] P0 L0 hVS0 hP0 hL0 hb0.1 hb0.2
        obtain ⟨gsF, PF, LF, wOut, hVSF, hlenF, _, hevalF⟩ :=
          buildTail brest gs1 P1 L1 w1 hVS1
            (fun w hw => hP1 (hP0 w hw))
            (fun w h1 h2 => hL1 (hL0 w h1 h2))
            hw1
            (fun b' hb' => hBlocksValid b' (by rw [hbl]; exact List.mem_cons_of_mem _ hb'))
        let D : Circuit := ⟨gsF, wOut⟩
        have hDlen : D.size = G.edgeFinset.card + blocks.length - 1 := by
          change gsF.length = _
          rw [← hBlocksSum, hbl]
          simp only [List.map_cons, List.sum_cons, List.length_cons] at hlenF ⊢
          simp only [List.length_nil, Nat.zero_add] at hlen1
          omega
        have hDsize : D.size ≤ C0.size := by
          have hpos : 1 ≤ blocks.length := by rw [hbl]; simp
          omega
        refine ⟨D, PF, LF, hVSF.1, ?_, hDsize, hVSF.2.1, hVSF.2.2.1, hVSF.2.2.2⟩
        intro z
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_iff]
        change (gsF.foldl stepW (List.ofFn z)).getD wOut false = true ↔ _
        rw [hevalF z, heval1 z, ← hBlocksSem z, hbl]
        constructor
        · rintro (h0 | ⟨b', hb', hcb', hvb'⟩)
          · exact ⟨b0, List.mem_cons_self .., h0⟩
          · exact ⟨b', List.mem_cons_of_mem _ hb', hcb', hvb'⟩
        · rintro ⟨b', hb', hcb', hvb'⟩
          rcases List.mem_cons.mp hb' with rfl | hbrest
          · exact Or.inl ⟨hcb', hvb'⟩
          · exact Or.inr ⟨b', hbrest, hcb', hvb'⟩
  · refine ⟨⟨[], Np + Nl⟩, ∅, ∅, ?_, ?_, Nat.zero_le _, by simp, by simp, by simp⟩
    · exact ⟨fun g hg => by simp at hg, fun j hj => by simp at hj, by simp⟩
    · intro z
      have hfalse : ¬ ∃ (p : Fin Np) (l : Fin Nl),
          I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true := by
        rintro ⟨p, l, hI, _, _⟩
        exact hHasEdge ⟨p, l, hI⟩
      change (List.ofFn z).getD (Np + Nl) false = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp), Option.getD_none]
      simp [hfalse]
