import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Reduce L-meta-612 (C4-free monotone lower bound |E| + tau - 1) to TopForm normalization
-- and the dirty-AND (junk.Nonempty) case, proving the clean (junk = empty) case outright
-- by counting star AND gates, top OR gates, and disjoint leaf-merge OR gates together.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_612_8
    (hNorm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → Monotone2 C → circuitFun n C = NestedCover.graphFun G ∅ →
      ∃ D : Circuit, IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hDirty : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty →
      (∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card) →
      IsLeastAO G D → PEqualNP.TopForm.TopForm G D → (junk G D).Nonempty →
      G.edgeFinset.card + t ≤ D.size + 1) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  intro n t G C hEdges hNoCycle _ hMin hMono hEval
  have hNonempty : G.edgeFinset.Nonempty := by
    obtain ⟨u, v, huv⟩ := hEdges
    exact ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr huv)⟩
  have hFour : NoFourCycle G := by
    intro a c hac
    apply Finset.card_le_one.mpr
    intro b hb d hd
    have hbAdj := (Finset.mem_filter.mp hb).2
    have hdAdj := (Finset.mem_filter.mp hd).2
    by_contra hbd
    exact hNoCycle a b c d hbAdj.1.ne hac hdAdj.1.ne hbAdj.2.ne.symm hbd hdAdj.2.ne
      hbAdj.1 hbAdj.2.symm hdAdj.2 hdAdj.1.symm
  have hFun : circuitFun n C = NestedCover.graphFun G ∅ := by
    funext x
    change C.eval (List.ofFn x) =
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    have hx : C.eval (List.ofFn x) = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
      cases h : C.eval (List.ofFn x) with
      | false => exact (decide_eq_false (fun he => by simpa [h] using (hEval x).mpr he)).symm
      | true => exact (decide_eq_true ((hEval x).mp h)).symm
    simpa using hx
  obtain ⟨D, hLeast, hTop, hSize⟩ := hNorm n G C hNonempty hMono hFun
  suffices hD : G.edgeFinset.card + t ≤ D.size + 1 by
    rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
    omega
  by_cases hJ : (junk G D).Nonempty
  · exact hDirty n t G D hFour hNonempty hMin hLeast hTop hJ
  have hNoJunk : junk G D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
  have hAO2 : IsAO2 n D := hLeast.1
  have hDFun : circuitFun n D = NestedCover.graphFun G ∅ := hLeast.2.1
  have hAndOr : AndOrOnly D := hAO2.1
  have hRB : ReadsBack n D := hAO2.2.1
  have hLen2 : ∀ g ∈ D.gates, g.inputs.length = 2 := hAO2.2.2
  -- Universal DAG merge bound: if base wires (not in Merge) have |S w| <= 1 and
  -- every merge wire w in Merge satisfies S w subset S a union S b for some a, b < w,
  -- then |(R.biUnion S)| <= |(Merge.filter (< K))| + |R| for all R subset range K.
  have hMerge : ∀ {α : Type} [DecidableEq α] (S : ℕ → Finset α) (Merge : Finset ℕ),
      (∀ w, w ∉ Merge → (S w).card ≤ 1) →
      (∀ w ∈ Merge, ∃ a < w, ∃ b < w, S w ⊆ S a ∪ S b) →
      ∀ (K : ℕ) (R : Finset ℕ), R ⊆ Finset.range K →
        (R.biUnion S).card ≤ (Merge.filter (· < K)).card + R.card := by
    intro α _ S Merge hBase hStep K
    induction K with
    | zero =>
      intro R hR
      have hRe : R = ∅ := Finset.subset_empty.mp (by simpa using hR)
      subst hRe
      simp
    | succ K ih =>
      intro R hR
      by_cases hKR : K ∈ R
      · have hErSub : R.erase K ⊆ Finset.range K := by
          intro x hx
          have hx1 := Finset.mem_erase.mp hx
          have hx2 := Finset.mem_range.mp (hR hx1.2)
          exact Finset.mem_range.mpr (by omega)
        have hErCard : (R.erase K).card + 1 = R.card := Finset.card_erase_add_one hKR
        by_cases hKM : K ∈ Merge
        · obtain ⟨a, ha, b, hb, hSub⟩ := hStep K hKM
          let R' : Finset ℕ := (R.erase K) ∪ ({a, b} : Finset ℕ)
          have hR'Sub : R' ⊆ Finset.range K := by
            intro x hx
            rcases Finset.mem_union.mp hx with hx1 | hx2
            · exact hErSub hx1
            · rcases Finset.mem_insert.mp hx2 with rfl | hx3
              · exact Finset.mem_range.mpr ha
              · rw [Finset.mem_singleton.mp hx3]
                exact Finset.mem_range.mpr hb
          have hBiSub : R.biUnion S ⊆ R'.biUnion S := by
            intro z hz
            obtain ⟨w, hwR, hzw⟩ := Finset.mem_biUnion.mp hz
            by_cases hwK : w = K
            · subst hwK
              rcases Finset.mem_union.mp (hSub hzw) with hza | hzb
              · exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self a {b})), hza⟩
              · exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))), hzb⟩
            · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hwK, hwR⟩)), hzw⟩
          have hR'Card : R'.card ≤ R.card + 1 := by
            have h1 : R'.card ≤ (R.erase K).card + ({a, b} : Finset ℕ).card := Finset.card_union_le _ _
            have h2 : ({a, b} : Finset ℕ).card ≤ 2 := by
              calc ({a, b} : Finset ℕ).card ≤ ({b} : Finset ℕ).card + 1 := Finset.card_insert_le a {b}
                _ = 2 := by simp
            omega
          have hFilt : (Merge.filter (· < K + 1)).card = (Merge.filter (· < K)).card + 1 := by
            have hEq : Merge.filter (· < K + 1) = insert K (Merge.filter (· < K)) := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_insert]
              constructor
              · rintro ⟨hxM, hxlt⟩
                by_cases hxK : x = K
                · exact Or.inl hxK
                · exact Or.inr ⟨hxM, by omega⟩
              · rintro (rfl | ⟨hxM, hxlt⟩)
                · exact ⟨hKM, by omega⟩
                · exact ⟨hxM, by omega⟩
            rw [hEq, Finset.card_insert_of_notMem]
            simp
          have hIH := ih R' hR'Sub
          have hBiCard : (R.biUnion S).card ≤ (R'.biUnion S).card := Finset.card_le_card hBiSub
          omega
        · have hBaseK : (S K).card ≤ 1 := hBase K hKM
          have hBiSub : R.biUnion S ⊆ (R.erase K).biUnion S ∪ S K := by
            intro z hz
            obtain ⟨w, hwR, hzw⟩ := Finset.mem_biUnion.mp hz
            by_cases hwK : w = K
            · subst hwK; exact Finset.mem_union.mpr (Or.inr hzw)
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwK, hwR⟩, hzw⟩))
          have hFiltSub : Merge.filter (· < K) ⊆ Merge.filter (· < K + 1) := by
            intro x hx
            have hx' := Finset.mem_filter.mp hx
            exact Finset.mem_filter.mpr ⟨hx'.1, by omega⟩
          have hIH := ih (R.erase K) hErSub
          have h1 : (R.biUnion S).card ≤ ((R.erase K).biUnion S).card + (S K).card :=
            (Finset.card_le_card hBiSub).trans (Finset.card_union_le _ _)
          have h2 : (Merge.filter (· < K)).card ≤ (Merge.filter (· < K + 1)).card :=
            Finset.card_le_card hFiltSub
          omega
      · have hRSub : R ⊆ Finset.range K := by
          intro x hx
          have hx1 := Finset.mem_range.mp (hR hx)
          have hxne : x ≠ K := fun h => hKR (h ▸ hx)
          exact Finset.mem_range.mpr (by omega)
        have hFiltSub : Merge.filter (· < K) ⊆ Merge.filter (· < K + 1) := by
          intro x hx
          have hx' := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hx'.1, by omega⟩
        have hIH := ih R hRSub
        have h2 : (Merge.filter (· < K)).card ≤ (Merge.filter (· < K + 1)).card :=
          Finset.card_le_card hFiltSub
        omega
  -- Wire evaluation helpers (no simp on GateOp.eval / Circuit.size / gateAt / opnd / cones / InCone).
  let wstep : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let W : List Gate → List Bool → List Bool := fun gs x => gs.foldl wstep x
  have hW_len : ∀ (gs : List Gate) (w : List Bool), (W gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; change w.length = w.length + 0; omega
    | cons g gs ih =>
      intro w
      change (W gs (wstep w g)).length = w.length + (g :: gs).length
      rw [ih (wstep w g)]
      have hl : (wstep w g).length = w.length + 1 := by
        dsimp only [wstep]; rw [List.length_append]; simp
      rw [hl, List.length_cons]
      omega
  have hW_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (W gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      change (W gs (wstep w g)).getD i false = w.getD i false
      have hl : i < (wstep w g).length := by
        dsimp only [wstep]; rw [List.length_append]; simp; omega
      rw [ih (wstep w g) i hl]
      dsimp only [wstep]
      exact List.getD_append w _ false i hi
  have hW_append : ∀ (gs1 gs2 : List Gate) (w : List Bool),
      W (gs1 ++ gs2) w = W gs2 (W gs1 w) := by
    intro gs1 gs2 w
    dsimp only [W]
    exact List.foldl_append
  have hGateAt_eq : ∀ j (hj : j < D.gates.length), gateAt D j = D.gates[j]'hj := by
    intro j hj
    change D.gates.getD j ⟨GateOp.or, []⟩ = D.gates[j]'hj
    exact List.getD_eq_getElem D.gates ⟨GateOp.or, []⟩ hj
  have hGateAt_mem : ∀ j, j < D.gates.length → gateAt D j ∈ D.gates := by
    intro j hj
    rw [hGateAt_eq j hj]
    exact List.getElem_mem hj
  have hOp_eq : ∀ j, j < D.gates.length →
      (gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or :=
    fun j hj => hAndOr (gateAt D j) (hGateAt_mem j hj)
  have hInputs_pair : ∀ j, j < D.gates.length →
      (gateAt D j).inputs = [opnd D j 0, opnd D j 1] := by
    intro j hj
    have hl : (gateAt D j).inputs.length = 2 := hLen2 (gateAt D j) (hGateAt_mem j hj)
    rcases hlist : (gateAt D j).inputs with _ | ⟨a, rest⟩
    · rw [hlist] at hl; simp at hl
    · rcases rest with _ | ⟨b, rest2⟩
      · rw [hlist] at hl; simp at hl
      · rcases rest2 with _ | ⟨c, rest3⟩
        · change [a, b] = [(gateAt D j).inputs.getD 0 0, (gateAt D j).inputs.getD 1 0]
          rw [hlist]; rfl
        · rw [hlist] at hl; simp at hl
  have hOpnd_lt : ∀ j, j < D.gates.length → ∀ b : Fin 2, opnd D j b < n + j := by
    intro j hj b
    have hmem : opnd D j b ∈ (gateAt D j).inputs := by
      rw [hInputs_pair j hj]
      fin_cases b <;> simp
    exact hRB j hj (opnd D j b) hmem
  let wval : ℕ → (Fin n → Bool) → Bool := fun w x => (D.wires (List.ofFn x)).getD w false
  have hWval_in : ∀ (i : Fin n) (x : Fin n → Bool), wval i.val x = x i := by
    intro i x
    change (W D.gates (List.ofFn x)).getD i.val false = x i
    rw [hW_prefix D.gates (List.ofFn x) i.val (by rw [List.length_ofFn]; exact i.isLt)]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt)]
    exact List.getElem_ofFn (by rw [List.length_ofFn]; exact i.isLt)
  have hWval_ge : ∀ w (hw : n + D.gates.length ≤ w) (x : Fin n → Bool), wval w x = false := by
    intro w hw x
    change (W D.gates (List.ofFn x)).getD w false = false
    rw [List.getD_eq_default]
    rw [hW_len, List.length_ofFn]
    exact hw
  have hWval_gate : ∀ j, j < D.gates.length → ∀ x : Fin n → Bool,
      wval (n + j) x =
        if (gateAt D j).op = GateOp.and then (wval (opnd D j 0) x && wval (opnd D j 1) x)
        else (wval (opnd D j 0) x || wval (opnd D j 1) x) := by
    intro j hj x
    let pre := D.gates.take j
    let post := D.gates.drop (j + 1)
    let gj := D.gates[j]'hj
    have hpre_len : pre.length = j := by
      dsimp only [pre]; rw [List.length_take]; exact min_eq_left (Nat.le_of_lt hj)
    have hsplit : D.gates = pre ++ gj :: post := by
      dsimp only [pre, post, gj]
      have h1 := (List.take_append_drop j D.gates).symm
      rw [List.drop_eq_getElem_cons hj] at h1
      exact h1
    have hgj : gj = gateAt D j := (hGateAt_eq j hj).symm
    let wpre := W pre (List.ofFn x)
    have hwpre_len : wpre.length = n + j := by
      dsimp only [wpre]; rw [hW_len, List.length_ofFn, hpre_len]
    have hD_eq : W D.gates (List.ofFn x) = W post (wstep wpre gj) := by
      rw [hsplit, hW_append]; rfl
    have hget_lt : ∀ u, u < n + j → wpre.getD u false = wval u x := by
      intro u hu
      change wpre.getD u false = (W D.gates (List.ofFn x)).getD u false
      rw [hD_eq]
      have h1 : u < (wstep wpre gj).length := by
        dsimp only [wstep]; rw [List.length_append]; simp; omega
      rw [hW_prefix post (wstep wpre gj) u h1]
      dsimp only [wstep]
      exact (List.getD_append wpre _ false u (by omega)).symm
    have hval_at : wval (n + j) x = gj.op.eval (gj.inputs.map fun i => wpre.getD i false) := by
      change (W D.gates (List.ofFn x)).getD (n + j) false = _
      rw [hD_eq]
      have h1 : n + j < (wstep wpre gj).length := by
        dsimp only [wstep]; rw [List.length_append]; simp; omega
      rw [hW_prefix post (wstep wpre gj) (n + j) h1]
      dsimp only [wstep]
      rw [← hwpre_len]
      simp
    rw [hval_at, hgj, hInputs_pair j hj]
    have h0 := hget_lt (opnd D j 0) (hOpnd_lt j hj 0)
    have h1 := hget_lt (opnd D j 1) (hOpnd_lt j hj 1)
    rw [List.map_cons, List.map_cons, List.map_nil, h0, h1]
    rcases hOp_eq j hj with hAnd | hOr
    · rw [if_pos hAnd, hAnd]
      change List.all [wval (opnd D j 0) x, wval (opnd D j 1) x] id =
        (wval (opnd D j 0) x && wval (opnd D j 1) x)
      cases wval (opnd D j 0) x <;> cases wval (opnd D j 1) x <;> rfl
    · have hne : (gateAt D j).op ≠ GateOp.and := by rw [hOr]; intro h; cases h
      rw [if_neg hne, hOr]
      change List.any [wval (opnd D j 0) x, wval (opnd D j 1) x] id =
        (wval (opnd D j 0) x || wval (opnd D j 1) x)
      cases wval (opnd D j 0) x <;> cases wval (opnd D j 1) x <;> rfl
  -- Monotonicity of wval
  have hMonoW : ∀ (w : ℕ) (x y : Fin n → Bool),
      (∀ i : Fin n, x i = true → y i = true) → wval w x = true → wval w y = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro x y hxy hwx
      by_cases hwn : w < n
      · have h1 := hWval_in ⟨w, hwn⟩ x
        have h2 := hWval_in ⟨w, hwn⟩ y
        rw [h1] at hwx
        rw [h2]
        exact hxy ⟨w, hwn⟩ hwx
      · by_cases hwg : w - n < D.gates.length
        · have hwEq : w = n + (w - n) := by omega
          rw [hwEq] at hwx ⊢
          rw [hWval_gate (w - n) hwg x] at hwx
          rw [hWval_gate (w - n) hwg y]
          have hlt0 : opnd D (w - n) 0 < w := by
            have := hOpnd_lt (w - n) hwg 0; omega
          have hlt1 : opnd D (w - n) 1 < w := by
            have := hOpnd_lt (w - n) hwg 1; omega
          by_cases hop : (gateAt D (w - n)).op = GateOp.and
          · rw [if_pos hop] at hwx ⊢
            rw [Bool.and_eq_true] at hwx ⊢
            exact ⟨ih _ hlt0 x y hxy hwx.1, ih _ hlt1 x y hxy hwx.2⟩
          · rw [if_neg hop] at hwx ⊢
            rw [Bool.or_eq_true] at hwx ⊢
            rcases hwx with h0 | h1
            · exact Or.inl (ih _ hlt0 x y hxy h0)
            · exact Or.inr (ih _ hlt1 x y hxy h1)
        · rw [hWval_ge w (by omega) x] at hwx
          cases hwx
  -- Cones characterization (for InCone)
  have hConesLen : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      have hl : (coneStep n cs g).length = cs.length + 1 := by
        change (cs ++ [_]).length = cs.length + 1
        rw [List.length_append]; simp
      rw [hl, List.length_cons]
      omega
  have hConesPrefix : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ),
      k < cs.length → (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
    intro gs
    induction gs with
    | nil => intro cs k _; rfl
    | cons g gs ih =>
      intro cs k hk
      rw [List.foldl_cons]
      have hk1 : k < (coneStep n cs g).length := by
        change k < (cs ++ [_]).length
        rw [List.length_append]; simp; omega
      rw [ih (coneStep n cs g) k hk1]
      change (cs ++ [_]).getD k [] = cs.getD k []
      exact List.getD_append cs _ [] k hk
  have hConesChar : ∀ (gs : List Gate) (i j : ℕ),
      i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
          n ≤ w ∧ w < n + j ∧ (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      let prev := gs.foldl (coneStep n) []
      have hprev_len : prev.length = gs.length := by
        dsimp only [prev]; rw [hConesLen]; simp
      have hkeep : ∀ k, k < gs.length → (coneStep n prev g).getD k [] = prev.getD k [] := by
        intro k hk
        change (prev ++ [_]).getD k [] = prev.getD k []
        exact List.getD_append prev _ [] k (by omega)
      rcases Nat.lt_trichotomy j gs.length with hlt | heq | hgt
      · have hg_eq : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
          List.getD_append gs [g] ⟨GateOp.or, []⟩ j hlt
        rw [hkeep j hlt, ih i j, hg_eq]
        constructor
        · rintro ⟨_, w, hw, hnw, hwlt, hmem⟩
          refine ⟨by rw [List.length_append]; simp; omega, w, hw, hnw, hwlt, ?_⟩
          rcases hmem with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by rw [hkeep (w - n) (by omega)]; exact h2)
        · rintro ⟨_, w, hw, hnw, hwlt, hmem⟩
          refine ⟨hlt, w, hw, hnw, hwlt, ?_⟩
          rcases hmem with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by rw [hkeep (w - n) (by omega)] at h2; exact h2)
      · subst heq
        have hg_eq : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by simp
        have hstep_at : (coneStep n prev g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + prev.length))).flatMap
              (fun w => (w - n) :: prev.getD (w - n) []) := by
          change (prev ++ [_]).getD gs.length [] = _
          rw [← hprev_len]
          simp
        rw [hstep_at, hg_eq, hprev_len]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, hnw, hwlt⟩, hmem⟩
          refine ⟨by rw [List.length_append]; simp, w, hw, hnw, hwlt, ?_⟩
          rcases hmem with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by rw [hkeep (w - n) (by omega)]; exact h2)
        · rintro ⟨_, w, hw, hnw, hwlt, hmem⟩
          refine ⟨w, ⟨hw, hnw, hwlt⟩, ?_⟩
          rcases hmem with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by rw [hkeep (w - n) (by omega)] at h2; exact h2)
      · have hlen_step : (coneStep n prev g).length = gs.length + 1 := by
          change (prev ++ [_]).length = gs.length + 1
          rw [List.length_append, hprev_len]; simp
        have hge : (coneStep n prev g).length ≤ j := by omega
        have hnone : (coneStep n prev g).getD j [] = [] := List.getD_eq_default _ _ hge
        rw [hnone]
        constructor
        · intro h; simp at h
        · rintro ⟨hjlt, _⟩
          rw [List.length_append] at hjlt
          simp at hjlt
          omega
  have hInCone_iff : ∀ i j, InCone n D i j ↔
      j < D.gates.length ∧ ∃ w ∈ (gateAt D j).inputs,
        n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n D i (w - n)) := by
    intro i j
    exact hConesChar D.gates i j
  have hInCone_lt : ∀ i j, InCone n D i j → i < j := by
    intro i j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hij
      obtain ⟨_, w, _, hnw, hwlt, hmem⟩ := (hInCone_iff i j).mp hij
      rcases hmem with rfl | hrec
      · omega
      · have h1 := ih (w - n) (by omega) hrec
        omega
  -- Every AND gate in D is BelowF (since junk G D = empty)
  have hAndBelowF : ∀ j, j < D.gates.length → (gateAt D j).op = GateOp.and → BelowF G D j := by
    intro j hj hop x hgx
    by_contra hnf
    have hf : NestedCover.graphFun G ∅ x = false := Bool.eq_false_iff.mpr hnf
    have hdirty : IsDirtyAnd n G D j := ⟨hop, hj, x, hgx, hf⟩
    have hmem : j ∈ junk G D := by
      change j ∈ (Finset.range D.gates.length).filter (fun k => IsDirtyAnd n G D k)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hdirty⟩
    rw [hNoJunk] at hmem
    exact Finset.notMem_empty j hmem
  -- graphFun G empty facts
  have hGraphFun_iff : ∀ x : Fin n → Bool,
      NestedCover.graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    simp
  have hGraphFun_one : ∀ u : Fin n, NestedCover.graphFun G ∅ (fun k => decide (k = u)) = false := by
    intro u
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨a, b, hab, ha, hb⟩ := (hGraphFun_iff _).mp h
    have ha' : a = u := of_decide_eq_true ha
    have hb' : b = u := of_decide_eq_true hb
    subst ha'; subst hb'
    exact G.loopless.irrefl _ hab
  have hGraphFun_pair : ∀ u v : Fin n,
      NestedCover.graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    intro u v
    rw [hGraphFun_iff]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      have ha' : a = u ∨ a = v := of_decide_eq_true ha
      have hb' : b = u ∨ b = v := of_decide_eq_true hb
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact absurd hab (G.loopless.irrefl _)
      · exact hab
      · exact hab.symm
      · exact absurd hab (G.loopless.irrefl _)
    · intro huv
      exact ⟨u, v, huv, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
  -- 1-hot support S(w)
  let S : ℕ → Finset (Fin n) :=
    fun w => Finset.univ.filter fun u => wval w (fun k => decide (k = u)) = true
  have hS_in : ∀ i : Fin n, S i.val = {i} := by
    intro i
    ext u
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hWval_in i]
    simp [eq_comm]
  have hS_and : ∀ j, j < D.gates.length → (gateAt D j).op = GateOp.and → S (n + j) = ∅ := by
    intro j hj hop
    ext u
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro h
    have hbf := hAndBelowF j hj hop (fun k => decide (k = u)) h
    rw [hGraphFun_one u] at hbf
    cases hbf
  have hS_or : ∀ j, j < D.gates.length → (gateAt D j).op = GateOp.or →
      S (n + j) = S (opnd D j 0) ∪ S (opnd D j 1) := by
    intro j hj hop
    have hne : (gateAt D j).op ≠ GateOp.and := by rw [hop]; intro h; cases h
    ext u
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [hWval_gate j hj, if_neg hne, Bool.or_eq_true]
  have hS_true_of_mem : ∀ (w : ℕ) (u : Fin n) (x : Fin n → Bool),
      u ∈ S w → x u = true → wval w x = true := by
    intro w u x hu hxu
    have h1 : wval w (fun k => decide (k = u)) = true := (Finset.mem_filter.mp hu).2
    apply hMonoW w (fun k => decide (k = u)) x _ h1
    intro k hk
    have hku : k = u := of_decide_eq_true hk
    subst hku; exact hxu
  -- Every AND gate's two sides form a star of G (disjoint, cross-adjacent, one side card <= 1)
  have hAndStar : ∀ j, j < D.gates.length → (gateAt D j).op = GateOp.and →
      Disjoint (S (opnd D j 0)) (S (opnd D j 1)) ∧
      (∀ u ∈ S (opnd D j 0), ∀ v ∈ S (opnd D j 1), G.Adj u v) ∧
      ((S (opnd D j 0)).card ≤ 1 ∨ (S (opnd D j 1)).card ≤ 1) := by
    intro j hj hop
    have hAdj : ∀ u ∈ S (opnd D j 0), ∀ v ∈ S (opnd D j 1), G.Adj u v := by
      intro u hu v hv
      have h0 : wval (opnd D j 0) (pairInput u v) = true :=
        hS_true_of_mem _ u _ hu (decide_eq_true (Or.inl rfl))
      have h1 : wval (opnd D j 1) (pairInput u v) = true :=
        hS_true_of_mem _ v _ hv (decide_eq_true (Or.inr rfl))
      have hgj : wval (n + j) (pairInput u v) = true := by
        rw [hWval_gate j hj, if_pos hop, h0, h1]; rfl
      exact (hGraphFun_pair u v).mp (hAndBelowF j hj hop (pairInput u v) hgj)
    have hDisj : Disjoint (S (opnd D j 0)) (S (opnd D j 1)) := by
      rw [Finset.disjoint_left]
      intro u hu0 hu1
      exact G.loopless.irrefl u (hAdj u hu0 u hu1)
    have hCard : (S (opnd D j 0)).card ≤ 1 ∨ (S (opnd D j 1)).card ≤ 1 := by
      by_contra h
      push Not at h
      obtain ⟨u1, u2, hu1, hu2, hune⟩ := Finset.one_lt_card_iff.mp h.1
      obtain ⟨v1, v2, hv1, hv2, hvne⟩ := Finset.one_lt_card_iff.mp h.2
      have hle := hFour u1 u2 hune
      have hm1 : v1 ∈ Finset.univ.filter (fun w => G.Adj u1 w ∧ G.Adj u2 w) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ v1, hAdj u1 hu1 v1 hv1, hAdj u2 hu2 v1 hv1⟩
      have hm2 : v2 ∈ Finset.univ.filter (fun w => G.Adj u1 w ∧ G.Adj u2 w) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ v2, hAdj u1 hu1 v2 hv2, hAdj u2 hu2 v2 hv2⟩
      exact hvne (Finset.card_le_one.mp hle v1 hm1 v2 hm2)
    exact ⟨hDisj, hAdj, hCard⟩
  -- Pure-OR wire evaluation: if no AND gate is at w or in w's cone, then wval w x = true <-> exists u in S w, x u = true.
  have hPureOrEval : ∀ w, w < n + D.gates.length →
      (∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
        w ≠ n + i ∧ ∀ k, w = n + k → ¬ InCone n D i k) →
      ∀ x : Fin n → Bool, wval w x = true ↔ ∃ u ∈ S w, x u = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hno x
      by_cases hwn : w < n
      · let u : Fin n := ⟨w, hwn⟩
        rw [hWval_in u x, hS_in u]
        simp
      · let k := w - n
        have hwk : w = n + k := by omega
        have hklt : k < D.gates.length := by omega
        have hkOr : (gateAt D k).op = GateOp.or := by
          rcases hOp_eq k hklt with hAnd | hOr
          · exact absurd hwk (hno k hklt hAnd).1
          · exact hOr
        have hne : (gateAt D k).op ≠ GateOp.and := by rw [hkOr]; intro h; cases h
        have hno_opnd : ∀ b : Fin 2, ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
            opnd D k b ≠ n + i ∧ ∀ k', opnd D k b = n + k' → ¬ InCone n D i k' := by
          intro b i hi hopi
          have hmem : opnd D k b ∈ (gateAt D k).inputs := by
            rw [hInputs_pair k hklt]; fin_cases b <;> simp
          have hltb : opnd D k b < n + k := hOpnd_lt k hklt b
          constructor
          · intro heq
            have hic : InCone n D i k := (hInCone_iff i k).mpr
              ⟨hklt, opnd D k b, hmem, by omega, hltb, Or.inl (by omega)⟩
            exact (hno i hi hopi).2 k hwk hic
          · intro k' heq hic'
            have hic : InCone n D i k := (hInCone_iff i k).mpr
              ⟨hklt, opnd D k b, hmem, by omega, hltb, Or.inr (by rw [heq, Nat.add_sub_cancel_left]; exact hic')⟩
            exact (hno i hi hopi).2 k hwk hic
        have hlt0 : opnd D k 0 < w := by have := hOpnd_lt k hklt 0; omega
        have hlt1 : opnd D k 1 < w := by have := hOpnd_lt k hklt 1; omega
        rw [hwk, hWval_gate k hklt x, if_neg hne, Bool.or_eq_true, hS_or k hklt hkOr]
        rw [ih _ hlt0 (by omega) (hno_opnd 0) x, ih _ hlt1 (by omega) (hno_opnd 1) x]
        constructor
        · rintro (⟨u, hu, hxu⟩ | ⟨u, hu, hxu⟩)
          · exact ⟨u, Finset.mem_union.mpr (Or.inl hu), hxu⟩
          · exact ⟨u, Finset.mem_union.mpr (Or.inr hu), hxu⟩
        · rintro ⟨u, hu, hxu⟩
          rcases Finset.mem_union.mp hu with hu0 | hu1
          · exact Or.inl ⟨u, hu0, hxu⟩
          · exact Or.inr ⟨u, hu1, hxu⟩
  -- Every operand of an AND gate is pure-OR (by TopForm + hAndBelowF)
  have hAndOpndPure : ∀ j, j < D.gates.length → (gateAt D j).op = GateOp.and → ∀ b : Fin 2,
      ∀ x : Fin n → Bool, wval (opnd D j b) x = true ↔ ∃ u ∈ S (opnd D j b), x u = true := by
    intro j hj hop b x
    have hltb : opnd D j b < n + j := hOpnd_lt j hj b
    have hmem : opnd D j b ∈ (gateAt D j).inputs := by
      rw [hInputs_pair j hj]; fin_cases b <;> simp
    apply hPureOrEval (opnd D j b) (by omega) _ x
    intro i hi hopi
    have hbfi : BelowF G D i := hAndBelowF i hi hopi
    constructor
    · intro heq
      have hic : InCone n D i j := (hInCone_iff i j).mpr
        ⟨hj, opnd D j b, hmem, by omega, hltb, Or.inl (by omega)⟩
      exact hTop i hi j hj hopi hbfi hop hic
    · intro k' heq hic'
      have hic : InCone n D i j := (hInCone_iff i j).mpr
        ⟨hj, opnd D j b, hmem, by omega, hltb, Or.inr (by rw [heq, Nat.add_sub_cancel_left]; exact hic')⟩
      exact hTop i hi j hj hopi hbfi hop hic
  -- Output wire is BelowF (so S D.output = empty and n <= D.output < n + D.gates.length)
  have hOutEval : ∀ x : Fin n → Bool, wval D.output x = NestedCover.graphFun G ∅ x := by
    intro x
    exact congrFun hDFun x
  have hOutLt : D.output < n + D.gates.length := by
    obtain ⟨u, v, huv⟩ := hEdges
    by_contra hge
    have h0 := hWval_ge D.output (by omega) (pairInput u v)
    rw [hOutEval, (hGraphFun_pair u v).mpr huv] at h0
    cases h0
  have hOutS : S D.output = ∅ := by
    ext u
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rw [hOutEval, hGraphFun_one u]
    intro h; cases h
  -- BelowF wires (S w = empty): reachable AND gates
  let andReach : ℕ → Finset ℕ := fun w =>
    if w < n then ∅
    else (Finset.range D.gates.length).filter fun i =>
      (gateAt D i).op = GateOp.and ∧ (w = n + i ∨ InCone n D i (w - n))
  have hAndReach_and : ∀ i, i < D.gates.length → (gateAt D i).op = GateOp.and →
      andReach (n + i) = {i} := by
    intro i hi hopi
    ext k
    dsimp only [andReach]
    rw [if_neg (by omega), Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hopk, heq | hic⟩
      · omega
      · rw [Nat.add_sub_cancel_left] at hic
        exact absurd hic (hTop k hk i hi hopk (hAndBelowF k hk hopk) hopi)
    · rintro rfl
      exact ⟨hi, hopi, Or.inl rfl⟩
  have hAndReach_or : ∀ j, j < D.gates.length → (gateAt D j).op = GateOp.or →
      andReach (n + j) ⊆ andReach (opnd D j 0) ∪ andReach (opnd D j 1) := by
    intro j hj hopj i hi
    dsimp only [andReach] at hi
    rw [if_neg (by omega), Finset.mem_filter, Finset.mem_range] at hi
    rcases hi with ⟨hilt, hopi, heq | hic⟩
    · have hjeq : j = i := by omega
      subst hjeq
      rw [hopj] at hopi; cases hopi
    · rw [Nat.add_sub_cancel_left] at hic
      obtain ⟨_, w, hw, hnw, hwlt, hmem⟩ := (hInCone_iff i j).mp hic
      rw [hInputs_pair j hj] at hw
      have hSub : ∀ b : Fin 2, w = opnd D j b → i ∈ andReach (opnd D j b) := by
        intro b hwb
        rw [← hwb]
        dsimp only [andReach]
        rw [if_neg (by omega), Finset.mem_filter, Finset.mem_range]
        refine ⟨hilt, hopi, ?_⟩
        rcases hmem with h1 | h2
        · exact Or.inl (by omega)
        · exact Or.inr h2
      rcases List.mem_cons.mp hw with h0 | hw'
      · exact Finset.mem_union.mpr (Or.inl (hSub 0 h0))
      · rcases List.mem_cons.mp hw' with h1 | hnil
        · exact Finset.mem_union.mpr (Or.inr (hSub 1 h1))
        · cases hnil
  have hBelowEval : ∀ w, w < n + D.gates.length → S w = ∅ →
      ∀ x : Fin n → Bool, wval w x = true → ∃ i ∈ andReach w, wval (n + i) x = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hSw x hwx
      by_cases hwn : w < n
      · have h1 := hS_in ⟨w, hwn⟩
        rw [hSw] at h1
        exact absurd (Finset.mem_singleton_self (⟨w, hwn⟩ : Fin n)) (by rw [← h1]; simp)
      · let j := w - n
        have hwj : w = n + j := by omega
        have hjlt : j < D.gates.length := by omega
        rcases hOp_eq j hjlt with hAnd | hOr
        · refine ⟨j, ?_, by rw [← hwj]; exact hwx⟩
          rw [hwj, hAndReach_and j hjlt hAnd]
          exact Finset.mem_singleton_self j
        · have hne : (gateAt D j).op ≠ GateOp.and := by rw [hOr]; intro h; cases h
          have hS01 : S (opnd D j 0) ∪ S (opnd D j 1) = ∅ := by
            rw [← hS_or j hjlt hOr, ← hwj, hSw]
          have hS0 : S (opnd D j 0) = ∅ := Finset.union_eq_empty.mp hS01 |>.1
          have hS1 : S (opnd D j 1) = ∅ := Finset.union_eq_empty.mp hS01 |>.2
          rw [hwj, hWval_gate j hjlt x, if_neg hne, Bool.or_eq_true] at hwx
          have hlt0 : opnd D j 0 < w := by have := hOpnd_lt j hjlt 0; omega
          have hlt1 : opnd D j 1 < w := by have := hOpnd_lt j hjlt 1; omega
          rcases hwx with h0 | h1
          · obtain ⟨i, hi, hix⟩ := ih _ hlt0 (by omega) hS0 x h0
            have hi' : i ∈ andReach (n + j) := by
              dsimp only [andReach] at hi ⊢
              rw [if_neg (by omega), Finset.mem_filter, Finset.mem_range]
              by_cases h0n : opnd D j 0 < n
              · rw [if_pos h0n] at hi; exact absurd hi (Finset.notMem_empty i)
              · rw [if_neg h0n, Finset.mem_filter, Finset.mem_range] at hi
                refine ⟨hi.1, hi.2.1, Or.inr ?_⟩
                rw [Nat.add_sub_cancel_left]
                have hmem0 : opnd D j 0 ∈ (gateAt D j).inputs := by rw [hInputs_pair j hjlt]; simp
                refine (hInCone_iff i j).mpr ⟨hjlt, opnd D j 0, hmem0, by omega, hOpnd_lt j hjlt 0, ?_⟩
                rcases hi.2.2 with heq | hic
                · exact Or.inl (by omega)
                · exact Or.inr hic
            exact ⟨i, by rw [hwj]; exact hi', hix⟩
          · obtain ⟨i, hi, hix⟩ := ih _ hlt1 (by omega) hS1 x h1
            have hi' : i ∈ andReach (n + j) := by
              dsimp only [andReach] at hi ⊢
              rw [if_neg (by omega), Finset.mem_filter, Finset.mem_range]
              by_cases h1n : opnd D j 1 < n
              · rw [if_pos h1n] at hi; exact absurd hi (Finset.notMem_empty i)
              · rw [if_neg h1n, Finset.mem_filter, Finset.mem_range] at hi
                refine ⟨hi.1, hi.2.1, Or.inr ?_⟩
                rw [Nat.add_sub_cancel_left]
                have hmem1 : opnd D j 1 ∈ (gateAt D j).inputs := by rw [hInputs_pair j hjlt]; simp
                refine (hInCone_iff i j).mpr ⟨hjlt, opnd D j 1, hmem1, by omega, hOpnd_lt j hjlt 1, ?_⟩
                rcases hi.2.2 with heq | hic
                · exact Or.inl (by omega)
                · exact Or.inr hic
            exact ⟨i, by rw [hwj]; exact hi', hix⟩
  -- Define A0 (active star-AND gates reachable from D.output), OT (BelowF OR gates), and centers
  let A0 : Finset ℕ := (andReach D.output).filter fun i =>
    (S (opnd D i 0)).Nonempty ∧ (S (opnd D i 1)).Nonempty
  have hA0_lt : ∀ i ∈ A0, i < D.gates.length := by
    intro i hi
    have h1 := (Finset.mem_filter.mp hi).1
    dsimp only [andReach] at h1
    by_cases hon : D.output < n
    · rw [if_pos hon] at h1; exact absurd h1 (Finset.notMem_empty i)
    · rw [if_neg hon, Finset.mem_filter, Finset.mem_range] at h1
      exact h1.1
  have hA0_and : ∀ i ∈ A0, (gateAt D i).op = GateOp.and := by
    intro i hi
    have h1 := (Finset.mem_filter.mp hi).1
    dsimp only [andReach] at h1
    by_cases hon : D.output < n
    · rw [if_pos hon] at h1; exact absurd h1 (Finset.notMem_empty i)
    · rw [if_neg hon, Finset.mem_filter, Finset.mem_range] at h1
      exact h1.2.1
  -- Center and leaf wire of each i in A0
  have hCenterSpec : ∀ i, i ∈ A0 →
      ∃ (c : Fin n) (leafW : ℕ),
        leafW < n + D.gates.length ∧
        (∀ v ∈ S leafW, G.Adj c v) ∧
        (∀ u v : Fin n, wval (n + i) (pairInput u v) = true →
          (u = c ∧ v ∈ S leafW) ∨ (v = c ∧ u ∈ S leafW)) := by
    intro i hi
    have hilt := hA0_lt i hi
    have hopi := hA0_and i hi
    have hne0 := (Finset.mem_filter.mp hi).2.1
    have hne1 := (Finset.mem_filter.mp hi).2.2
    obtain ⟨hDisj, hAdj, hCard⟩ := hAndStar i hilt hopi
    have hEvalPair : ∀ u v : Fin n, wval (n + i) (pairInput u v) = true →
        (u ∈ S (opnd D i 0) ∧ v ∈ S (opnd D i 1)) ∨ (v ∈ S (opnd D i 0) ∧ u ∈ S (opnd D i 1)) := by
      intro u v htr
      rw [hWval_gate i hilt, if_pos hopi, Bool.and_eq_true] at htr
      obtain ⟨p, hp, hpu⟩ := (hAndOpndPure i hilt hopi 0 (pairInput u v)).mp htr.1
      obtain ⟨q, hq, hqv⟩ := (hAndOpndPure i hilt hopi 1 (pairInput u v)).mp htr.2
      have hp' : p = u ∨ p = v := of_decide_eq_true hpu
      have hq' : q = u ∨ q = v := of_decide_eq_true hqv
      rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
      · exact absurd hq (Finset.disjoint_left.mp hDisj hp)
      · exact Or.inl ⟨hp, hq⟩
      · exact Or.inr ⟨hp, hq⟩
      · exact absurd hq (Finset.disjoint_left.mp hDisj hp)
    rcases hCard with h0 | h1
    · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (le_antisymm h0 (Finset.Nonempty.card_pos hne0))
      refine ⟨c, opnd D i 1, by have := hOpnd_lt i hilt 1; omega, ?_, ?_⟩
      · intro v hv; exact hAdj c (by rw [hc]; simp) v hv
      · intro u v htr
        rcases hEvalPair u v htr with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · rw [hc, Finset.mem_singleton] at hu; exact Or.inl ⟨hu, hv⟩
        · rw [hc, Finset.mem_singleton] at hv; exact Or.inr ⟨hv, hu⟩
    · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (le_antisymm h1 (Finset.Nonempty.card_pos hne1))
      refine ⟨c, opnd D i 0, by have := hOpnd_lt i hilt 0; omega, ?_, ?_⟩
      · intro v hv; exact (hAdj v hv c (by rw [hc]; simp)).symm
      · intro u v htr
        rcases hEvalPair u v htr with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · rw [hc, Finset.mem_singleton] at hv; exact Or.inr ⟨hv, hu⟩
        · rw [hc, Finset.mem_singleton] at hu; exact Or.inl ⟨hu, hv⟩
  let cen : ∀ i ∈ A0, Fin n := fun i hi => Classical.choose (hCenterSpec i hi)
  let leafW : ∀ i ∈ A0, ℕ := fun i hi => Classical.choose (Classical.choose_spec (hCenterSpec i hi))
  have hCL_spec : ∀ i (hi : i ∈ A0),
      leafW i hi < n + D.gates.length ∧
      (∀ v ∈ S (leafW i hi), G.Adj (cen i hi) v) ∧
      (∀ u v : Fin n, wval (n + i) (pairInput u v) = true →
        (u = cen i hi ∧ v ∈ S (leafW i hi)) ∨ (v = cen i hi ∧ u ∈ S (leafW i hi))) :=
    fun i hi => Classical.choose_spec (Classical.choose_spec (hCenterSpec i hi))
  -- Every edge of G is covered by some i in A0
  have hEdgeCov : ∀ u v : Fin n, G.Adj u v →
      ∃ i, ∃ hi : i ∈ A0,
        (u = cen i hi ∧ v ∈ S (leafW i hi)) ∨ (v = cen i hi ∧ u ∈ S (leafW i hi)) := by
    intro u v huv
    have hout : wval D.output (pairInput u v) = true := by
      rw [hOutEval]; exact (hGraphFun_pair u v).mpr huv
    obtain ⟨i, hiR, hix⟩ := hBelowEval D.output hOutLt hOutS (pairInput u v) hout
    have hiA0 : i ∈ A0 := by
      have hilt : i < D.gates.length := by
        dsimp only [andReach] at hiR
        by_cases hon : D.output < n
        · rw [if_pos hon] at hiR; exact absurd hiR (Finset.notMem_empty i)
        · rw [if_neg hon, Finset.mem_filter, Finset.mem_range] at hiR; exact hiR.1
      have hopi : (gateAt D i).op = GateOp.and := by
        dsimp only [andReach] at hiR
        by_cases hon : D.output < n
        · rw [if_pos hon] at hiR; exact absurd hiR (Finset.notMem_empty i)
        · rw [if_neg hon, Finset.mem_filter, Finset.mem_range] at hiR; exact hiR.2.1
      rw [hWval_gate i hilt, if_pos hopi, Bool.and_eq_true] at hix
      obtain ⟨p, hp, _⟩ := (hAndOpndPure i hilt hopi 0 (pairInput u v)).mp hix.1
      obtain ⟨q, hq, _⟩ := (hAndOpndPure i hilt hopi 1 (pairInput u v)).mp hix.2
      exact Finset.mem_filter.mpr ⟨hiR, ⟨p, hp⟩, ⟨q, hq⟩⟩
    exact ⟨i, hiA0, (hCL_spec i hiA0).2.2 u v hix⟩
  -- Set of centers T is a vertex cover of G, so t <= T.card <= A0.card
  let T : Finset (Fin n) := A0.attach.image fun p => cen p.1 p.2
  have hT_vc : CoverPromise.IsVertexCover G T := by
    intro u v huv
    obtain ⟨i, hi, hcov⟩ := hEdgeCov u v huv
    have hmemT : cen i hi ∈ T :=
      Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_attach A0 ⟨i, hi⟩, rfl⟩
    rcases hcov with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl hmemT
    · exact Or.inr hmemT
  have ht_le_A0 : t ≤ A0.card := by
    have h1 := hMin T hT_vc
    have h2 : T.card ≤ A0.attach.card := Finset.card_image_le
    rw [Finset.card_attach] at h2
    omega
  -- Count 1: OT = BelowF OR gates; prove A0.card <= OT.card + 1 via hMerge!
  let OT : Finset ℕ := (Finset.range D.gates.length).filter fun j =>
    (gateAt D j).op = GateOp.or ∧ S (n + j) = ∅
  let MergeOT : Finset ℕ := OT.image (fun j => n + j)
  let SOT : ℕ → Finset ℕ := fun w => if S w = ∅ then andReach w ∩ A0 else ∅
  have hA0_le_OT : A0.card ≤ OT.card + 1 := by
    have hBase : ∀ w, w ∉ MergeOT → (SOT w).card ≤ 1 := by
      intro w hw
      dsimp only [SOT]
      by_cases hSw : S w = ∅
      · rw [if_pos hSw]
        by_cases hwn : w < n
        · have h1 := hS_in ⟨w, hwn⟩; rw [hSw] at h1
          exact absurd (Finset.mem_singleton_self (⟨w, hwn⟩ : Fin n)) (by rw [← h1]; simp)
        · by_cases hwg : w - n < D.gates.length
          · rcases hOp_eq (w - n) hwg with hAnd | hOr
            · have hwEq : w = n + (w - n) := by omega
              rw [hwEq, hAndReach_and (w - n) hwg hAnd]
              exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
            · exfalso
              apply hw
              refine Finset.mem_image.mpr ⟨w - n, ?_, by omega⟩
              exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwg, hOr, by
                have hwEq : n + (w - n) = w := by omega
                rw [hwEq]; exact hSw⟩
          · have hEmp : andReach w = ∅ := by
              ext i
              dsimp only [andReach]
              rw [if_neg hwn, Finset.mem_filter, Finset.mem_range]
              simp only [Finset.notMem_empty, iff_false, not_and]
              intro hilt _ hmem
              rcases hmem with heq | hic
              · omega
              · have := (hInCone_iff i (w - n)).mp hic
                omega
            rw [hEmp]; simp
      · rw [if_neg hSw]; simp
    have hStep : ∀ w ∈ MergeOT, ∃ a < w, ∃ b < w, SOT w ⊆ SOT a ∪ SOT b := by
      intro w hw
      obtain ⟨j, hjOT, rfl⟩ := Finset.mem_image.mp hw
      have hjf := Finset.mem_filter.mp hjOT
      have hjlt : j < D.gates.length := Finset.mem_range.mp hjf.1
      have hjOr : (gateAt D j).op = GateOp.or := hjf.2.1
      have hjS : S (n + j) = ∅ := hjf.2.2
      have hS01 : S (opnd D j 0) ∪ S (opnd D j 1) = ∅ := by rw [← hS_or j hjlt hjOr, hjS]
      have hS0 : S (opnd D j 0) = ∅ := (Finset.union_eq_empty.mp hS01).1
      have hS1 : S (opnd D j 1) = ∅ := (Finset.union_eq_empty.mp hS01).2
      refine ⟨opnd D j 0, hOpnd_lt j hjlt 0, opnd D j 1, hOpnd_lt j hjlt 1, ?_⟩
      intro i hi
      dsimp only [SOT] at hi ⊢
      rw [if_pos hjS, Finset.mem_inter] at hi
      rw [if_pos hS0, if_pos hS1]
      rcases Finset.mem_union.mp (hAndReach_or j hjlt hjOr hi.1) with h0 | h1
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨h0, hi.2⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨h1, hi.2⟩))
    have hBound := hMerge SOT MergeOT hBase hStep (n + D.gates.length) {D.output}
      (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hOutLt))
    have hBi : ({D.output} : Finset ℕ).biUnion SOT = A0 := by
      rw [Finset.singleton_biUnion]
      dsimp only [SOT]
      rw [if_pos hOutS]
      exact Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [hBi, Finset.card_singleton] at hBound
    have hMC : (MergeOT.filter (· < n + D.gates.length)).card ≤ OT.card :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans Finset.card_image_le
    omega
  -- Count 2: Disjoint leaf-merge OR gates U_c for each center c in T!
  let U : Fin n → Finset ℕ := fun c =>
    (Finset.range D.gates.length).filter fun j =>
      (gateAt D j).op = GateOp.or ∧ 2 ≤ (S (n + j)).card ∧ ∀ v ∈ S (n + j), G.Adj c v
  have hU_disj : ∀ c1 ∈ T, ∀ c2 ∈ T, c1 ≠ c2 → Disjoint (U c1) (U c2) := by
    intro c1 _ c2 _ hne
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := (Finset.mem_filter.mp hj1).2
    have h2 := (Finset.mem_filter.mp hj2).2
    obtain ⟨v1, v2, hv1, hv2, hvne⟩ := Finset.one_lt_card_iff.mp (Nat.lt_of_succ_le h1.2.1)
    have hle := hFour c1 c2 hne
    have hm1 : v1 ∈ Finset.univ.filter (fun w => G.Adj c1 w ∧ G.Adj c2 w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ v1, h1.2.2 v1 hv1, h2.2.2 v1 hv1⟩
    have hm2 : v2 ∈ Finset.univ.filter (fun w => G.Adj c1 w ∧ G.Adj c2 w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ v2, h1.2.2 v2 hv2, h2.2.2 v2 hv2⟩
    exact hvne (Finset.card_le_one.mp hle v1 hm1 v2 hm2)
  -- For each c in T, let Ac(c) = {p in A0.attach | cen p = c}, and Vc(c) = neighbors of c covered by Ac(c).
  let Ac : Fin n → Finset {i // i ∈ A0} := fun c => A0.attach.filter fun p => cen p.1 p.2 = c
  let Vc : Fin n → Finset (Fin n) := fun c => (Ac c).biUnion fun p => S (leafW p.1 p.2)
  have hVc_le : ∀ c : Fin n, (Vc c).card ≤ (U c).card + (Ac c).card := by
    intro c
    let Sc : ℕ → Finset (Fin n) := fun w => if ∀ v ∈ S w, G.Adj c v then S w else ∅
    let MergeC : Finset ℕ := (U c).image (fun j => n + j)
    have hBase : ∀ w, w ∉ MergeC → (Sc w).card ≤ 1 := by
      intro w hw
      dsimp only [Sc]
      by_cases hAdjC : ∀ v ∈ S w, G.Adj c v
      · rw [if_pos hAdjC]
        by_cases hwn : w < n
        · rw [hS_in ⟨w, hwn⟩]; simp
        · by_cases hwg : w - n < D.gates.length
          · rcases hOp_eq (w - n) hwg with hAnd | hOr
            · have hwEq : w = n + (w - n) := by omega
              rw [hwEq, hS_and (w - n) hwg hAnd]; simp
            · by_contra hgt
              push Not at hgt
              apply hw
              refine Finset.mem_image.mpr ⟨w - n, ?_, by omega⟩
              have hwEq : n + (w - n) = w := by omega
              exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwg, hOr,
                by rw [hwEq]; omega, by rw [hwEq]; exact hAdjC⟩
          · have hEmp : S w = ∅ := by
              ext u
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
              rw [hWval_ge w (by omega)]; intro h; cases h
            rw [hEmp]; simp
      · rw [if_neg hAdjC]; simp
    have hStep : ∀ w ∈ MergeC, ∃ a < w, ∃ b < w, Sc w ⊆ Sc a ∪ Sc b := by
      intro w hw
      obtain ⟨j, hjU, rfl⟩ := Finset.mem_image.mp hw
      have hjf := Finset.mem_filter.mp hjU
      have hjlt : j < D.gates.length := Finset.mem_range.mp hjf.1
      have hjOr : (gateAt D j).op = GateOp.or := hjf.2.1
      have hjAdj : ∀ v ∈ S (n + j), G.Adj c v := hjf.2.2.2
      have hS01 : S (n + j) = S (opnd D j 0) ∪ S (opnd D j 1) := hS_or j hjlt hjOr
      have hAdj0 : ∀ v ∈ S (opnd D j 0), G.Adj c v := fun v hv =>
        hjAdj v (by rw [hS01]; exact Finset.mem_union.mpr (Or.inl hv))
      have hAdj1 : ∀ v ∈ S (opnd D j 1), G.Adj c v := fun v hv =>
        hjAdj v (by rw [hS01]; exact Finset.mem_union.mpr (Or.inr hv))
      refine ⟨opnd D j 0, hOpnd_lt j hjlt 0, opnd D j 1, hOpnd_lt j hjlt 1, ?_⟩
      dsimp only [Sc]
      rw [if_pos hjAdj, if_pos hAdj0, if_pos hAdj1, hS01]
    let Rc : Finset ℕ := (Ac c).image fun p => leafW p.1 p.2
    have hRcSub : Rc ⊆ Finset.range (n + D.gates.length) := by
      intro w hw
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_range.mpr (hCL_spec p.1 p.2).1
    have hBound := hMerge Sc MergeC hBase hStep (n + D.gates.length) Rc hRcSub
    have hVcSub : Vc c ⊆ Rc.biUnion Sc := by
      intro v hv
      obtain ⟨p, hpAc, hvp⟩ := Finset.mem_biUnion.mp hv
      have hcen : cen p.1 p.2 = c := (Finset.mem_filter.mp hpAc).2
      have hAdjP : ∀ z ∈ S (leafW p.1 p.2), G.Adj c z := by
        rw [← hcen]; exact (hCL_spec p.1 p.2).2.1
      refine Finset.mem_biUnion.mpr ⟨leafW p.1 p.2, Finset.mem_image.mpr ⟨p, hpAc, rfl⟩, ?_⟩
      dsimp only [Sc]
      rw [if_pos hAdjP]
      exact hvp
    have h1 : (Vc c).card ≤ (Rc.biUnion Sc).card := Finset.card_le_card hVcSub
    have h2 : (MergeC.filter (· < n + D.gates.length)).card ≤ (U c).card :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans Finset.card_image_le
    have h3 : Rc.card ≤ (Ac c).card := Finset.card_image_le
    omega
  -- Every edge of G lies in the union over c in T of {(c, v) | v in Vc c}, so |E(G)| <= sum_{c in T} |Vc c|
  have hEdges_le_sum : G.edgeFinset.card ≤ ∑ c ∈ T, (Vc c).card := by
    let covE : Finset (Sym2 (Fin n)) := T.biUnion fun c => (Vc c).image fun v => s(c, v)
    have hSub : G.edgeFinset ⊆ covE := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
        obtain ⟨i, hi, hcov⟩ := hEdgeCov u v huv
        let p : {k // k ∈ A0} := ⟨i, hi⟩
        have hcT : cen i hi ∈ T := Finset.mem_image.mpr ⟨p, Finset.mem_attach A0 p, rfl⟩
        have hpAc : p ∈ Ac (cen i hi) := Finset.mem_filter.mpr ⟨Finset.mem_attach A0 p, rfl⟩
        rcases hcov with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
        · refine Finset.mem_biUnion.mpr ⟨cen i hi, hcT, Finset.mem_image.mpr ⟨v, ?_, rfl⟩⟩
          exact Finset.mem_biUnion.mpr ⟨p, hpAc, hv⟩
        · refine Finset.mem_biUnion.mpr ⟨cen i hi, hcT, Finset.mem_image.mpr ⟨u, ?_, Sym2.eq_swap⟩⟩
          exact Finset.mem_biUnion.mpr ⟨p, hpAc, hu⟩
    calc G.edgeFinset.card
        ≤ covE.card := Finset.card_le_card hSub
      _ ≤ ∑ c ∈ T, ((Vc c).image fun v => s(c, v)).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ T, (Vc c).card := Finset.sum_le_sum (fun c _ => Finset.card_image_le)
  -- Sum of |Ac c| over c in T equals A0.card
  have hSumAc : ∑ c ∈ T, (Ac c).card = A0.card := by
    have h1 : (T.biUnion Ac) = A0.attach := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_attach, iff_true]
      exact ⟨cen p.1 p.2, Finset.mem_image.mpr ⟨p, Finset.mem_attach A0 p, rfl⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_attach A0 p, rfl⟩⟩
    have hDisj : Set.PairwiseDisjoint (T : Set (Fin n)) Ac := by
      intro c1 _ c2 _ hne
      change Disjoint (Ac c1) (Ac c2)
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      exact hne ((Finset.mem_filter.mp hp1).2.symm.trans (Finset.mem_filter.mp hp2).2)
    rw [← Finset.card_biUnion hDisj, h1, Finset.card_attach]
  -- Sum of |U c| over c in T equals (T.biUnion U).card
  let UT : Finset ℕ := T.biUnion U
  have hSumU : ∑ c ∈ T, (U c).card = UT.card := by
    have hDisj : Set.PairwiseDisjoint (T : Set (Fin n)) U := fun c1 hc1 c2 hc2 hne =>
      hU_disj c1 hc1 c2 hc2 hne
    exact (Finset.card_biUnion hDisj).symm
  -- A0, OT, UT are pairwise disjoint subsets of Finset.range D.gates.length
  have hSubA0 : A0 ⊆ Finset.range D.gates.length := fun i hi => Finset.mem_range.mpr (hA0_lt i hi)
  have hSubOT : OT ⊆ Finset.range D.gates.length := Finset.filter_subset _ _
  have hSubUT : UT ⊆ Finset.range D.gates.length := by
    intro j hj
    obtain ⟨c, _, hjU⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp hjU).1
  have hDisj_A0_OT : Disjoint A0 OT := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := hA0_and j hj1
    have h2 := (Finset.mem_filter.mp hj2).2.1
    rw [h1] at h2; cases h2
  have hDisj_A0_UT : Disjoint A0 UT := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := hA0_and j hj1
    obtain ⟨c, _, hjU⟩ := Finset.mem_biUnion.mp hj2
    have h2 := (Finset.mem_filter.mp hjU).2.1
    rw [h1] at h2; cases h2
  have hDisj_OT_UT : Disjoint OT UT := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 : S (n + j) = ∅ := (Finset.mem_filter.mp hj1).2.2
    obtain ⟨c, _, hjU⟩ := Finset.mem_biUnion.mp hj2
    have h2 : 2 ≤ (S (n + j)).card := (Finset.mem_filter.mp hjU).2.2.1
    rw [h1] at h2
    simp at h2
  have hTotal : A0.card + OT.card + UT.card ≤ D.gates.length := by
    have h1 : (A0 ∪ OT ∪ UT).card ≤ (Finset.range D.gates.length).card :=
      Finset.card_le_card (Finset.union_subset (Finset.union_subset hSubA0 hSubOT) hSubUT)
    rw [Finset.card_range] at h1
    have h2 : (A0 ∪ OT ∪ UT).card = (A0 ∪ OT).card + UT.card :=
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hDisj_A0_UT, hDisj_OT_UT⟩)
    have h3 : (A0 ∪ OT).card = A0.card + OT.card :=
      Finset.card_union_of_disjoint hDisj_A0_OT
    omega
  have hSumBound : G.edgeFinset.card ≤ UT.card + A0.card := by
    calc G.edgeFinset.card
        ≤ ∑ c ∈ T, (Vc c).card := hEdges_le_sum
      _ ≤ ∑ c ∈ T, ((U c).card + (Ac c).card) := Finset.sum_le_sum (fun c _ => hVc_le c)
      _ = (∑ c ∈ T, (U c).card) + (∑ c ∈ T, (Ac c).card) := Finset.sum_add_distrib
      _ = UT.card + A0.card := by rw [hSumU, hSumAc]
  have hDsize : D.size = D.gates.length := rfl
  omega
