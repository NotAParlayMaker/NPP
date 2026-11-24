import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3545_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma foldl_append_len {α : Type} (f : List α → Gate → α) :
    ∀ (gs : List Gate) (init : List α),
      (gs.foldl (fun a g => a ++ [f a g]) init).length = init.length + gs.length
  | [], init => by simp
  | g :: gs, init => by
      simp only [List.foldl_cons, foldl_append_len, List.length_append, List.length_cons,
        List.length_nil]
      omega

lemma foldl_append_prefix {α : Type} (f : List α → Gate → α) :
    ∀ (gs : List Gate) (init : List α) (i : ℕ), i < init.length → ∀ (d : α),
      (gs.foldl (fun a g => a ++ [f a g]) init).getD i d = init.getD i d
  | [], init, i, _, d => rfl
  | g :: gs, init, i, hi, d => by
      simp only [List.foldl_cons]
      have hlen : i < (init ++ [f init g]).length := by simp; omega
      rw [foldl_append_prefix f gs (init ++ [f init g]) i hlen d]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_append_at {α : Type} (f : List α → Gate → α) :
    ∀ (gs : List Gate) (init : List α) (j : ℕ) (hj : j < gs.length) (d : α),
      (gs.foldl (fun a g => a ++ [f a g]) init).getD (init.length + j) d =
        f ((gs.take j).foldl (fun a g => a ++ [f a g]) init) gs[j]
  | [], _, _, hj, _ => by simp at hj
  | g :: gs, init, 0, _, d => by
      simp only [List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil,
        List.getElem_cons_zero]
      have hlen : init.length < (init ++ [f init g]).length := by simp
      rw [foldl_append_prefix f gs (init ++ [f init g]) init.length hlen d]
      simp [List.getD_eq_getElem?_getD]
  | g :: gs, init, j + 1, hj, d => by
      simp only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ]
      have hj' : j < gs.length := Nat.lt_of_succ_lt_succ hj
      have heq : init.length + (j + 1) = (init ++ [f init g]).length + j := by simp; omega
      rw [heq, foldl_append_at f gs (init ++ [f init g]) j hj' d]

lemma wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_append_len (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates x

lemma wireVal_input (n : ℕ) (C : Circuit) (y : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i y = y ⟨i, hi⟩ := by
  unfold wireVal Circuit.wires
  have hlen : i < (List.ofFn y).length := by simpa using hi
  rw [foldl_append_prefix _ C.gates (List.ofFn y) i hlen false]
  simp [List.getD_eq_getElem?_getD, hi]

lemma wireVal_ge (n : ℕ) (C : Circuit) (y : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) :
    wireVal n C w y = false := by
  unfold wireVal
  have hlen : (C.wires (List.ofFn y)).length ≤ w := by
    rw [wires_len, List.length_ofFn]; exact hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
  rfl

lemma wireVal_gate (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (y : Fin n → Bool) :
    wireVal n C (n + j) y =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => if i < n + j then wireVal n C i y else false) := by
  unfold wireVal Circuit.wires
  have hn : n = (List.ofFn y).length := by simp
  have hstep := foldl_append_at (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn y) j hj false
  rw [← hn] at hstep
  rw [hstep]
  have hgj : C.gates[j] = gateAt C j := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]
  rw [hgj]
  congr 1
  apply List.map_congr_left
  intro i _
  set pref := (C.gates.take j).foldl
    (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn y)
  have hplen : pref.length = n + j := by
    rw [foldl_append_len, List.length_ofFn, List.length_take]
    omega
  by_cases hi : i < n + j
  · rw [if_pos hi]
    have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_rhs => rw [hsplit, List.foldl_append]
    exact (foldl_append_prefix _ (C.gates.drop j) pref i (by omega) false).symm
  · rw [if_neg hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

lemma wireVal_append_left (n : ℕ) (G0 G1 : List Gate) (o1 o2 : ℕ) (w : ℕ)
    (hw : w < n + G0.length) (y : Fin n → Bool) :
    wireVal n ⟨G0 ++ G1, o1⟩ w y = wireVal n ⟨G0, o2⟩ w y := by
  unfold wireVal Circuit.wires
  simp only [List.foldl_append]
  have hlen : w < (G0.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn y)).length := by
    rw [foldl_append_len, List.length_ofFn]; exact hw
  exact foldl_append_prefix _ G1 _ w hlen false

lemma cones_len (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones coneStep
  simpa using foldl_append_len
    (fun cs g => (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])) C.gates []

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones coneStep
  have hstep := foldl_append_at
    (fun cs g => (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])) C.gates [] j hj []
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [hstep]
  have hgj : C.gates[j] = gateAt C j := by
    unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
  rw [hgj]
  set pref := (C.gates.take j).foldl
    (fun cs g => cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])]) []
  have hplen : pref.length = j := by
    rw [foldl_append_len, List.length_nil, Nat.zero_add, List.length_take]; omega
  rw [hplen, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    refine ⟨w, hw.1, hw.2.1, hw.2.2, ?_⟩
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · left; rfl
    · right
      have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
      rw [hsplit, List.foldl_append]
      rw [foldl_append_prefix _ (C.gates.drop j) pref (w - n) (by omega) []]
      exact hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hw, hnw, hlt⟩
    · simp only [List.mem_cons]
      rcases hi with rfl | hi
      · left; rfl
      · right
        have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
        rw [hsplit, List.foldl_append] at hi
        rw [foldl_append_prefix _ (C.gates.drop j) pref (w - n) (by omega) []] at hi
        exact hi

lemma inCone_of_mem (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length)
    (hij : i < j) (hmem : n + i ∈ (gateAt C j).inputs) : InCone n C i j := by
  rw [inCone_iff n C i j hj]
  exact ⟨n + i, hmem, by omega, by omega, Or.inl (by omega)⟩

lemma inCone_trans_mem (n : ℕ) (C : Circuit) (i k j : ℕ) (hj : j < C.gates.length)
    (hkj : k < j) (hmem : n + k ∈ (gateAt C j).inputs) (hik : InCone n C i k) :
    InCone n C i j := by
  rw [inCone_iff n C i j hj]
  exact ⟨n + k, hmem, by omega, by omega, Or.inr (by simpa using hik)⟩

lemma orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  simpa using foldl_append_len
    (fun cs g => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) []) else [])) C.gates []

lemma orReaches_iff (n : ℕ) (C : Circuit) (j g : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) g ↔
      g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w g) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold OrReaches orSets orStep
  simp only [Nat.le_add_right, Nat.add_sub_cancel_left, true_and]
  have hstep := foldl_append_at
    (fun cs g => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) []) else [])) C.gates [] j hj []
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [hstep]
  have hgj : C.gates[j] = gateAt C j := by
    unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
  rw [hgj]
  set pref := (C.gates.take j).foldl
    (fun cs g => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) []) else [])]) []
  have hplen : pref.length = j := by
    rw [foldl_append_len, List.length_nil, Nat.zero_add, List.length_take]; omega
  rw [hplen, List.mem_cons]
  constructor
  · rintro (rfl | h)
    · left; rfl
    · right
      by_cases hop : (gateAt C j).op = GateOp.or
      · rw [if_pos hop, List.mem_flatMap] at h
        rcases h with ⟨w, hw, hg⟩
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        refine ⟨hop, w, hw.1, hw.2.1, hw.2.2, hw.2.1, ?_⟩
        have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
        rw [hsplit, List.foldl_append]
        rw [foldl_append_prefix _ (C.gates.drop j) pref (w - n) (by omega) []]
        exact hg
      · rw [if_neg hop] at h; simp at h
  · rintro (rfl | ⟨hop, w, hw, hnw, hlt, _, hg⟩)
    · left; rfl
    · right
      rw [if_pos hop, List.mem_flatMap]
      refine ⟨w, ?_, ?_⟩
      · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hw, hnw, hlt⟩
      · have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
        rw [hsplit, List.foldl_append] at hg
        rw [foldl_append_prefix _ (C.gates.drop j) pref (w - n) (by omega) []] at hg
        exact hg

lemma orReaches_lt (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    w < n + C.gates.length := by
  by_contra hge
  have h1 : (orSets n C).length ≤ w - n := by rw [orSets_len]; omega
  have h2 : (orSets n C).getD (w - n) [] = [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]; rfl
  rcases h with ⟨_, hmem⟩
  rw [h2] at hmem
  simp at hmem

lemma orReaches_wireVal (n : ℕ) (C : Circuit) (y : Fin n → Bool) :
    ∀ j, j < C.gates.length → ∀ g, OrReaches n C (n + j) g →
      wireVal n C (n + g) y = true → wireVal n C (n + j) y = true := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj g hor hval
    rw [orReaches_iff n C j g hj] at hor
    rcases hor with rfl | ⟨hop, w, hw, hnw, hlt, hor'⟩
    · exact hval
    · have hwval : wireVal n C w y = true := by
        have heq : n + (w - n) = w := by omega
        rw [← heq] at hor' ⊢
        exact ih (w - n) (by omega) (by omega) g hor' hval
      rw [wireVal_gate n C j hj y, hop]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      exact ⟨w, hw, by rw [if_pos hlt]; exact hwval⟩

lemma orReaches_wireVal_any (n : ℕ) (C : Circuit) (w g : ℕ) (y : Fin n → Bool)
    (hor : OrReaches n C w g) (hval : wireVal n C (n + g) y = true) :
    wireVal n C w y = true := by
  have hlt := orReaches_lt n C w g hor
  have hnw : n ≤ w := hor.1
  have heq : n + (w - n) = w := by omega
  rw [← heq] at hor ⊢
  exact orReaches_wireVal n C y (w - n) (by omega) g hor hval

lemma gateAt_D_right (C : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ) (o : ℕ)
    (r : ℕ) (hr : r < C.gates.length) :
    gateAt ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : Gate)), o⟩
      (G0.length + r) =
    { op := (gateAt C r).op, inputs := (gateAt C r).inputs.map (fun i7 => rho r i7) } := by
  unfold gateAt
  simp only [List.getD_eq_getElem?_getD]
  have h1 : G0.length ≤ G0.length + r := Nat.le_add_right _ _
  rw [List.getElem?_append_right h1, Nat.add_sub_cancel_left]
  have hr' : r < (C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : Gate))).length := by
    simpa using hr
  rw [List.getElem?_eq_getElem hr', List.getElem_mapIdx, List.getElem?_eq_getElem hr]
  rfl

lemma eval_and_iff (l : List Bool) : GateOp.and.eval l = true ↔ ∀ b ∈ l, b = true := by
  simp [GateOp.eval]

lemma eval_or_iff (l : List Bool) : GateOp.or.eval l = true ↔ ∃ b ∈ l, b = true := by
  simp [GateOp.eval]

theorem main : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 := by
  intro n H qH C m u T W z NR P G0 rho D hqH hAO2 hCeval hNR hP hPair hClosed hNoDep _ hD hRhoKeep hRhoNR
  rcases hAO2 with ⟨hAO, hRB, hLen2⟩
  have hOpAO : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    intro j hj
    have hmem : gateAt C j ∈ C.gates := by
      unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
    exact hAO _ hmem
  have hDlen : D.gates.length = G0.length + C.gates.length := by
    rw [hD]; simp
  have hGateD : ∀ r < C.gates.length,
      gateAt D (G0.length + r) =
        { op := (gateAt C r).op, inputs := (gateAt C r).inputs.map (fun i7 => rho r i7) } := by
    intro r hr
    rw [hD]
    exact gateAt_D_right C G0 rho _ r hr
  have hWireD_noNR : ∀ g, g < C.gates.length →
      (∀ k < m, ∀ r, NR k r → r ≠ g ∧ ¬ InCone n C r g) →
      ∀ y : Fin n → Bool, wireVal n D (n + G0.length + g) y = wireVal n C (n + g) y := by
    intro g
    induction g using Nat.strongRecOn with
    | ind g ih =>
      intro hg hno y
      have hDlt : G0.length + g < D.gates.length := by omega
      have heq1 : n + G0.length + g = n + (G0.length + g) := by omega
      rw [heq1, wireVal_gate n D (G0.length + g) hDlt y, wireVal_gate n C g hg y, hGateD g hg]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp_apply]
      have hilt : i < n + g := hRB g hg i hi
      rw [if_pos hilt]
      have hnotNR : ∀ k < m, ¬ (NR k g ∧ i = n + u k) := by
        intro k hk ⟨hnr, _⟩
        exact (hno k hk g hnr).1 rfl
      rw [hRhoKeep g hg i hi hnotNR]
      by_cases hin : i < n
      · rw [if_pos hin, if_pos (by omega), wireVal_input n D y i hin, wireVal_input n C y i hin]
      · rw [if_neg hin, if_pos (by omega)]
        have hgi : i - n < g := by omega
        have hno' : ∀ k < m, ∀ r, NR k r → r ≠ i - n ∧ ¬ InCone n C r (i - n) := by
          intro k hk r hnr
          have hmem : n + (i - n) ∈ (gateAt C g).inputs := by
            have : n + (i - n) = i := by omega
            rwa [this]
          refine ⟨?_, ?_⟩
          · rintro rfl
            exact (hno k hk (i - n) hnr).2 (inCone_of_mem n C (i - n) g hg hgi hmem)
          · intro hic
            exact (hno k hk r hnr).2 (inCone_trans_mem n C r (i - n) g hg hgi hmem hic)
        have hrec := ih (i - n) hgi (by omega) hno' y
        have heq2 : i + G0.length = n + G0.length + (i - n) := by omega
        have heq3 : n + (i - n) = i := by omega
        rw [heq2, hrec, heq3]
  have hReadNR : ∀ r < C.gates.length, ∀ k < m, NR k r → ∀ y : Fin n → Bool,
      (if rho r (n + u k) < n + (G0.length + r) then wireVal n D (rho r (n + u k)) y else false) = P k y := by
    intro r hr k hk hnr y
    rcases hRhoNR r k hk hnr with ⟨hlt, hval⟩ | ⟨g9, hg9, hreq, hval, hno⟩ | ⟨hfalse, hge⟩
    · rw [if_pos (by omega), hD, wireVal_append_left n G0 _ _ 0 _ hlt y, hval y]
    · rw [hreq, if_pos (by omega), hWireD_noNR g9 (by omega) hno y, hval y]
    · rw [if_neg (by omega), hfalse y]
  have hStarOfP : ∀ (k : ℕ) (hk : k < m) (y : Fin n → Bool), P k y = true →
      y ⟨z k, (hPair k hk).2.2.2.1⟩ = true →
      (∀ x, wireVal n C (n + u k) x = true → wireVal n C (W k) x = true) →
      qH y = true := by
    intro k hk y hPy hzy hReach
    have hp := hPair k hk
    rcases hp with ⟨_, hTlt, hTop, hzk, hTins, hTimp, _⟩
    rw [hP k y, decide_eq_true_eq] at hPy
    rcases hPy with ⟨w1, hyw1, hu1⟩
    set e : Fin n → Bool := fun j1 => decide (j1 = w1 ∨ (j1 : ℕ) = z k)
    have hWe : wireVal n C (W k) e = true := hReach e hu1
    have hze : wireVal n C (z k) e = true := by
      rw [wireVal_input n C e (z k) hzk]
      simp [e]
    have hTe : wireVal n C (n + T k) e = true := by
      rw [wireVal_gate n C (T k) hTlt e, hTop, eval_and_iff]
      intro b hb
      rw [List.mem_map] at hb
      rcases hb with ⟨w, hw, rfl⟩
      have hwlt : w < n + T k := hRB (T k) hTlt w hw
      rw [if_pos hwlt]
      rcases hTins with hTins | hTins
      · rw [hTins] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hWe
        · exact hze
      · rw [hTins] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hze
        · exact hWe
    have hqe : qH e = true := hTimp e hTe
    rw [hqH] at hqe ⊢
    rcases hqe with ⟨a0, b0, hadj, hea, heb⟩
    have hle : ∀ j : Fin n, e j = true → y j = true := by
      intro j hj
      simp only [e, decide_eq_true_eq] at hj
      rcases hj with rfl | hjz
      · exact hyw1
      · have : j = ⟨z k, hzk⟩ := Fin.ext hjz
        rw [this]; exact hzy
    exact ⟨a0, b0, hadj, hle a0 hea, hle b0 heb⟩
  have hUpperInd : ∀ y : Fin n → Bool, ∀ g, g < C.gates.length →
      wireVal n D (n + G0.length + g) y = true →
      wireVal n C (n + g) y = true ∨ qH y = true ∨
        ∃ k < m, OrReaches n C (W k) g ∧ (gateAt C g).op = GateOp.or ∧ InCone n C (u k) g ∧
          P k y = true ∧ (∀ x, wireVal n C (n + u k) x = true → wireVal n C (W k) x = true) := by
    intro y g
    induction g using Nat.strongRecOn with
    | ind g ih =>
      intro hg hDg
      have hDlt : G0.length + g < D.gates.length := by omega
      have heq1 : n + G0.length + g = n + (G0.length + g) := by omega
      rw [heq1, wireVal_gate n D (G0.length + g) hDlt y, hGateD g hg] at hDg
      rcases hOpAO g hg with hop | hop
      · rw [hop, eval_and_iff] at hDg
        have hInput : ∀ i ∈ (gateAt C g).inputs,
            wireVal n C i y = true ∨ qH y = true := by
          intro i hi
          have hDi : (if rho g i < n + (G0.length + g) then wireVal n D (rho g i) y else false) = true := by
            apply hDg
            rw [List.mem_map]
            exact ⟨rho g i, List.mem_map_of_mem hi, rfl⟩
          have hilt : i < n + g := hRB g hg i hi
          by_cases hex : ∃ k < m, NR k g ∧ i = n + u k
          · rcases hex with ⟨k, hk, hnr, rfl⟩
            have hPk : P k y = true := by rw [← hReadNR g hg k hk hnr y]; exact hDi
            have hp := hPair k hk
            rcases hp with ⟨_, hTlt, hTop, hzk, hTins, _, _⟩
            have hgT : g = T k := by
              have hnr' := (hNR k g).mp hnr
              rcases hnr'.2.2 with h1 | ⟨_, hor⟩
              · exact h1
              · rw [hop] at hor; cases hor
            have hWu : W k = n + u k := by
              rw [hgT] at hi
              rcases hTins with hTins | hTins
              · rw [hTins] at hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with h1 | h1
                · exact h1.symm
                · omega
              · rw [hTins] at hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with h1 | h1
                · omega
                · exact h1.symm
            have hzmem : z k ∈ (gateAt C g).inputs := by
              rw [hgT]
              rcases hTins with hTins | hTins <;> simp [hTins]
            have hznotNR : ∀ k' < m, ¬ (NR k' g ∧ z k = n + u k') := by
              intro k' _ ⟨_, heq⟩; omega
            have hDz : (if rho g (z k) < n + (G0.length + g) then wireVal n D (rho g (z k)) y else false) = true := by
              apply hDg
              rw [List.mem_map]
              exact ⟨rho g (z k), List.mem_map_of_mem hzmem, rfl⟩
            rw [hRhoKeep g hg (z k) hzmem hznotNR, if_pos hzk, if_pos (by omega),
              wireVal_input n D y (z k) hzk] at hDz
            right
            exact hStarOfP k hk y hPk hDz (fun _ hx => by rw [hWu]; exact hx)
          · rw [hRhoKeep g hg i hi (fun k hk h => hex ⟨k, hk, h⟩)] at hDi
            by_cases hin : i < n
            · rw [if_pos hin, if_pos (by omega), wireVal_input n D y i hin] at hDi
              left; rw [wireVal_input n C y i hin]; exact hDi
            · rw [if_neg hin, if_pos (by omega)] at hDi
              have hgi : i - n < g := by omega
              have heq2 : i + G0.length = n + G0.length + (i - n) := by omega
              rw [heq2] at hDi
              rcases ih (i - n) hgi (by omega) hDi with hC | hQ | ⟨k, hk, hor, hop', hic, hPk, hReach⟩
              · left
                have : n + (i - n) = i := by omega
                rwa [this] at hC
              · right; exact hQ
              · have hmem' : n + (i - n) ∈ (gateAt C g).inputs := by
                  have : n + (i - n) = i := by omega
                  rwa [this]
                have hcl := (hClosed k hk (i - n) (by omega) hor hop' hic).2 g hg hmem'
                have hgT : g = T k := by
                  rcases hcl with h1 | ⟨_, hor2⟩
                  · exact h1
                  · rw [hop] at hor2; cases hor2
                have hp := hPair k hk
                rcases hp with ⟨_, _, _, hzk, hTins, _, _⟩
                have hzmem : z k ∈ (gateAt C g).inputs := by
                  rw [hgT]
                  rcases hTins with hTins | hTins <;> simp [hTins]
                have hznotNR : ∀ k' < m, ¬ (NR k' g ∧ z k = n + u k') := by
                  intro k' _ ⟨_, heq⟩; omega
                have hDz : (if rho g (z k) < n + (G0.length + g) then wireVal n D (rho g (z k)) y else false) = true := by
                  apply hDg
                  rw [List.mem_map]
                  exact ⟨rho g (z k), List.mem_map_of_mem hzmem, rfl⟩
                rw [hRhoKeep g hg (z k) hzmem hznotNR, if_pos hzk, if_pos (by omega),
                  wireVal_input n D y (z k) hzk] at hDz
                right
                exact hStarOfP k hk y hPk hDz hReach
        by_cases hq : qH y = true
        · right; left; exact hq
        · left
          rw [wireVal_gate n C g hg y, hop, eval_and_iff]
          intro b hb
          rw [List.mem_map] at hb
          rcases hb with ⟨i, hi, rfl⟩
          rw [if_pos (hRB g hg i hi)]
          exact (hInput i hi).resolve_right hq
      · rw [hop, eval_or_iff] at hDg
        rcases hDg with ⟨_, hmem, hval⟩
        rw [List.mem_map] at hmem
        rcases hmem with ⟨w, hw, rfl⟩
        rw [List.mem_map] at hw
        rcases hw with ⟨i, hi, rfl⟩
        have hilt : i < n + g := hRB g hg i hi
        by_cases hex : ∃ k < m, NR k g ∧ i = n + u k
        · rcases hex with ⟨k, hk, hnr, rfl⟩
          have hPk : P k y = true := by rw [← hReadNR g hg k hk hnr y]; exact hval
          have hnr' := (hNR k g).mp hnr
          have hor : OrReaches n C (W k) g := by
            rcases hnr'.2.2 with h1 | ⟨h2, _⟩
            · have hTop := (hPair k hk).2.2.1
              rw [h1, hTop] at hop; cases hop
            · exact h2
          have hic : InCone n C (u k) g := inCone_of_mem n C (u k) g hg (by omega) hi
          have hReach : ∀ x, wireVal n C (n + u k) x = true → wireVal n C (W k) x = true := by
            intro x hux
            apply orReaches_wireVal_any n C (W k) g x hor
            rw [wireVal_gate n C g hg x, hop, eval_or_iff]
            exact ⟨true, List.mem_map.mpr ⟨n + u k, hi, by rw [if_pos hilt]; exact hux⟩, rfl⟩
          right; right
          exact ⟨k, hk, hor, hop, hic, hPk, hReach⟩
        · rw [hRhoKeep g hg i hi (fun k hk h => hex ⟨k, hk, h⟩)] at hval
          by_cases hin : i < n
          · rw [if_pos hin, if_pos (by omega), wireVal_input n D y i hin] at hval
            left
            rw [wireVal_gate n C g hg y, hop, eval_or_iff]
            refine ⟨true, List.mem_map.mpr ⟨i, hi, ?_⟩, rfl⟩
            rw [if_pos hilt, wireVal_input n C y i hin]; exact hval
          · rw [if_neg hin, if_pos (by omega)] at hval
            have hgi : i - n < g := by omega
            have heq2 : i + G0.length = n + G0.length + (i - n) := by omega
            rw [heq2] at hval
            rcases ih (i - n) hgi (by omega) hval with hC | hQ | ⟨k, hk, hor, hop', hic, hPk, hReach⟩
            · left
              rw [wireVal_gate n C g hg y, hop, eval_or_iff]
              refine ⟨true, List.mem_map.mpr ⟨i, hi, ?_⟩, rfl⟩
              rw [if_pos hilt]
              have : n + (i - n) = i := by omega
              rwa [this] at hC
            · right; left; exact hQ
            · have hmem' : n + (i - n) ∈ (gateAt C g).inputs := by
                have : n + (i - n) = i := by omega
                rwa [this]
              have hcl := (hClosed k hk (i - n) (by omega) hor hop' hic).2 g hg hmem'
              have hor2 : OrReaches n C (W k) g := by
                rcases hcl with h1 | ⟨h2, _⟩
                · have hTop := (hPair k hk).2.2.1
                  rw [h1, hTop] at hop; cases hop
                · exact h2
              have hic2 : InCone n C (u k) g := inCone_trans_mem n C (u k) (i - n) g hg hgi hmem' hic
              right; right
              exact ⟨k, hk, hor2, hop, hic2, hPk, hReach⟩
  have hD_imp_qH : ∀ y : Fin n → Bool, D.eval (List.ofFn y) = true → qH y = true := by
    intro y hDy
    change wireVal n D D.output y = true at hDy
    have hDout : D.output = if C.output < n then C.output else C.output + G0.length := by
      rw [hD]
    rw [hDout] at hDy
    by_cases hlt : C.output < n
    · rw [if_pos hlt, wireVal_input n D y C.output hlt] at hDy
      rw [← hCeval y]
      change wireVal n C C.output y = true
      rw [wireVal_input n C y C.output hlt]
      exact hDy
    · rw [if_neg hlt] at hDy
      by_cases hge : n + C.gates.length ≤ C.output
      · rw [wireVal_ge n D y (C.output + G0.length) (by omega)] at hDy
        cases hDy
      · have hg : C.output - n < C.gates.length := by omega
        have heq : C.output + G0.length = n + G0.length + (C.output - n) := by omega
        rw [heq] at hDy
        rcases hUpperInd y (C.output - n) hg hDy with hC | hQ | ⟨k, hk, hor, hop, hic, _, _⟩
        · rw [← hCeval y]
          change wireVal n C C.output y = true
          have : n + (C.output - n) = C.output := by omega
          rwa [this] at hC
        · exact hQ
        · exfalso
          have hne := (hClosed k hk (C.output - n) hg hor hop hic).1
          omega
  have hP_mono : ∀ k y1 y2, (∀ j, y1 j = true → y2 j = true) → P k y1 = true → P k y2 = true := by
    intro k y1 y2 hle h1
    rw [hP k y1, decide_eq_true_eq] at h1
    rw [hP k y2, decide_eq_true_eq]
    rcases h1 with ⟨w1, hw1, hu1⟩
    exact ⟨w1, hle w1 hw1, hu1⟩
  have hWireD_mono : ∀ g, g < C.gates.length → ∀ y1 y2, (∀ j, y1 j = true → y2 j = true) →
      wireVal n D (n + G0.length + g) y1 = true → wireVal n D (n + G0.length + g) y2 = true := by
    intro g
    induction g using Nat.strongRecOn with
    | ind g ih =>
      intro hg y1 y2 hle h1
      have hDlt : G0.length + g < D.gates.length := by omega
      have heq1 : n + G0.length + g = n + (G0.length + g) := by omega
      rw [heq1, wireVal_gate n D (G0.length + g) hDlt y1, hGateD g hg] at h1
      rw [heq1, wireVal_gate n D (G0.length + g) hDlt y2, hGateD g hg]
      have hInMono : ∀ i ∈ (gateAt C g).inputs,
          (if rho g i < n + (G0.length + g) then wireVal n D (rho g i) y1 else false) = true →
          (if rho g i < n + (G0.length + g) then wireVal n D (rho g i) y2 else false) = true := by
        intro i hi hDi
        have hilt : i < n + g := hRB g hg i hi
        by_cases hex : ∃ k < m, NR k g ∧ i = n + u k
        · rcases hex with ⟨k, hk, hnr, rfl⟩
          rw [hReadNR g hg k hk hnr y1] at hDi
          rw [hReadNR g hg k hk hnr y2]
          exact hP_mono k y1 y2 hle hDi
        · rw [hRhoKeep g hg i hi (fun k hk h => hex ⟨k, hk, h⟩)] at hDi ⊢
          by_cases hin : i < n
          · rw [if_pos hin, if_pos (by omega), wireVal_input n D y1 i hin] at hDi
            rw [if_pos hin, if_pos (by omega), wireVal_input n D y2 i hin]
            exact hle ⟨i, hin⟩ hDi
          · rw [if_neg hin, if_pos (by omega)] at hDi ⊢
            have heq2 : i + G0.length = n + G0.length + (i - n) := by omega
            rw [heq2] at hDi ⊢
            exact ih (i - n) (by omega) (by omega) y1 y2 hle hDi
      rcases hOpAO g hg with hop | hop
      · rw [hop, eval_and_iff] at h1 ⊢
        intro b hb
        rw [List.mem_map] at hb
        rcases hb with ⟨w, hw, rfl⟩
        rw [List.mem_map] at hw
        rcases hw with ⟨i, hi, rfl⟩
        apply hInMono i hi
        exact h1 _ (List.mem_map.mpr ⟨rho g i, List.mem_map_of_mem hi, rfl⟩)
      · rw [hop, eval_or_iff] at h1 ⊢
        rcases h1 with ⟨_, hb, hval⟩
        rw [List.mem_map] at hb
        rcases hb with ⟨w, hw, rfl⟩
        rw [List.mem_map] at hw
        rcases hw with ⟨i, hi, rfl⟩
        exact ⟨true, List.mem_map.mpr ⟨rho g i, List.mem_map_of_mem hi, hInMono i hi hval⟩, rfl⟩
  have hDeval_mono : ∀ (y1 y2 : Fin n → Bool), (∀ j, y1 j = true → y2 j = true) →
      D.eval (List.ofFn y1) = true → D.eval (List.ofFn y2) = true := by
    intro y1 y2 hle h1
    change wireVal n D D.output y1 = true at h1
    change wireVal n D D.output y2 = true
    have hDout : D.output = if C.output < n then C.output else C.output + G0.length := by rw [hD]
    rw [hDout] at h1 ⊢
    by_cases hlt : C.output < n
    · rw [if_pos hlt, wireVal_input n D y1 C.output hlt] at h1
      rw [if_pos hlt, wireVal_input n D y2 C.output hlt]
      exact hle ⟨C.output, hlt⟩ h1
    · rw [if_neg hlt] at h1 ⊢
      by_cases hge : n + C.gates.length ≤ C.output
      · rw [wireVal_ge n D y1 (C.output + G0.length) (by omega)] at h1; cases h1
      · have heq : C.output + G0.length = n + G0.length + (C.output - n) := by omega
        rw [heq] at h1 ⊢
        exact hWireD_mono (C.output - n) (by omega) y1 y2 hle h1
  have hLowerPair : ∀ (a0 b0 : Fin n) (g : ℕ), g < C.gates.length →
      let e : Fin n → Bool := fun j => decide (j = a0 ∨ j = b0)
      wireVal n C (n + g) e = true →
      wireVal n D (n + G0.length + g) e = true ∨
        ∃ k < m, (∀ hz : z k < n, e ⟨z k, hz⟩ = false) ∧
          OrReaches n C (W k) g ∧ (gateAt C g).op = GateOp.or ∧ InCone n C (u k) g := by
    intro a0 b0 g
    induction g using Nat.strongRecOn with
    | ind g ih =>
      intro hg e hCg
      have hDlt : G0.length + g < D.gates.length := by omega
      have heq1 : n + G0.length + g = n + (G0.length + g) := by omega
      have hT_z : ∀ (k : ℕ) (hk : k < m), g = T k → wireVal n C (n + g) e = true →
          e ⟨z k, (hPair k hk).2.2.2.1⟩ = true := by
        intro k hk hgT hTval
        have hp := hPair k hk
        rcases hp with ⟨_, hTlt, hTop, hzk, hTins, _, _⟩
        rw [hgT, wireVal_gate n C (T k) hTlt e, hTop, eval_and_iff] at hTval
        have hzmem : z k ∈ (gateAt C (T k)).inputs := by
          rcases hTins with hTins | hTins <;> simp [hTins]
        have hzval := hTval _ (List.mem_map.mpr ⟨z k, hzmem, rfl⟩)
        rw [if_pos (hRB (T k) hTlt (z k) hzmem), wireVal_input n C e (z k) hzk] at hzval
        exact hzval
      have hInStep : ∀ i ∈ (gateAt C g).inputs, wireVal n C i e = true →
          (if rho g i < n + (G0.length + g) then wireVal n D (rho g i) e else false) = true ∨
          ∃ k < m, (∀ hz : z k < n, e ⟨z k, hz⟩ = false) ∧
            OrReaches n C (W k) g ∧ (gateAt C g).op = GateOp.or ∧ InCone n C (u k) g := by
        intro i hi hCi
        have hilt : i < n + g := hRB g hg i hi
        by_cases hex : ∃ k < m, NR k g ∧ i = n + u k
        · rcases hex with ⟨k, hk, hnr, rfl⟩
          have hzk : z k < n := (hPair k hk).2.2.2.1
          by_cases hez : e ⟨z k, hzk⟩ = true
          · left
            rw [hReadNR g hg k hk hnr e, hP k e, decide_eq_true_eq]
            have hez' : (⟨z k, hzk⟩ : Fin n) = a0 ∨ (⟨z k, hzk⟩ : Fin n) = b0 := by
              simpa [e] using hez
            rcases hez' with ha | hb
            · refine ⟨b0, by simp [e], ?_⟩
              have heeq : (fun j1 : Fin n => decide (j1 = b0 ∨ (j1 : ℕ) = z k)) = e := by
                funext j1
                have hja : (j1 : ℕ) = z k ↔ j1 = a0 :=
                  ⟨fun h => by rw [← ha]; exact Fin.ext h, fun h => by rw [h, ← ha]⟩
                simp [e, hja, or_comm]
              rw [heeq]; exact hCi
            · refine ⟨a0, by simp [e], ?_⟩
              have heeq : (fun j1 : Fin n => decide (j1 = a0 ∨ (j1 : ℕ) = z k)) = e := by
                funext j1
                have hjb : (j1 : ℕ) = z k ↔ j1 = b0 :=
                  ⟨fun h => by rw [← hb]; exact Fin.ext h, fun h => by rw [h, ← hb]⟩
                simp [e, hjb]
              rw [heeq]; exact hCi
          · have hezf : e ⟨z k, hzk⟩ = false := Bool.eq_false_iff.mpr hez
            have hnr' := (hNR k g).mp hnr
            rcases hnr'.2.2 with hgT | ⟨hor, hop⟩
            · exfalso
              have hzt := hT_z k hk hgT hCg
              rw [hezf] at hzt; cases hzt
            · right
              exact ⟨k, hk, fun _ => hezf, hor, hop, inCone_of_mem n C (u k) g hg (by omega) hi⟩
        · rw [hRhoKeep g hg i hi (fun k hk h => hex ⟨k, hk, h⟩)]
          by_cases hin : i < n
          · left
            rw [if_pos hin, if_pos (by omega), wireVal_input n D e i hin]
            rw [wireVal_input n C e i hin] at hCi
            exact hCi
          · rw [if_neg hin, if_pos (by omega)]
            have hgi : i - n < g := by omega
            have heq2 : i + G0.length = n + G0.length + (i - n) := by omega
            have hCi' : wireVal n C (n + (i - n)) e = true := by
              have : n + (i - n) = i := by omega
              rwa [this]
            rcases ih (i - n) hgi (by omega) hCi' with hD' | ⟨k, hk, hezf, hor, hop', hic⟩
            · left; rw [heq2]; exact hD'
            · have hmem' : n + (i - n) ∈ (gateAt C g).inputs := by
                have : n + (i - n) = i := by omega
                rwa [this]
              have hcl := (hClosed k hk (i - n) (by omega) hor hop' hic).2 g hg hmem'
              rcases hcl with hgT | ⟨hor2, hop2⟩
              · exfalso
                have hzt := hT_z k hk hgT hCg
                have hzf : e ⟨z k, (hPair k hk).2.2.2.1⟩ = false := hezf (hPair k hk).2.2.2.1
                rw [hzf] at hzt; cases hzt
              · right
                exact ⟨k, hk, hezf, hor2, hop2, inCone_trans_mem n C (u k) (i - n) g hg hgi hmem' hic⟩
      rcases hOpAO g hg with hop | hop
      · left
        rw [wireVal_gate n C g hg e, hop, eval_and_iff] at hCg
        rw [heq1, wireVal_gate n D (G0.length + g) hDlt e, hGateD g hg, hop, eval_and_iff]
        intro b hb
        rw [List.mem_map] at hb
        rcases hb with ⟨w, hw, rfl⟩
        rw [List.mem_map] at hw
        rcases hw with ⟨i, hi, rfl⟩
        have hCi : wireVal n C i e = true := by
          have hv := hCg _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
          rwa [if_pos (hRB g hg i hi)] at hv
        rcases hInStep i hi hCi with hD' | ⟨_, _, _, _, hop', _⟩
        · exact hD'
        · rw [hop] at hop'; cases hop'
      · rw [wireVal_gate n C g hg e, hop, eval_or_iff] at hCg
        rcases hCg with ⟨_, hmem, hval⟩
        rw [List.mem_map] at hmem
        rcases hmem with ⟨i, hi, rfl⟩
        rw [if_pos (hRB g hg i hi)] at hval
        rcases hInStep i hi hval with hD' | hEx
        · left
          rw [heq1, wireVal_gate n D (G0.length + g) hDlt e, hGateD g hg, hop, eval_or_iff]
          exact ⟨true, List.mem_map.mpr ⟨rho g i, List.mem_map_of_mem hi, hD'⟩, rfl⟩
        · right; exact hEx
  have hqH_imp_D : ∀ y : Fin n → Bool, qH y = true → D.eval (List.ofFn y) = true := by
    intro y hqy
    rw [hqH] at hqy
    rcases hqy with ⟨a0, b0, hadj, hya, hyb⟩
    set e : Fin n → Bool := fun j => decide (j = a0 ∨ j = b0)
    have hle : ∀ j, e j = true → y j = true := by
      intro j hj
      simp only [e, decide_eq_true_eq] at hj
      rcases hj with rfl | rfl
      · exact hya
      · exact hyb
    apply hDeval_mono e y hle
    have hCe : C.eval (List.ofFn e) = true := by
      rw [hCeval e, hqH]
      exact ⟨a0, b0, hadj, by simp [e], by simp [e]⟩
    change wireVal n C C.output e = true at hCe
    change wireVal n D D.output e = true
    have hDout : D.output = if C.output < n then C.output else C.output + G0.length := by rw [hD]
    rw [hDout]
    by_cases hlt : C.output < n
    · rw [if_pos hlt, wireVal_input n D e C.output hlt]
      rw [wireVal_input n C e C.output hlt] at hCe
      exact hCe
    · rw [if_neg hlt]
      by_cases hge : n + C.gates.length ≤ C.output
      · rw [wireVal_ge n C e C.output hge] at hCe; cases hCe
      · have hg : C.output - n < C.gates.length := by omega
        have hCe' : wireVal n C (n + (C.output - n)) e = true := by
          have : n + (C.output - n) = C.output := by omega
          rwa [this]
        have heq : C.output + G0.length = n + G0.length + (C.output - n) := by omega
        rw [heq]
        rcases hLowerPair a0 b0 (C.output - n) hg hCe' with hD' | ⟨k, hk, _, hor, hop, hic⟩
        · exact hD'
        · exfalso
          have hne := (hClosed k hk (C.output - n) hg hor hop hic).1
          omega
  intro y12
  cases h1 : D.eval (List.ofFn y12) <;> cases h2 : qH y12
  · rfl
  · exfalso; have := hqH_imp_D y12 h2; rw [h1] at this; cases this
  · exfalso; have := hD_imp_qH y12 h1; rw [h2] at this; cases this
  · rfl

end PEqualNP.Outside.L_meta_3545_aux

theorem PEqualNP.Outside.L_meta_3545 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 := PEqualNP.Outside.L_meta_3545_aux.main
