import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3297_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.FactorSubst

private def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wireStep_len (gs : List Gate) (w : List Bool) :
    (gs.foldl wireStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g rest ih =>
    rw [List.foldl_cons, ih]
    simp [wireStep]; omega

private lemma foldl_wireStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wireStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons, ih (wireStep w g) (by simp [wireStep]; omega)]
    simp [wireStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl wireStep x := rfl

private lemma wireVal_input (n : ℕ) (C : Circuit) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    wireVal n C i x = x ⟨i, hi⟩ := by
  unfold wireVal
  rw [wires_eq_foldl, foldl_wireStep_getD_lt _ _ i (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi]

private lemma wireVal_gate (n : ℕ) (C : Circuit) (k : ℕ) (x : Fin n → Bool) :
    wireVal n C (n + k) x = gateVal n C k x := rfl

private lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

private lemma gateVal_eval (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hrb : ReadsBack n C) (x : Fin n → Bool) :
    gateVal n C k x = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => wireVal n C i x) := by
  unfold gateVal
  rw [wires_eq_foldl]
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k C.gates, List.drop_eq_getElem_cons hk]
    simp
  let w0 := (C.gates.take k).foldl wireStep (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_wireStep_len, List.length_take_of_le (le_of_lt hk)]
  have h1 : (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false =
      (wireStep w0 C.gates[k]).getD (n + k) false := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlt : n + k < (wireStep w0 C.gates[k]).length := by
      have : (wireStep w0 C.gates[k]).length = w0.length + 1 := by simp [wireStep]
      omega
    exact foldl_wireStep_getD_lt _ _ (n + k) hlt
  rw [h1]
  have h2 : (wireStep w0 C.gates[k]).getD (n + k) false =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => w0.getD i false) := by
    simp only [wireStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w0.length ≤ n + k),
      hw0_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [h2, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + k := hrb k hk i (by rw [gateAt_eq_getElem C k hk]; exact hi)
  unfold wireVal
  rw [wires_eq_foldl]
  conv_rhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlt1 : i < (wireStep w0 C.gates[k]).length := by
    have : (wireStep w0 C.gates[k]).length = w0.length + 1 := by simp [wireStep]
    omega
  rw [foldl_wireStep_getD_lt _ _ i hlt1]
  simp only [wireStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < w0.length)]

private lemma gateVal_and2 (n : ℕ) (C : Circuit) (k p q : ℕ) (hk : k < C.gates.length)
    (hrb : ReadsBack n C) (hop : (gateAt C k).op = GateOp.and) (hins : (gateAt C k).inputs = [p, q])
    (x : Fin n → Bool) :
    gateVal n C k x = (wireVal n C p x && wireVal n C q x) := by
  rw [gateVal_eval n C k hk hrb x, hop, hins]
  simp [GateOp.eval]

private lemma gateVal_or2 (n : ℕ) (C : Circuit) (k p q : ℕ) (hk : k < C.gates.length)
    (hrb : ReadsBack n C) (hop : (gateAt C k).op = GateOp.or) (hins : (gateAt C k).inputs = [p, q])
    (x : Fin n → Bool) :
    gateVal n C k x = (wireVal n C p x || wireVal n C q x) := by
  rw [gateVal_eval n C k hk hrb x, hop, hins]
  simp [GateOp.eval]

private lemma foldl_orStep_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g rest ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]; omega

private lemma foldl_orStep_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ)
    (hj : j < cs.length) :
    (gs.foldl (orStep n) cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons, ih (orStep n cs g) (by simp [orStep]; omega)]
    simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

private lemma orReaches_iff (n : ℕ) (C : Circuit) (j g : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) g ↔
      g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w g) := by
  unfold OrReaches orSets
  rw [Nat.add_sub_cancel_left]
  simp only [Nat.le_add_right, true_and]
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates, List.drop_eq_getElem_cons hj]
    simp
  let cs0 := (C.gates.take j).foldl (orStep n) []
  have hcs0_len : cs0.length = j := by
    simp [cs0, foldl_orStep_len, List.length_take_of_le (le_of_lt hj)]
  have h1 : (C.gates.foldl (orStep n) []).getD j [] = (orStep n cs0 C.gates[j]).getD j [] := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlt : j < (orStep n cs0 C.gates[j]).length := by
      have : (orStep n cs0 C.gates[j]).length = cs0.length + 1 := by simp [orStep]
      omega
    exact foldl_orStep_getD_lt n _ _ j hlt
  have hcs0_eq : ∀ w, n ≤ w → w < n + j → cs0.getD (w - n) [] = (C.gates.foldl (orStep n) []).getD (w - n) [] := by
    intro w hnw hwlt
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlt1 : w - n < (orStep n cs0 C.gates[j]).length := by
      have : (orStep n cs0 C.gates[j]).length = cs0.length + 1 := by simp [orStep]
      omega
    rw [foldl_orStep_getD_lt n _ _ (w - n) hlt1]
    simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w - n < cs0.length)]
  rw [h1]
  conv_lhs => unfold orStep
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : cs0.length ≤ j),
    hcs0_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_cons,
    gateAt_eq_getElem C j hj]
  constructor
  · intro h
    rcases h with rfl | h
    · left; rfl
    · right
      split_ifs at h with hor
      · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at h
        obtain ⟨w, ⟨hw, hnw, hwlt⟩, hg⟩ := h
        rw [hcs0_eq w hnw hwlt] at hg
        exact ⟨hor, w, hw, hnw, hwlt, hnw, hg⟩
      · simp at h
  · intro h
    rcases h with rfl | ⟨hor, w, hw, hnw, hwlt, _, hg⟩
    · left; rfl
    · right
      split_ifs
      rw [← hcs0_eq w hnw hwlt] at hg
      exact List.mem_flatMap.mpr ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨hnw, hwlt⟩⟩, hg⟩

private lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff n C j j hj).mpr (Or.inl rfl)

private lemma orReaches_le (n : ℕ) (C : Circuit) (j g : ℕ) (hj : j < C.gates.length)
    (hr : OrReaches n C (n + j) g) : g ≤ j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_iff n C j g hj] at hr
    rcases hr with rfl | ⟨_, w, _, hnw, hwlt, hrw⟩
    · exact le_refl _
    · have h1 : w - n < j := by omega
      have h2 : n + (w - n) = w := by omega
      rw [← h2] at hrw
      have hle := ih (w - n) h1 (by omega) hrw
      omega

private lemma orReaches_mono_val (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (j g : ℕ) (hj : j < C.gates.length) (hr : OrReaches n C (n + j) g)
    (z : Fin n → Bool) (hg : gateVal n C g z = true) :
    gateVal n C j z = true := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_iff n C j g hj] at hr
    rcases hr with rfl | ⟨hor, w, hw, hnw, hwlt, hrw⟩
    · exact hg
    · have h1 : w - n < j := by omega
      have h2 : n + (w - n) = w := by omega
      rw [← h2] at hrw
      have hwv : wireVal n C w z = true := by
        rw [← h2, wireVal_gate]
        exact ih (w - n) h1 (by omega) hrw
      rw [gateVal_eval n C j hj hrb z, hor]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      exact ⟨true, ⟨w, hw, hwv⟩, rfl⟩

private lemma foldl_coneStep_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g rest ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]; omega

private lemma foldl_coneStep_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ)
    (hj : j < cs.length) :
    (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons, ih (coneStep n cs g) (by simp [coneStep]; omega)]
    simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

private lemma cones_getD (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  unfold cones
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates, List.drop_eq_getElem_cons hj]
    simp
  let cs0 := (C.gates.take j).foldl (coneStep n) []
  have hcs0_len : cs0.length = j := by
    simp [cs0, foldl_coneStep_len, List.length_take_of_le (le_of_lt hj)]
  have h1 : (C.gates.foldl (coneStep n) []).getD j [] = (coneStep n cs0 C.gates[j]).getD j [] := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlt : j < (coneStep n cs0 C.gates[j]).length := by
      have : (coneStep n cs0 C.gates[j]).length = cs0.length + 1 := by simp [coneStep]
      omega
    exact foldl_coneStep_getD_lt n _ _ j hlt
  rw [h1]
  have h2 : (coneStep n cs0 C.gates[j]).getD j [] =
      (C.gates[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: cs0.getD (w - n) []) := by
    unfold coneStep
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : cs0.length ≤ j),
      hcs0_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [h2, gateAt_eq_getElem C j hj]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hwlt : w - n < cs0.length := by omega
  congr 1
  conv_rhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlt1 : w - n < (coneStep n cs0 C.gates[j]).length := by
    have : (coneStep n cs0 C.gates[j]).length = cs0.length + 1 := by simp [coneStep]
    omega
  rw [foldl_coneStep_getD_lt n _ _ (w - n) hlt1]
  simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt]

private lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  rw [cones_getD n C j hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hnw, hwlt⟩, h⟩; exact ⟨w, hw, hnw, hwlt, h⟩
  · rintro ⟨w, hw, hnw, hwlt, h⟩; exact ⟨w, ⟨hw, hnw, hwlt⟩, h⟩

private lemma inCone_trans (n : ℕ) (C : Circuit) (i j k : ℕ) (hk : k < C.gates.length)
    (hij : InCone n C i j) (hjk : InCone n C j k) : InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [inCone_iff n C j k hk] at hjk
    obtain ⟨w, hw, hnw, hwlt, hcase⟩ := hjk
    rw [inCone_iff n C i k hk]
    refine ⟨w, hw, hnw, hwlt, Or.inr ?_⟩
    rcases hcase with rfl | hrec
    · exact hij
    · exact ih (w - n) (by omega) (by omega) hrec

private lemma substReads_length (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n c sigma).gates.length = C.gates.length := by
  simp [substReads]

private lemma substReads_gateAt (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) (j : ℕ)
    (hj : j < C.gates.length) :
    gateAt (substReads C n c sigma) j =
      ⟨(gateAt C j).op, (gateAt C j).inputs.map fun i => if i = n + c then sigma j else i⟩ := by
  simp [gateAt, substReads, List.getD_eq_getElem?_getD, hj]

end PEqualNP.Outside.L_meta_3297_aux

theorem PEqualNP.Outside.L_meta_3297 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C := by
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
    PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.FactorSubst PEqualNP.Outside.L_meta_3297_aux in
  intro n C c a b sigma hAO2 hc_lt hc_and hc_ins hsigma hfront_and _ hout hc_live
  obtain ⟨hAO, hrb, hlen2⟩ := hAO2
  let C' := substReads C n c sigma
  have hlen' : C'.gates.length = C.gates.length := substReads_length C n c sigma
  have ha_lt : a < n + c := hrb c hc_lt a (by simp [hc_ins])
  have hb_lt : b < n + c := hrb c hc_lt b (by simp [hc_ins])
  have hsigma_lt : ∀ r ∈ readers n C c, sigma r < n + c := by
    intro r hr
    rcases hsigma r hr with h | h <;> rw [h] <;> assumption
  have hrb' : ReadsBack n C' := by
    intro j hj i hi
    rw [hlen'] at hj
    rw [substReads_gateAt C n c sigma j hj] at hi
    simp only [List.mem_map] at hi
    obtain ⟨w, hw, rfl⟩ := hi
    have hwlt : w < n + j := hrb j hj w hw
    by_cases hwc : w = n + c
    · subst hwc
      have hr : j ∈ readers n C c := by
        simp [readers, hj, hw]
      have hs := hsigma_lt j hr
      simp only [ite_true]; omega
    · simp only [hwc, ite_false]; exact hwlt
  have hno_c_read : ∀ j < C.gates.length, n + c ∉ (gateAt C' j).inputs := by
    intro j hj hmem
    rw [substReads_gateAt C n c sigma j hj] at hmem
    simp only [List.mem_map] at hmem
    obtain ⟨w, hw, heq⟩ := hmem
    by_cases hwc : w = n + c
    · subst hwc
      have hr : j ∈ readers n C c := by simp [readers, hj, hw]
      have hs := hsigma_lt j hr
      simp only [ite_true] at heq; omega
    · simp only [hwc, ite_false] at heq
  -- Part 2: Cone inclusion and liveSize drop.
  have hcone_sub : ∀ j < C.gates.length, ∀ i, InCone n C' i j → InCone n C i j := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj i hij'
      rw [inCone_iff n C' i j (by omega)] at hij'
      obtain ⟨w', hw', hnw', hw'lt, hcase⟩ := hij'
      rw [substReads_gateAt C n c sigma j hj] at hw'
      simp only [List.mem_map] at hw'
      obtain ⟨w, hw, rfl⟩ := hw'
      by_cases hwc : w = n + c
      · subst hwc
        simp only [ite_true] at hnw' hw'lt hcase
        have hr : j ∈ readers n C c := by simp [readers, hj, hw]
        have hcj : c < j := by have := hrb j hj (n + c) hw; omega
        have hinc_cj : InCone n C c j := by
          rw [inCone_iff n C c j hj]
          exact ⟨n + c, hw, Nat.le_add_right n c, by omega, Or.inl (by omega)⟩
        have hs_in_c : sigma j ∈ (gateAt C c).inputs := by
          rw [hc_ins]
          rcases hsigma j hr with h | h <;> simp [h]
        have hs_lt_c : sigma j < n + c := hsigma_lt j hr
        have hinc_sc : InCone n C (sigma j - n) c := by
          rw [inCone_iff n C (sigma j - n) c hc_lt]
          exact ⟨sigma j, hs_in_c, hnw', hs_lt_c, Or.inl rfl⟩
        have hinc_sj : InCone n C (sigma j - n) j := inCone_trans n C (sigma j - n) c j hj hinc_sc hinc_cj
        rcases hcase with rfl | hrec
        · exact hinc_sj
        · have hrec' : InCone n C i (sigma j - n) := ih (sigma j - n) (by omega) (by omega) i hrec
          exact inCone_trans n C i (sigma j - n) j hj hrec' hinc_sj
      · simp only [hwc, ite_false] at hnw' hw'lt hcase
        rw [inCone_iff n C i j hj]
        refine ⟨w, hw, hnw', hw'lt, ?_⟩
        rcases hcase with rfl | hrec
        · left; rfl
        · right; exact ih (w - n) (by omega) (by omega) i hrec
  have hc_not_cone' : ∀ j < C.gates.length, ¬ InCone n C' c j := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj hc'
      rw [inCone_iff n C' c j (by omega)] at hc'
      obtain ⟨w, hw, hnw, hwlt, hcase⟩ := hc'
      rcases hcase with hce | hrec
      · have hwc : w = n + c := by omega
        subst hwc; exact hno_c_read j hj hw
      · exact ih (w - n) (by omega) (by omega) hrec
  have hlive_drop : liveSize n C' + 1 ≤ liveSize n C := by
    have hout' : C'.output = C.output := rfl
    have hsub : liveGates n C' ⊆ (liveGates n C).erase c := by
      intro j hj
      simp only [liveGates, Finset.mem_filter, Finset.mem_range, hlen', hout'] at hj
      obtain ⟨hjlt, hnout, hcase⟩ := hj
      have hjne : j ≠ c := by
        intro hjeq
        subst j
        rcases hcase with hout_eq | hcone
        · exact hout c (Finset.mem_insert_self c _) (by omega)
        · have hout_lt : C.output - n < C.gates.length := by
            by_contra hge
            unfold InCone at hcone
            have hclen : (cones n C').length = C.gates.length := by
              unfold cones; rw [foldl_coneStep_len]; simp [hlen']
            rw [List.getD_eq_default _ _ (by omega)] at hcone
            simp at hcone
          exact hc_not_cone' (C.output - n) hout_lt hcone
      refine Finset.mem_erase.mpr ⟨hjne, ?_⟩
      simp only [liveGates, Finset.mem_filter, Finset.mem_range]
      refine ⟨hjlt, hnout, ?_⟩
      rcases hcase with hout_eq | hcone
      · left; exact hout_eq
      · right
        have hout_lt : C.output - n < C.gates.length := by
          by_contra hge
          unfold InCone at hcone
          have hclen : (cones n C').length = C.gates.length := by
            unfold cones; rw [foldl_coneStep_len]; simp [hlen']
          rw [List.getD_eq_default _ _ (by omega)] at hcone
          simp at hcone
        exact hcone_sub (C.output - n) hout_lt j hcone
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hc_live] at hcard
    have hpos : 0 < (liveGates n C).card := Finset.card_pos.mpr ⟨c, hc_live⟩
    unfold liveSize; omega
  -- Part 1: Combined strong induction on k < C.gates.length.
  have hmain : ∀ k < C.gates.length, ∀ z : Fin n → Bool,
      (k ≠ c → k ∉ orClosure n C c → gateVal n C' k z = gateVal n C k z) ∧
      (gateVal n C k z = true → gateVal n C' k z = true) ∧
      (k ∈ orClosure n C c → gateVal n C' k z = true → gateVal n C k z = false →
        ∃ r ∈ readers n C c, OrReaches n C (n + k) r ∧ wireVal n C (sigma r) z = true) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk z
      have hgate_op : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
        rw [gateAt_eq_getElem C k hk]
        exact hAO C.gates[k] (List.getElem_mem hk)
      have hgate_len : (gateAt C k).inputs.length = 2 := by
        rw [gateAt_eq_getElem C k hk]
        exact hlen2 C.gates[k] (List.getElem_mem hk)
      obtain ⟨p, q, hpq⟩ : ∃ p q, (gateAt C k).inputs = [p, q] := by
        rcases h : (gateAt C k).inputs with _ | ⟨p, _ | ⟨q, _ | ⟨r, rs⟩⟩⟩
        · simp [h] at hgate_len
        · simp [h] at hgate_len
        · exact ⟨p, q, rfl⟩
        · simp [h] at hgate_len
      let mapIn : ℕ → ℕ := fun w => if w = n + c then sigma k else w
      have hgate'_op : (gateAt C' k).op = (gateAt C k).op := by
        rw [substReads_gateAt C n c sigma k hk]
      have hgate'_ins : (gateAt C' k).inputs = [mapIn p, mapIn q] := by
        rw [substReads_gateAt C n c sigma k hk, hpq]; rfl
      -- Helper: wires strictly below n + c are preserved (not in insert c O).
      have hwire_lt_c : ∀ w < n + c, w < n + k → wireVal n C' w z = wireVal n C w z := by
        intro w hwc hwk
        by_cases hwn : w < n
        · rw [wireVal_input n C' w hwn z, wireVal_input n C w hwn z]
        · have hjlt : w - n < k := by omega
          have hjc : w - n < c := by omega
          have hnw : n + (w - n) = w := by omega
          rw [← hnw, wireVal_gate, wireVal_gate]
          have hnotO : w - n ∉ orClosure n C c := by
            intro hmem
            simp only [orClosure, Finset.mem_filter, Finset.mem_range] at hmem
            have hle := orReaches_le n C (w - n) c hmem.1 hmem.2.2
            omega
          exact (ih (w - n) hjlt (by omega) z).1 (by omega) hnotO
      -- Helper: any wire w < n + k not in insert c O is preserved.
      have hwire_out : ∀ w < n + k, (∀ u ∈ insert c (orClosure n C c), w ≠ n + u) →
          wireVal n C' w z = wireVal n C w z := by
        intro w hwk houtw
        by_cases hwn : w < n
        · rw [wireVal_input n C' w hwn z, wireVal_input n C w hwn z]
        · have hjlt : w - n < k := by omega
          have hnw : n + (w - n) = w := by omega
          rw [← hnw, wireVal_gate, wireVal_gate]
          have hjne : w - n ≠ c := fun h => houtw c (Finset.mem_insert_self c _) (by omega)
          have hjnotO : w - n ∉ orClosure n C c := fun h =>
            houtw (w - n) (Finset.mem_insert_of_mem h) (by omega)
          exact (ih (w - n) hjlt (by omega) z).1 hjne hjnotO
      -- Helper: monotonicity of each mapped input wire.
      have hwire_mono : ∀ w ∈ (gateAt C k).inputs,
          wireVal n C w z = true → wireVal n C' (mapIn w) z = true := by
        intro w hw hwv
        have hwk : w < n + k := hrb k hk w hw
        by_cases hwc : w = n + c
        · subst hwc
          have hr : k ∈ readers n C c := by simp [readers, hk, hw]
          have hs_lt : sigma k < n + c := hsigma_lt k hr
          have hcv : gateVal n C c z = true := hwv
          rw [gateVal_and2 n C c a b hc_lt hrb hc_and hc_ins z, Bool.and_eq_true] at hcv
          have hmap : mapIn (n + c) = sigma k := by simp [mapIn]
          rw [hmap, hwire_lt_c (sigma k) hs_lt (by omega)]
          rcases hsigma k hr with h | h <;> rw [h]
          · exact hcv.1
          · exact hcv.2
        · have hmap : mapIn w = w := by simp [mapIn, hwc]
          rw [hmap]
          by_cases hwn : w < n
          · rw [wireVal_input n C' w hwn z, ← wireVal_input n C w hwn z]; exact hwv
          · have hjlt : w - n < k := by omega
            have hnw : n + (w - n) = w := by omega
            rw [← hnw, wireVal_gate] at hwv ⊢
            exact (ih (w - n) hjlt (by omega) z).2.1 hwv
      -- Prove (2): monotonicity at k.
      have hmono_k : gateVal n C k z = true → gateVal n C' k z = true := by
        intro hkv
        rcases hgate_op with hand | hor
        · rw [gateVal_and2 n C k p q hk hrb hand hpq z, Bool.and_eq_true] at hkv
          rw [gateVal_and2 n C' k (mapIn p) (mapIn q) (by omega) hrb' (hgate'_op.trans hand) hgate'_ins z,
            Bool.and_eq_true]
          exact ⟨hwire_mono p (by simp [hpq]) hkv.1, hwire_mono q (by simp [hpq]) hkv.2⟩
        · rw [gateVal_or2 n C k p q hk hrb hor hpq z, Bool.or_eq_true] at hkv
          rw [gateVal_or2 n C' k (mapIn p) (mapIn q) (by omega) hrb' (hgate'_op.trans hor) hgate'_ins z,
            Bool.or_eq_true]
          rcases hkv with hpv | hqv
          · left; exact hwire_mono p (by simp [hpq]) hpv
          · right; exact hwire_mono q (by simp [hpq]) hqv
      -- Prove (3): upper bound on k ∈ orClosure n C c.
      have hupper_k : k ∈ orClosure n C c → gateVal n C' k z = true → gateVal n C k z = false →
          ∃ r ∈ readers n C c, OrReaches n C (n + k) r ∧ wireVal n C (sigma r) z = true := by
        intro hkO hk'v hkv
        simp only [orClosure, Finset.mem_filter, Finset.mem_range] at hkO
        have hor : (gateAt C k).op = GateOp.or := by
          have hr := hkO.2.2
          rw [orReaches_iff n C k c hk] at hr
          rcases hr with hce | ⟨hor, _⟩
          · exact (hkO.2.1 hce.symm).elim
          · exact hor
        rw [gateVal_or2 n C' k (mapIn p) (mapIn q) (by omega) hrb' (hgate'_op.trans hor) hgate'_ins z,
          Bool.or_eq_true] at hk'v
        rw [gateVal_or2 n C k p q hk hrb hor hpq z, Bool.or_eq_false_iff] at hkv
        have hstep : ∀ w ∈ (gateAt C k).inputs,
            wireVal n C' (mapIn w) z = true → wireVal n C w z = false →
            ∃ r ∈ readers n C c, OrReaches n C (n + k) r ∧ wireVal n C (sigma r) z = true := by
          intro w hw hw'v hwv
          have hwk : w < n + k := hrb k hk w hw
          by_cases hwc : w = n + c
          · subst hwc
            have hr : k ∈ readers n C c := by simp [readers, hk, hw]
            have hs_lt : sigma k < n + c := hsigma_lt k hr
            have hmap : mapIn (n + c) = sigma k := by simp [mapIn]
            rw [hmap, hwire_lt_c (sigma k) hs_lt (by omega)] at hw'v
            exact ⟨k, hr, orReaches_self n C k hk, hw'v⟩
          · have hmap : mapIn w = w := by simp [mapIn, hwc]
            rw [hmap] at hw'v
            by_cases hwn : w < n
            · rw [wireVal_input n C' w hwn z] at hw'v
              rw [wireVal_input n C w hwn z] at hwv
              rw [hwv] at hw'v; cases hw'v
            · have hjlt : w - n < k := by omega
              have hnw : n + (w - n) = w := by omega
              rw [← hnw, wireVal_gate] at hw'v hwv
              have hjne : w - n ≠ c := by omega
              have hjO : w - n ∈ orClosure n C c := by
                by_contra hnotO
                have heq := (ih (w - n) hjlt (by omega) z).1 hjne hnotO
                rw [hwv] at heq; rw [heq] at hw'v; cases hw'v
              obtain ⟨r, hr, hreach, hsr⟩ := (ih (w - n) hjlt (by omega) z).2.2 hjO hw'v hwv
              refine ⟨r, hr, ?_, hsr⟩
              rw [orReaches_iff n C k r hk]
              right
              refine ⟨hor, w, hw, by omega, hwk, ?_⟩
              rw [← hnw]; exact hreach
        rcases hk'v with hp' | hq'
        · exact hstep p (by simp [hpq]) hp' hkv.1
        · exact hstep q (by simp [hpq]) hq' hkv.2
      -- Prove (1): equality outside insert c O.
      refine ⟨?_, hmono_k, hupper_k⟩
      intro hkne hknotO
      apply Bool.eq_iff_iff.mpr
      refine ⟨?_, hmono_k⟩
      intro hk'v
      by_cases hfr : k ∈ frontier n C c
      · -- k is on the frontier of c, hence must be an AND gate!
        have hk_and : (gateAt C k).op = GateOp.and := by
          rcases hgate_op with hand | hor
          · exact hand
          · exfalso
            simp only [FactorSubst.frontier, Finset.mem_filter, Finset.mem_range] at hfr
            obtain ⟨_, _, _, w, hwS, hw_in⟩ := hfr
            have hwlt : n + w < n + k := hrb k hk (n + w) hw_in
            have hreach : OrReaches n C (n + k) c := by
              rw [orReaches_iff n C k c hk]
              right
              refine ⟨hor, n + w, hw_in, Nat.le_add_right n w, hwlt, ?_⟩
              rcases Finset.mem_insert.mp hwS with hwc | hwO
              · rw [hwc]; exact orReaches_self n C c hc_lt
              · simp only [orClosure, Finset.mem_filter, Finset.mem_range] at hwO
                exact hwO.2.2
            exact hknotO (by simp [orClosure, hk, hkne, hreach])
        simp only [FactorSubst.frontier, Finset.mem_filter, Finset.mem_range] at hfr
        obtain ⟨_, _, _, w, hwS, hw_in⟩ := hfr
        rw [hpq, List.mem_cons, List.mem_singleton] at hw_in
        -- Symmetric handler for (u, y) with u = n + w.
        have hand_side : ∀ u y : ℕ,
            ((gateAt C k).inputs = [u, y] ∨ (gateAt C k).inputs = [y, u]) →
            u = n + w →
            wireVal n C' (mapIn u) z = true →
            wireVal n C' (mapIn y) z = true →
            wireVal n C u z = true ∧ wireVal n C y z = true := by
          intro u y hins hu hu'v hy'v
          have hfr_k : k ∈ frontier n C c := by
            simp only [FactorSubst.frontier, Finset.mem_filter, Finset.mem_range]
            refine ⟨hk, hkne, hknotO, w, hwS, ?_⟩
            rcases hins with h | h <;> simp [h, hu]
          obtain ⟨hy_notS, hclean⟩ := hfront_and k hfr_k hk_and u y hins ⟨w, hwS, hu⟩
          have hy_in : y ∈ (gateAt C k).inputs := by
            rcases hins with h | h <;> simp [h]
          have hy_lt : y < n + k := hrb k hk y hy_in
          have hy_nec : y ≠ n + c := hy_notS c (Finset.mem_insert_self c _)
          have hmap_y : mapIn y = y := by simp [mapIn, hy_nec]
          rw [hmap_y, hwire_out y hy_lt hy_notS] at hy'v
          refine ⟨?_, hy'v⟩
          rcases Finset.mem_insert.mp hwS with hwc | hwO
          · -- Direct reader: u = n + c, k ∈ readers n C c.
            rw [hwc] at hu
            have hu_in : n + c ∈ (gateAt C k).inputs := by
              rw [← hu]; rcases hins with h | h <;> simp [h]
            have hr : k ∈ readers n C c := by simp [readers, hk, hu_in]
            have hs_lt : sigma k < n + c := hsigma_lt k hr
            have hmap_u : mapIn u = sigma k := by simp [mapIn, hu]
            rw [hmap_u, hwire_lt_c (sigma k) hs_lt (by have := hrb k hk (n + c) hu_in; omega)] at hu'v
            obtain ⟨hcb, hca⟩ := hclean k hr (Or.inl rfl)
            rw [hu, wireVal_gate, gateVal_and2 n C c a b hc_lt hrb hc_and hc_ins z, Bool.and_eq_true]
            rcases hsigma k hr with h | h
            · rw [h] at hu'v; exact ⟨hu'v, hca h z hy'v⟩
            · rw [h] at hu'v; exact ⟨hcb h z hy'v, hu'v⟩
          · -- Indirect reader through O: w ∈ orClosure n C c, u = n + w ≠ n + c.
            simp only [orClosure, Finset.mem_filter, Finset.mem_range] at hwO
            have hune : u ≠ n + c := by have := hwO.2.1; omega
            have hmap_u : mapIn u = u := by simp [mapIn, hune]
            rw [hmap_u, hu, wireVal_gate] at hu'v
            rw [hu, wireVal_gate]
            cases hwu : gateVal n C w z with
            | true => rfl
            | false =>
              exfalso
              have hwlt : w < k := by
                have hu_in : n + w ∈ (gateAt C k).inputs := by
                  rw [← hu]; rcases hins with h | h <;> simp [h]
                have := hrb k hk (n + w) hu_in; omega
              have hwO' : w ∈ orClosure n C c := by
                simp [orClosure, hwO.1, hwO.2.1, hwO.2.2]
              obtain ⟨r, hr, hreach, hsr⟩ := (ih w hwlt hwO.1 z).2.2 hwO' hu'v hwu
              obtain ⟨hcb, hca⟩ := hclean r hr (Or.inr (hu.symm ▸ hreach))
              have hc_true : gateVal n C c z = true := by
                rw [gateVal_and2 n C c a b hc_lt hrb hc_and hc_ins z, Bool.and_eq_true]
                rcases hsigma r hr with h | h
                · rw [h] at hsr; exact ⟨hsr, hca h z hy'v⟩
                · rw [h] at hsr; exact ⟨hcb h z hy'v, hsr⟩
              have hw_true := orReaches_mono_val n C hrb w c hwO.1 hwO.2.2 z hc_true
              rw [hwu] at hw_true; cases hw_true
        rw [gateVal_and2 n C' k (mapIn p) (mapIn q) (by omega) hrb' (hgate'_op.trans hk_and) hgate'_ins z,
          Bool.and_eq_true] at hk'v
        rw [gateVal_and2 n C k p q hk hrb hk_and hpq z, Bool.and_eq_true]
        rcases hw_in with hpw | hqw
        · exact hand_side p q (Or.inl hpq) hpw.symm hk'v.1 hk'v.2
        · have hres := hand_side q p (Or.inr hpq) hqw.symm hk'v.2 hk'v.1
          exact ⟨hres.2, hres.1⟩
      · -- Not on frontier: neither p nor q is in insert c O.
        have hnotS : ∀ w ∈ (gateAt C k).inputs, ∀ u ∈ insert c (orClosure n C c), w ≠ n + u := by
          intro w hw u hu heq
          apply hfr
          simp only [FactorSubst.frontier, Finset.mem_filter, Finset.mem_range]
          exact ⟨hk, hkne, hknotO, u, hu, heq ▸ hw⟩
        have hp_notS := hnotS p (by simp [hpq])
        have hq_notS := hnotS q (by simp [hpq])
        have hmp : mapIn p = p := by simp [mapIn, hp_notS c (Finset.mem_insert_self c _)]
        have hmq : mapIn q = q := by simp [mapIn, hq_notS c (Finset.mem_insert_self c _)]
        have hpeq : wireVal n C' (mapIn p) z = wireVal n C p z := by
          rw [hmp]; exact hwire_out p (hrb k hk p (by simp [hpq])) hp_notS
        have hqeq : wireVal n C' (mapIn q) z = wireVal n C q z := by
          rw [hmq]; exact hwire_out q (hrb k hk q (by simp [hpq])) hq_notS
        rcases hgate_op with hand | hor
        · rw [gateVal_and2 n C' k (mapIn p) (mapIn q) (by omega) hrb' (hgate'_op.trans hand) hgate'_ins z,
            hpeq, hqeq] at hk'v
          rw [gateVal_and2 n C k p q hk hrb hand hpq z]; exact hk'v
        · rw [gateVal_or2 n C' k (mapIn p) (mapIn q) (by omega) hrb' (hgate'_op.trans hor) hgate'_ins z,
            hpeq, hqeq] at hk'v
          rw [gateVal_or2 n C k p q hk hrb hor hpq z]; exact hk'v
  exact ⟨fun k hk hkne hknotO z => (hmain k hk z).1 hkne hknotO, hlive_drop⟩
