import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2231

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_fold (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp only [stepW, List.length_append, List.length_cons, List.length_nil]
    omega

theorem pre_fold (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have hi' : i < (stepW w g).length := by
      simp only [stepW, List.length_append, List.length_cons, List.length_nil]; omega
    rw [List.foldl_cons, ih _ i hi']
    simp only [stepW]
    exact List.getD_append _ _ _ _ hi

theorem entry_fold (gs : List Gate) : ∀ (w : List Bool) (k : ℕ), k < gs.length →
    (∀ m < gs.length, ∀ i ∈ (gs.getD m ⟨GateOp.or, []⟩).inputs, i < w.length + m) →
    (gs.foldl stepW w).getD (w.length + k) false =
      (gs.getD k ⟨GateOp.or, []⟩).op.eval
        ((gs.getD k ⟨GateOp.or, []⟩).inputs.map fun i => (gs.foldl stepW w).getD i false) := by
  induction gs with
  | nil => intro w k hk; simp at hk
  | cons g gs ih =>
    intro w k hk hr
    rw [List.foldl_cons]
    cases k with
    | zero =>
      have hlen : w.length + 0 < (stepW w g).length := by
        simp only [stepW, List.length_append, List.length_cons, List.length_nil]; omega
      rw [pre_fold gs (stepW w g) _ hlen]
      have hmap : (g.inputs.map fun i => (gs.foldl stepW (stepW w g)).getD i false) =
          (g.inputs.map fun i => w.getD i false) := by
        apply List.map_congr_left
        intro i hi
        have hiw : i < w.length := by
          have := hr 0 (by simp) i (by simpa using hi)
          omega
        have hi' : i < (stepW w g).length := by
          simp only [stepW, List.length_append, List.length_cons, List.length_nil]; omega
        rw [pre_fold gs (stepW w g) i hi']
        simp only [stepW]
        exact List.getD_append _ _ _ _ hiw
      rw [List.getD_cons_zero, hmap]
      have hv : (stepW w g).getD (w.length + 0) false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [stepW]
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp
      exact hv
    | succ k' =>
      have hk' : k' < gs.length := by simpa using hk
      have hr' : ∀ m < gs.length, ∀ i ∈ (gs.getD m ⟨GateOp.or, []⟩).inputs,
          i < (stepW w g).length + m := by
        intro m hm i hi
        have := hr (m + 1) (by simpa using hm) i (by simpa using hi)
        have hl : (stepW w g).length = w.length + 1 := by
          simp only [stepW, List.length_append, List.length_cons, List.length_nil]
        omega
      have hl : (stepW w g).length = w.length + 1 := by
        simp only [stepW, List.length_append, List.length_cons, List.length_nil]
      have := ih (stepW w g) k' hk' hr'
      rw [hl] at this
      have e : w.length + (k' + 1) = w.length + 1 + k' := by omega
      rw [e, this]
      simp

-- The value of the wire `i` of `C` at the input `x`.
def V {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

theorem wires_eq (C : Circuit) (w : List Bool) : C.wires w = C.gates.foldl stepW w := rfl

theorem V_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) : V C x i.val = x i := by
  unfold V
  rw [wires_eq, pre_fold C.gates _ i.val (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem V_gate {n : ℕ} (C : Circuit) (hR : ReadsBack n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    V C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V C x i) := by
  have h := entry_fold C.gates (List.ofFn x) j hj (by
    intro m hm i hi
    rw [List.length_ofFn]
    exact hR m hm i hi)
  rw [List.length_ofFn] at h
  unfold V
  rw [wires_eq]
  exact h

-- Closure lists of the OR closure computation.
theorem len_orFold (n : ℕ) (gs : List Gate) : ∀ cs : List (List ℕ),
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs with
  | nil => intro cs; simp
  | cons g gs ih =>
    intro cs
    rw [List.foldl_cons, ih]
    simp only [orStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem pre_orFold (n : ℕ) (gs : List Gate) : ∀ (cs : List (List ℕ)) (i : ℕ), i < cs.length →
    (gs.foldl (orStep n) cs).getD i [] = cs.getD i [] := by
  induction gs with
  | nil => intro cs i _; rfl
  | cons g gs ih =>
    intro cs i hi
    have hi' : i < (orStep n cs g).length := by
      simp only [orStep, List.length_append, List.length_cons, List.length_nil]; omega
    rw [List.foldl_cons, ih _ i hi']
    simp only [orStep]
    exact List.getD_append _ _ _ _ hi

open Classical in
theorem entry_orFold (n : ℕ) (gs : List Gate) : ∀ (cs : List (List ℕ)) (k : ℕ), k < gs.length →
    (gs.foldl (orStep n) cs).getD (cs.length + k) [] =
      (cs.length + k) :: (if (gs.getD k ⟨GateOp.or, []⟩).op = GateOp.or then
        (((gs.getD k ⟨GateOp.or, []⟩).inputs.filter
          (fun w => decide (n ≤ w ∧ w < n + (cs.length + k)))).flatMap
          (fun w => (gs.foldl (orStep n) cs).getD (w - n) []))
        else []) := by
  induction gs with
  | nil => intro cs k hk; simp at hk
  | cons g gs ih =>
    intro cs k hk
    rw [List.foldl_cons]
    cases k with
    | zero =>
      have hlen : cs.length + 0 < (orStep n cs g).length := by
        simp only [orStep, List.length_append, List.length_cons, List.length_nil]; omega
      rw [pre_orFold n gs (orStep n cs g) _ hlen]
      simp only [List.getD_cons_zero]
      have hc : (orStep n cs g).getD (cs.length + 0) [] =
          cs.length :: (if g.op = GateOp.or then
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
              (fun w => cs.getD (w - n) []) else []) := by
        simp only [orStep]
        rw [List.getD_append_right _ _ _ _ (by omega)]
        by_cases hg : g.op = GateOp.or <;> simp [hg]
      rw [hc]
      simp only [Nat.add_zero]
      by_cases hg : g.op = GateOp.or
      · simp only [hg, ite_true]
        congr 1
        apply List.flatMap_congr
        intro w hw
        have hw' := (List.mem_filter.1 hw).2
        have hw'' : n ≤ w ∧ w < n + cs.length := of_decide_eq_true hw'
        have hlt : w - n < (orStep n cs g).length := by
          simp only [orStep, List.length_append, List.length_cons, List.length_nil]; omega
        rw [pre_orFold n gs (orStep n cs g) _ hlt]
        simp only [orStep]
        exact (List.getD_append _ _ _ _ (by omega)).symm
      · simp [hg]
    | succ k' =>
      have hk' : k' < gs.length := by simpa using hk
      have hl : (orStep n cs g).length = cs.length + 1 := by
        simp only [orStep, List.length_append, List.length_cons, List.length_nil]
      have := ih (orStep n cs g) k' hk'
      rw [hl] at this
      have e : cs.length + (k' + 1) = cs.length + 1 + k' := by omega
      rw [e, this]
      simp only [List.getD_cons_succ]

theorem orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  have h := len_orFold n C.gates []
  simpa [orSets] using h

theorem lt_of_mem_orSets (n : ℕ) (C : Circuit) (m g : ℕ) (h : g ∈ (orSets n C).getD m []) :
    m < C.gates.length := by
  by_contra hcon
  have h1 : (orSets n C).length ≤ m := by rw [orSets_len]; omega
  rw [List.getD_eq_default _ _ h1] at h
  simp at h

open Classical in
theorem or_reach_val {n : ℕ} (C : Circuit) (hR : ReadsBack n C) (x : Fin n → Bool) :
    ∀ j g : ℕ, j < C.gates.length → g ∈ (orSets n C).getD j [] →
      V C x (n + g) = true → V C x (n + j) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro g hj hg hgv
    have hentry : (orSets n C).getD j [] = j :: (if (gateAt C j).op = GateOp.or then
        (((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
          (fun w => (orSets n C).getD (w - n) [])) else []) := by
      have h := entry_orFold n C.gates [] j hj
      rw [List.length_nil, Nat.zero_add] at h
      exact h
    rw [hentry] at hg
    rcases List.mem_cons.1 hg with h | h
    · rw [h] at hgv; exact hgv
    · by_cases hop : (gateAt C j).op = GateOp.or
      · simp only [hop, ↓reduceIte] at h
        obtain ⟨w, hw, hgw⟩ := List.mem_flatMap.1 h
        have hw' := List.mem_filter.1 hw
        have hcond : n ≤ w ∧ w < n + j := of_decide_eq_true hw'.2
        have hVw : V C x w = true := by
          have := ih (w - n) (by omega) g (by omega) hgw hgv
          have e : n + (w - n) = w := by omega
          rwa [e] at this
        rw [V_gate C hR x j hj, hop]
        simp only [GateOp.eval]
        rw [List.any_eq_true]
        exact ⟨V C x w, List.mem_map.2 ⟨w, hw'.1, rfl⟩, hVw⟩
      · simp only [hop, ↓reduceIte] at h
        simp at h

theorem V_orIn {n : ℕ} (C : Circuit) (hR : ReadsBack n C) (x : Fin n → Bool) (w : ℕ) (i : Fin n)
    (hi : i ∈ orIn n C w) (hx : x i = true) : V C x w = true := by
  let _ := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold orIn at hi
  have hi' := Finset.mem_filter.1 hi
  rcases hi'.2 with h | ⟨k, hk, hreach, hkop, hkin⟩
  · rw [← h, V_input]; exact hx
  · have hVk : V C x (n + k) = true := by
      rw [V_gate C hR x k hk, hkop]
      simp only [GateOp.eval]
      rw [List.any_eq_true]
      refine ⟨V C x i.val, List.mem_map.2 ⟨i.val, hkin, rfl⟩, ?_⟩
      rw [V_input]; exact hx
    obtain ⟨hnw, hmem⟩ := hreach
    have hlt := lt_of_mem_orSets n C (w - n) k hmem
    have := or_reach_val C hR x (w - n) k hlt hmem hVk
    have e : n + (w - n) = w := by omega
    rwa [e] at this

theorem and_gate_out {n : ℕ} (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hout : OrReaches n C C.output j) (x : Fin n → Bool)
    (h0 : V C x (opnd C j 0) = true) (h1 : V C x (opnd C j 1) = true) :
    circuitFun n C x = true := by
  obtain ⟨_, hR, hlen⟩ := hAO
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hl2 : (gateAt C j).inputs.length = 2 := hlen _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hl2
  have ha : opnd C j 0 = a := by simp [opnd, hab]
  have hb : opnd C j 1 = b := by simp [opnd, hab]
  rw [ha] at h0
  rw [hb] at h1
  have hVj : V C x (n + j) = true := by
    rw [V_gate C hR x j hj, hand, hab]
    simp [GateOp.eval, h0, h1]
  obtain ⟨hno, hmem'⟩ := hout
  have hlt := lt_of_mem_orSets n C (C.output - n) j hmem'
  have := or_reach_val C hR x (C.output - n) j hlt hmem' hVj
  have e : n + (C.output - n) = C.output := by omega
  rw [e] at this
  exact this

end PEqualNP.Outside.L_meta_2231

open PEqualNP.Outside.L_meta_2231 in
theorem PEqualNP.Outside.L_meta_2231 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.OrReaches n C C.output j → (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 → w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧ (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 → ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1)) ∧ (∀ F : Finset ℕ, (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), ∃ i ∈ F, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i ∧ ((e.1 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C i 1) ∨ (e.2 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.1 ∈ PEqualNP.TopForm.side (n := n) C i 1))) → ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)), e3.1 ∈ T ∨ e3.2 ∈ T) := by
  intro n G _ C hFour hAO hz1 hz2
  have hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C := hAO.2.1
  have part1 : ∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.OrReaches n C C.output j → (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 → w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧ (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 → ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1) := by
    intro j hj hand hout
    have hA1 : ∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 → w ∉ PEqualNP.TopForm.side (n := n) C j 1 := by
      intro w h0 h1
      have := and_gate_out C hAO j hj hand hout (fun k => decide (k = w))
        (V_orIn C hR _ (PEqualNP.TopForm.opnd C j 0) w h0 (by simp))
        (V_orIn C hR _ (PEqualNP.TopForm.opnd C j 1) w h1 (by simp))
      rw [hz1 w] at this
      exact Bool.false_ne_true this
    have hA2 : ∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 → ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v := by
      intro u hu v hv
      by_contra hnot
      have hne : u ≠ v := by
        intro h
        rw [h] at hu
        exact hA1 v hu hv
      have := and_gate_out C hAO j hj hand hout (fun k => decide (k = u ∨ k = v))
        (V_orIn C hR _ (PEqualNP.TopForm.opnd C j 0) u hu (by simp))
        (V_orIn C hR _ (PEqualNP.TopForm.opnd C j 1) v hv (by simp))
      rw [hz2 u v hne hnot] at this
      exact Bool.false_ne_true this
    have hA3 : (PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1 := by
      by_contra hcon
      obtain ⟨hc0, hc1⟩ := not_or.1 hcon
      obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.1 (by omega : 1 < (PEqualNP.TopForm.side (n := n) C j 0).card)
      obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.1 (by omega : 1 < (PEqualNP.TopForm.side (n := n) C j 1).card)
      have hsub : ({v1, v2} : Finset (Fin n)) ⊆ Finset.univ.filter (fun w => G.Adj u1 w ∧ G.Adj u2 w) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hw with rfl | rfl
        · exact ⟨hA2 u1 hu1 _ hv1, hA2 u2 hu2 _ hv1⟩
        · exact ⟨hA2 u1 hu1 _ hv2, hA2 u2 hu2 _ hv2⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_pair hv12] at hcard
      have := hFour u1 u2 hu12
      omega
    exact ⟨hA1, hA2, hA3⟩
  refine ⟨part1, ?_⟩
  intro F hF
  classical
  let good : ℕ → Prop := fun i => i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i
  let pick : ℕ → Finset (Fin n) := fun i => if (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1 then PEqualNP.TopForm.side (n := n) C i 0 else PEqualNP.TopForm.side (n := n) C i 1
  refine ⟨(F.filter good).biUnion pick, ?_, ?_⟩
  · calc ((F.filter good).biUnion pick).card ≤ (F.filter good).card * 1 :=
        Finset.card_biUnion_le_card_mul _ _ _ (by
          intro i hi
          obtain ⟨hiF, hg⟩ := Finset.mem_filter.1 hi
          have h3 := (part1 i hg.1 hg.2.1 hg.2.2).2.2
          show (if (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1 then PEqualNP.TopForm.side (n := n) C i 0 else PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1
          split_ifs with hc
          · exact hc
          · rcases h3 with h3 | h3
            · exact absurd h3 hc
            · exact h3)
      _ ≤ F.card := by
        rw [mul_one]
        exact Finset.card_filter_le _ _
  · intro e he
    obtain ⟨i, hiF, hi1, hi2, hi3, hcross⟩ := hF e he
    have hgood : good i := ⟨hi1, hi2, hi3⟩
    have hmem : i ∈ F.filter good := Finset.mem_filter.2 ⟨hiF, hgood⟩
    by_cases hc : (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1
    · have hpick : pick i = PEqualNP.TopForm.side (n := n) C i 0 := by simp only [pick, hc, ↓reduceIte]
      rcases hcross with ⟨h1, _⟩ | ⟨h2, _⟩
      · left
        exact Finset.mem_biUnion.2 ⟨i, hmem, by rw [hpick]; exact h1⟩
      · right
        exact Finset.mem_biUnion.2 ⟨i, hmem, by rw [hpick]; exact h2⟩
    · have hpick : pick i = PEqualNP.TopForm.side (n := n) C i 1 := by simp only [pick, hc, ↓reduceIte]
      rcases hcross with ⟨_, h2⟩ | ⟨_, h1⟩
      · right
        exact Finset.mem_biUnion.2 ⟨i, hmem, by rw [hpick]; exact h2⟩
      · left
        exact Finset.mem_biUnion.2 ⟨i, hmem, by rw [hpick]; exact h1⟩
