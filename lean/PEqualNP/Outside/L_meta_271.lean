import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_271_aux

open PEqualNP.CircuitLowerBounds

/-- One evaluation step: the gate adds one wire. -/
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

/-- The inputs a wire can depend on, one set per wire: a gate adds the union over the wires
  it reads. -/
def dstep {n : ℕ} (d : List (Finset (Fin n))) (g : Gate) : List (Finset (Fin n)) :=
  d ++ [g.inputs.toFinset.biUnion fun i => d.getD i ∅]

/-- A wire has the same value on two inputs that agree on its dependency set. -/
theorem sem {n : ℕ} (x x' : Fin n → Bool) (gs : List Gate) :
    ∀ (W W' : List Bool) (D : List (Finset (Fin n))), W.length = D.length →
      W'.length = D.length →
      (∀ i, (∀ q ∈ D.getD i ∅, x q = x' q) → W.getD i false = W'.getD i false) →
      ∀ i, (∀ q ∈ (gs.foldl dstep D).getD i ∅, x q = x' q) →
        (gs.foldl stp W).getD i false = (gs.foldl stp W').getD i false := by
  induction gs with
  | nil => intro W W' D _ _ h i hi; exact h i hi
  | cons g gs ih =>
    intro W W' D hW hW' h
    simp only [List.foldl_cons]
    apply ih
    · simp [stp, dstep, hW]
    · simp [stp, dstep, hW']
    · intro i hi
      rcases lt_trichotomy i D.length with hlt | heq | hgt
      · have e : (dstep D g).getD i ∅ = D.getD i ∅ := List.getD_append _ _ _ _ hlt
        rw [e] at hi
        simp only [stp]
        rw [List.getD_append _ _ _ _ (hW ▸ hlt), List.getD_append _ _ _ _ (hW' ▸ hlt)]
        exact h i hi
      · subst heq
        have e : (dstep D g).getD D.length ∅
            = g.inputs.toFinset.biUnion fun i => D.getD i ∅ := by
          simp [dstep, List.getD_eq_getElem?_getD]
        rw [e] at hi
        have hv : g.inputs.map (fun i => W.getD i false)
            = g.inputs.map (fun i => W'.getD i false) := by
          apply List.map_congr_left
          intro a ha
          apply h
          intro q hq
          exact hi q (Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr ha, hq⟩)
        have e1 : (stp W g).getD D.length false
            = g.op.eval (g.inputs.map fun i => W.getD i false) := by
          rw [← hW]
          simp [stp, List.getD_eq_getElem?_getD]
        have e2 : (stp W' g).getD D.length false
            = g.op.eval (g.inputs.map fun i => W'.getD i false) := by
          rw [← hW']
          simp [stp, List.getD_eq_getElem?_getD]
        rw [e1, e2, hv]
      · have e1 : (stp W g).getD i false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [stp]; omega)]
          rfl
        have e2 : (stp W' g).getD i false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [stp]; omega)]
          rfl
        rw [e1, e2]

/-- The counting statement: the inputs reached from a set `T` of wires, outside `F`, are at
  most the wires of `T` that do not reach `F`, plus `c`. -/
def H {n : ℕ} (F : Finset (Fin n)) (d : ℕ → Finset (Fin n)) (c : ℕ) : Prop :=
  ∀ T : Finset ℕ, ((T.biUnion d) \ F).card ≤ (T.filter fun w => d w ∩ F = ∅).card + c

theorem filt_insert_le (P : ℕ → Prop) [DecidablePred P] (s : Finset ℕ) (a : ℕ) :
    ((insert a s).filter P).card ≤ (s.filter P).card + if P a then 1 else 0 := by
  rw [Finset.filter_insert]
  split_ifs
  · exact Finset.card_insert_le _ _
  · simp

theorem H_step {n : ℕ} (F : Finset (Fin n)) (d : ℕ → Finset (Fin n)) (c j a b : ℕ)
    (h : H F d c) : H F (Function.update d j (d a ∪ d b)) (c + 1) := by
  have hjv : Function.update d j (d a ∪ d b) j = d a ∪ d b := by simp
  have hne : ∀ w, w ≠ j → Function.update d j (d a ∪ d b) w = d w :=
    fun w hw => Function.update_of_ne hw _ _
  generalize Function.update d j (d a ∪ d b) = d' at hjv hne ⊢
  intro T
  by_cases hj : j ∈ T
  · have hsub : T.biUnion d' ⊆ (insert a (insert b (T.erase j))).biUnion d := by
      intro q hq
      obtain ⟨w, hw, hq⟩ := Finset.mem_biUnion.mp hq
      by_cases e : w = j
      · subst e
        rw [hjv, Finset.mem_union] at hq
        rcases hq with hq | hq
        · exact Finset.mem_biUnion.mpr ⟨a, by simp, hq⟩
        · exact Finset.mem_biUnion.mpr ⟨b, by simp, hq⟩
      · rw [hne w e] at hq
        exact Finset.mem_biUnion.mpr ⟨w, by simp [e, hw], hq⟩
    have h1 : ((T.biUnion d') \ F).card
        ≤ (((insert a (insert b (T.erase j))).biUnion d) \ F).card :=
      Finset.card_le_card (Finset.sdiff_subset_sdiff hsub subset_rfl)
    have h2 := h (insert a (insert b (T.erase j)))
    have h3a := filt_insert_le (fun w => d w ∩ F = ∅) (insert b (T.erase j)) a
    have h3b := filt_insert_le (fun w => d w ∩ F = ∅) (T.erase j) b
    have hfc : (T.erase j).filter (fun w => d' w ∩ F = ∅)
        = (T.erase j).filter (fun w => d w ∩ F = ∅) := by
      apply Finset.filter_congr
      intro w hw
      rw [hne w (Finset.ne_of_mem_erase hw)]
    have h4 : (T.filter fun w => d' w ∩ F = ∅).card
        = ((T.erase j).filter fun w => d w ∩ F = ∅).card
          + (if (d a ∪ d b) ∩ F = ∅ then 1 else 0) := by
      have hT : T.filter (fun w => d' w ∩ F = ∅)
          = (insert j (T.erase j)).filter (fun w => d' w ∩ F = ∅) := by
        rw [Finset.insert_erase hj]
      rw [hT, Finset.filter_insert, hjv, hfc]
      split_ifs
      · rw [Finset.card_insert_of_notMem (by simp)]
      · simp
    have h5 : (if d a ∩ F = ∅ then 1 else 0) + (if d b ∩ F = ∅ then 1 else 0)
        ≤ (if (d a ∪ d b) ∩ F = ∅ then 1 else 0) + 1 := by
      have hiff : (d a ∪ d b) ∩ F = ∅ ↔ d a ∩ F = ∅ ∧ d b ∩ F = ∅ := by
        rw [Finset.union_inter_distrib_right, Finset.union_eq_empty]
      by_cases ha : d a ∩ F = ∅ <;> by_cases hb : d b ∩ F = ∅ <;> simp [hiff, ha, hb]
    omega
  · have hu : T.biUnion d' = T.biUnion d := by
      apply Finset.biUnion_congr rfl
      intro w hw
      exact hne w (fun e => hj (e ▸ hw))
    have hf : T.filter (fun w => d' w ∩ F = ∅) = T.filter (fun w => d w ∩ F = ∅) := by
      apply Finset.filter_congr
      intro w hw
      rw [hne w (fun e => hj (e ▸ hw))]
    rw [hu, hf]
    have := h T
    omega

theorem getD_dstep {n : ℕ} (D : List (Finset (Fin n))) (g : Gate) (a b : ℕ)
    (hg : g.inputs = [a, b]) :
    (fun i => (dstep D g).getD i ∅)
      = Function.update (fun i => D.getD i ∅) D.length (D.getD a ∅ ∪ D.getD b ∅) := by
  funext i
  rcases lt_trichotomy i D.length with hlt | heq | hgt
  · rw [Function.update_of_ne (Nat.ne_of_lt hlt)]
    exact List.getD_append _ _ _ _ hlt
  · subst heq
    simp [dstep, hg, List.getD_eq_getElem?_getD]
  · rw [Function.update_of_ne (Nat.ne_of_gt hgt)]
    have e1 : (dstep D g).getD i ∅ = ∅ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [dstep]; omega)]
      rfl
    have e2 : D.getD i ∅ = ∅ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [e1, e2]

theorem H_list {n : ℕ} (F : Finset (Fin n)) (gs : List Gate) :
    ∀ (D : List (Finset (Fin n))) (c : ℕ), (∀ g ∈ gs, g.inputs.length = 2) →
      H F (fun i => D.getD i ∅) c →
      H F (fun i => (gs.foldl dstep D).getD i ∅) (c + gs.length) := by
  induction gs with
  | nil => intro D c _ h; simpa using h
  | cons g gs ih =>
    intro D c hg h
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hg g (by simp))
    have h1 := H_step F (fun i => D.getD i ∅) c D.length a b h
    rw [← getD_dstep D g a b hab] at h1
    have h2 := ih (dstep D g) (c + 1) (fun g' hg' => hg g' (by simp [hg'])) h1
    have e : c + (g :: gs).length = c + 1 + gs.length := by simp; omega
    rw [e]
    exact h2

theorem H_small {n : ℕ} (F : Finset (Fin n)) (d : ℕ → Finset (Fin n))
    (hcard : ∀ i, (d i).card ≤ 1) : H F d 0 := by
  intro T
  have hsub : (T.biUnion d) \ F ⊆ (T.filter fun w => d w ∩ F = ∅).biUnion d := by
    intro q hq
    rw [Finset.mem_sdiff, Finset.mem_biUnion] at hq
    obtain ⟨⟨w, hw, hqw⟩, hqF⟩ := hq
    have hs : d w = {q} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hqw, fun y hy => Finset.card_le_one.mp (hcard w) y hy q hqw⟩
    refine Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, ?_⟩, hqw⟩
    rw [hs]
    simp [hqF]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le_card_mul (T.filter fun w => d w ∩ F = ∅) d 1
    (fun i _ => hcard i)
  omega

theorem H_base {n : ℕ} (F : Finset (Fin n)) :
    H F (fun i => (List.ofFn fun p : Fin n => ({p} : Finset (Fin n))).getD i ∅) 0 := by
  apply H_small
  intro i
  by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]

end PEqualNP.Outside.L_meta_271_aux

open PEqualNP.Outside.L_meta_271_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_271 : ∀ (n k : ℕ) (S₁ S₂ : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o₁ o₂ : ℕ), (S₁ ∩ S₂).card ≤ 1 → 2 ≤ S₁.card → 2 ≤ S₂.card → S₁.card ≤ k + 1 → S₂.card ≤ k + 1 → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o₁ false = true ↔ p ∈ S₁) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o₂ false = true ↔ p ∈ S₂) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S₁, x q = false) → (C.wires (List.ofFn x)).getD o₁ false = false) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S₂, x q = false) → (C.wires (List.ofFn x)).getD o₂ false = false) → S₁.card + S₂.card ≤ C.size + 2 := by
  intro n k S₁ S₂ C o₁ o₂ hI h1 h2 _ _ hG hA1 hA2 hB1 hB2
  -- every index of an output set is reached from that output
  have reach : ∀ (S : Finset (Fin n)) (o : ℕ),
      (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o false = true
        ↔ p ∈ S) →
      (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
        (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD o false = false) →
      S ⊆ (C.gates.foldl dstep (List.ofFn fun p : Fin n => ({p} : Finset (Fin n)))).getD o ∅ := by
    intro S o hA hB p hp
    by_contra hnot
    have hs := sem (fun q : Fin n => decide (q = p)) (fun _ => false) C.gates
      (List.ofFn (fun q : Fin n => decide (q = p))) (List.ofFn (fun _ : Fin n => false))
      (List.ofFn fun p : Fin n => ({p} : Finset (Fin n))) (by simp) (by simp)
      (by
        intro i hi
        by_cases hin : i < n
        · simp [List.getD_eq_getElem?_getD, hin] at hi ⊢
          exact hi
        · simp [List.getD_eq_getElem?_getD, hin])
      o (by
        intro q hq
        have : q ≠ p := fun e => hnot (e ▸ hq)
        simp [this])
    have ht := (hA p).mpr hp
    have hf := hB (fun _ => false) (by simp) (by simp)
    rw [wires_eq] at ht hf
    rw [ht, hf] at hs
    exact Bool.noConfusion hs
  have r1 := reach S₁ o₁ hA1 hB1
  have r2 := reach S₂ o₂ hA2 hB2
  have hH := H_list (S₁ ∩ S₂) C.gates (List.ofFn fun p : Fin n => ({p} : Finset (Fin n))) 0
    (fun g hg => (hG g hg).2) (H_base (S₁ ∩ S₂)) {o₁, o₂}
  generalize (C.gates.foldl dstep (List.ofFn fun p : Fin n => ({p} : Finset (Fin n)))) = D
    at r1 r2 hH
  beta_reduce at hH
  have hsub : (S₁ ∪ S₂) \ (S₁ ∩ S₂)
      ⊆ (({o₁, o₂} : Finset ℕ).biUnion fun i => D.getD i ∅) \ (S₁ ∩ S₂) := by
    apply Finset.sdiff_subset_sdiff _ subset_rfl
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact Finset.mem_biUnion.mpr ⟨o₁, by simp, r1 hq⟩
    · exact Finset.mem_biUnion.mpr ⟨o₂, by simp, r2 hq⟩
  have c1 := Finset.card_le_card hsub
  have c2 := Finset.card_union_add_card_inter S₁ S₂
  have c3 := Finset.card_sdiff_add_card_inter (S₁ ∪ S₂) (S₁ ∩ S₂)
  have c4 : (S₁ ∪ S₂) ∩ (S₁ ∩ S₂) = S₁ ∩ S₂ := by
    apply Finset.inter_eq_right.mpr
    exact Finset.inter_subset_left.trans Finset.subset_union_left
  rw [c4] at c3
  have hsz : C.size = C.gates.length := rfl
  rcases Nat.eq_zero_or_pos (S₁ ∩ S₂).card with h0 | hpos
  · have c5 : (({o₁, o₂} : Finset ℕ).filter fun w => D.getD w ∅ ∩ (S₁ ∩ S₂) = ∅).card ≤ 2 :=
      (Finset.card_filter_le _ _).trans Finset.card_le_two
    omega
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    have c5 : (({o₁, o₂} : Finset ℕ).filter fun w => D.getD w ∅ ∩ (S₁ ∩ S₂) = ∅) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw hemp
      have hp1 := Finset.mem_inter.mp hp
      have hin : p ∈ D.getD w ∅ ∩ (S₁ ∩ S₂) := by
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_inter.mpr ⟨r1 hp1.1, hp⟩
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_inter.mpr ⟨r2 hp1.2, hp⟩
      rw [hemp] at hin
      simp at hin
    rw [c5] at hH
    simp only [Finset.card_empty] at hH
    omega
