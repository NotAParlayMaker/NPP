import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem foldl_orStep (n : ℕ) (gs : List Gate) :
    (gs.foldl (orStep n) []).length = gs.length ∧
    ∀ k < gs.length, ∀ g : ℕ, g ∈ (gs.foldl (orStep n) []).getD k [] ↔
      (g = k ∨ ((gs.getD k ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + k ∧
          g ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs a ih =>
    obtain ⟨hlen, hmem⟩ := ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set R := gs.foldl (orStep n) [] with hR
    have hstep : orStep n R a = R ++ [R.length :: (if a.op = GateOp.or then
        (a.inputs.filter (fun w => decide (n ≤ w ∧ w < n + R.length))).flatMap
          (fun w => R.getD (w - n) []) else [])] := rfl
    rw [hstep]
    refine ⟨by simp [hlen], ?_⟩
    intro k hk g
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · have e1 : (R ++ [R.length :: (if a.op = GateOp.or then
          (a.inputs.filter (fun w => decide (n ≤ w ∧ w < n + R.length))).flatMap
            (fun w => R.getD (w - n) []) else [])]).getD k [] = R.getD k [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      have e2 : (gs ++ [a]).getD k ⟨GateOp.or, []⟩ = gs.getD k ⟨GateOp.or, []⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk,
          ← List.getD_eq_getElem?_getD]
      rw [e1, e2, hmem k hk g]
      constructor
      · rintro (h | ⟨h1, w, hw, h2, h3, h4⟩)
        · exact Or.inl h
        · refine Or.inr ⟨h1, w, hw, h2, h3, ?_⟩
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
            ← List.getD_eq_getElem?_getD]
          exact h4
      · rintro (h | ⟨h1, w, hw, h2, h3, h4⟩)
        · exact Or.inl h
        · refine Or.inr ⟨h1, w, hw, h2, h3, ?_⟩
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
            ← List.getD_eq_getElem?_getD] at h4
          exact h4
    · subst hk
      have e1 : (R ++ [R.length :: (if a.op = GateOp.or then
          (a.inputs.filter (fun w => decide (n ≤ w ∧ w < n + R.length))).flatMap
            (fun w => R.getD (w - n) []) else [])]).getD gs.length [] =
          R.length :: (if a.op = GateOp.or then
          (a.inputs.filter (fun w => decide (n ≤ w ∧ w < n + R.length))).flatMap
            (fun w => R.getD (w - n) []) else []) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp [hlen]
      have e2 : (gs ++ [a]).getD gs.length ⟨GateOp.or, []⟩ = a := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp
      rw [e1, e2, hlen]
      have e3 : ∀ (L : List ℕ) w, n ≤ w → w < n + gs.length →
          (R ++ [L]).getD (w - n) [] = R.getD (w - n) [] := by
        intro L w hw1 hw
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      rw [List.mem_cons]
      by_cases hop : a.op = GateOp.or
      · rw [if_pos hop]
        simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h | ⟨w, ⟨hw, h2, h3⟩, h4⟩)
          · exact Or.inl h
          · exact Or.inr ⟨hop, w, hw, h2, h3, by rw [e3 _ w h2 h3]; exact h4⟩
        · rintro (h | ⟨_, w, hw, h2, h3, h4⟩)
          · exact Or.inl h
          · exact Or.inr ⟨w, ⟨hw, h2, h3⟩, by rw [e3 _ w h2 h3] at h4; exact h4⟩
      · rw [if_neg hop]
        simp only [List.not_mem_nil, or_false]
        constructor
        · intro h; exact Or.inl h
        · rintro (h | ⟨h1, _⟩)
          · exact h
          · exact absurd h1 hop

theorem orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length :=
  (foldl_orStep n C.gates).1

theorem orSets_mem (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (g : ℕ) :
    g ∈ (orSets n C).getD k [] ↔
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ g ∈ (orSets n C).getD (w - n) [])) :=
  (foldl_orStep n C.gates).2 k hk g

theorem orSets_out (n : ℕ) (C : Circuit) (k : ℕ) (hk : C.gates.length ≤ k) :
    (orSets n C).getD k [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_len]; exact hk)]
  rfl

theorem orSets_le (n : ℕ) (C : Circuit) : ∀ k, ∀ g ∈ (orSets n C).getD k [], g ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    by_cases hk : k < C.gates.length
    · rcases (orSets_mem n C k hk g).mp hg with h | ⟨_, w, _, h2, h3, h4⟩
      · omega
      · have := ih (w - n) (by omega) g h4
        omega
    · rw [orSets_out n C k (by omega)] at hg
      simp at hg

theorem orSets_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hor : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (h2 : n ≤ w) (h3 : w < n + k) : ∀ g ∈ (orSets n C).getD (w - n) [], g ∈ (orSets n C).getD k [] :=
  fun g hg => (orSets_mem n C k hk g).mpr (Or.inr ⟨hor, w, hw, h2, h3, hg⟩)

theorem orSets_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    k ∈ (orSets n C).getD k [] :=
  (orSets_mem n C k hk k).mpr (Or.inl rfl)

theorem lowest_step (n : ℕ) (C : Circuit) : ∀ k, ∀ g ∈ (orSets n C).getD k [], g ≠ k →
    ∃ h ∈ (orSets n C).getD k [], (gateAt C h).op = GateOp.or ∧ n + g ∈ (gateAt C h).inputs := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg hne
    by_cases hk : k < C.gates.length
    · rcases (orSets_mem n C k hk g).mp hg with h | ⟨hor, w, hw, h2, h3, h4⟩
      · exact absurd h hne
      · by_cases hgw : g = w - n
        · refine ⟨k, orSets_self n C k hk, hor, ?_⟩
          have : n + g = w := by omega
          rw [this]; exact hw
        · obtain ⟨h, hh, hop, hin⟩ := ih (w - n) (by omega) g h4 hgw
          exact ⟨h, orSets_trans n C k hk hor w hw h2 h3 h hh, hop, hin⟩
    · rw [orSets_out n C k (by omega)] at hg
      simp at hg

theorem fibre_le (l : List ℕ) (hl : l.length = 2) (n : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, n + x ∈ l) : S.card ≤ 2 := by
  have hsub : S.image (fun x => n + x) ⊆ l.toFinset := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact List.mem_toFinset.mpr (hS x hx)
  have h1 : (S.image (fun x => n + x)).card = S.card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  have h2 := Finset.card_le_card hsub
  have h3 := List.toFinset_card_le l
  omega

end PEqualNP.Outside.L_meta_2233

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  classical
  intro n C F hC hF
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
    PEqualNP.Outside.L_meta_2233 in
  · set o := C.output - n with ho
    let D : Finset ℕ := (Finset.range C.gates.length).filter
      (fun i => (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i)
    have hD : Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i} = D.card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      simp [D]
    rw [hD]
    have hdisj : Disjoint F D := by
      rw [Finset.disjoint_left]
      intro x hxF hxD
      have h1 := (hF x hxF).2.1
      have h2 := (Finset.mem_filter.mp hxD).2.1
      rw [h1] at h2
      exact GateOp.noConfusion h2
    let X := F ∪ D
    have hX : X.card = F.card + D.card := Finset.card_union_of_disjoint hdisj
    have hXmem : ∀ x ∈ X, n ≤ C.output ∧ x ∈ (orSets n C).getD o [] := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (hF x hx).2.2
      · exact (Finset.mem_filter.mp hx).2.2
    have hpick : ∀ x ∈ X.erase o, ∃ h ∈ D, n + x ∈ (gateAt C h).inputs := by
      intro x hx
      obtain ⟨hxo, hxX⟩ := Finset.mem_erase.mp hx
      obtain ⟨hn, hxm⟩ := hXmem x hxX
      obtain ⟨h, hh, hop, hin⟩ := lowest_step n C o x hxm hxo
      have hle := orSets_le n C o h hh
      have hlt : o < C.gates.length := by
        by_contra hc
        rw [orSets_out n C o (by omega)] at hxm
        simp at hxm
      refine ⟨h, ?_, hin⟩
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, hop, ?_⟩
      exact ⟨hn, hh⟩
    choose! φ hφD hφin using hpick
    have hmaps : ∀ x ∈ X.erase o, φ x ∈ D := hφD
    have hcard : (X.erase o).card ≤ 2 * D.card := by
      have := Finset.card_le_mul_card_image_of_maps_to hmaps 2 (by
        intro h hh
        apply fibre_le (gateAt C h).inputs _ n
        · intro x hx
          rw [Finset.mem_filter] at hx
          rw [← hx.2]
          exact hφin x hx.1
        · have hhD := (Finset.mem_filter.mp hh).1
          rw [Finset.mem_range] at hhD
          have hmem : gateAt C h ∈ C.gates := by
            unfold gateAt
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hhD]
            exact List.getElem_mem hhD
          exact hC.2.2 _ hmem)
      linarith [mul_comm D.card 2]
    have h1 : X.card ≤ (X.erase o).card + 1 := by
      by_cases hoX : o ∈ X
      · rw [Finset.card_erase_add_one hoX]
      · rw [Finset.erase_eq_of_notMem hoX]; omega
    omega
