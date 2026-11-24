import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2233_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

theorem exit_bound (Q : Finset ℕ) (r : ℕ) (hr : r ∈ Q)
    (inputs : ℕ → Finset ℕ) (fanin : ∀ j ∈ Q, (inputs j).card ≤ 2)
    (parent : ∀ j ∈ Q, j ≠ r → ∃ a ∈ Q, j ∈ inputs a) :
    ((Q.biUnion inputs) \ Q).card ≤ Q.card + 1 := by
  classical
  let U := Q.biUnion inputs
  have hsub : Q.erase r ⊆ U := by
    intro j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    obtain ⟨a, ha, hja⟩ := parent j hj hne
    exact Finset.mem_biUnion.mpr ⟨a, ha, hja⟩
  have hd : Disjoint (U \ Q) (Q.erase r) := by
    apply Finset.disjoint_left.mpr
    intro j hj hq
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_of_mem_erase hq)
  have hc : (U \ Q).card + (Q.erase r).card ≤ 2 * Q.card := by
    calc
      (U \ Q).card + (Q.erase r).card = ((U \ Q) ∪ Q.erase r).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ U.card := Finset.card_le_card (Finset.union_subset Finset.sdiff_subset hsub)
      _ ≤ ∑ j ∈ Q, (inputs j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Q, 2 := Finset.sum_le_sum fanin
      _ = 2 * Q.card := by simp [Nat.mul_comm]
  have he := Finset.card_erase_add_one hr
  change (U \ Q).card ≤ Q.card + 1
  omega


theorem parent_reach (n : ℕ) (C : Circuit) (r j : ℕ)
    (hr : OrReaches n C (n+r) j) (hne : j ≠ r) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op = GateOp.or ∧
      OrReaches n C (n+r) a ∧ n+j ∈ (gateAt C a).inputs := by
  have hp := (orReaches_reach j (n+r) hr).1
  rcases Relation.ReflTransGen.cases_tail hp with he | ⟨v, hv, hs⟩
  · exfalso
    apply hne
    omega
  · obtain ⟨a, ha, rfl, hop, hin, _⟩ := hs
    exact ⟨a, ha, hop, reach_orReaches hv a rfl ha, hin⟩

end PEqualNP.Outside.L_meta_2233_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_2233_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by

  classical
  intro n C F hC hF
  by_cases hnon : F.Nonempty
  · obtain ⟨j0, hj0⟩ := hnon
    have hreach0 := (hF j0 hj0).2.2
    have hn : n ≤ C.output := hreach0.1
    let r := C.output - n
    have hout : C.output = n+r := by dsimp [r]; omega
    have hrlt : r < C.gates.length := by
      rw [hout] at hreach0
      exact ((orReaches_iff n C r j0).mp hreach0).1
    by_cases hor : (gateAt C r).op = GateOp.or
    · let Q := (Finset.range C.gates.length).filter
        (fun a => (gateAt C a).op = GateOp.or ∧ OrReaches n C (n+r) a)
      let inputs := fun a => ((gateAt C a).inputs.toFinset).image (fun v => v-n)
      have memQ : ∀ a, a ∈ Q ↔ a < C.gates.length ∧
          (gateAt C a).op = GateOp.or ∧ OrReaches n C (n+r) a := by
        intro a
        simp only [Q, Finset.mem_filter, Finset.mem_range]
      have hrQ : r ∈ Q := (memQ r).mpr
        ⟨hrlt, hor, (orReaches_iff n C r r).mpr ⟨hrlt, Or.inl rfl⟩⟩
      have hin : ∀ a j, n+j ∈ (gateAt C a).inputs → j ∈ inputs a := by
        intro a j hj
        exact Finset.mem_image.mpr ⟨n+j, List.mem_toFinset.mpr hj, by omega⟩
      have hparent : ∀ j ∈ Q, j ≠ r → ∃ a ∈ Q, j ∈ inputs a := by
        intro j hj hne
        obtain ⟨a, ha, hop, hre, hja⟩ := parent_reach n C r j ((memQ j).mp hj).2.2 hne
        exact ⟨a, (memQ a).mpr ⟨ha, hop, hre⟩, hin a j hja⟩
      have hfanin : ∀ a ∈ Q, (inputs a).card ≤ 2 := by
        intro a ha
        have hlt := ((memQ a).mp ha).1
        have hg : gateAt C a ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem _ _ hlt]
          exact List.getElem_mem hlt
        calc
          (inputs a).card ≤ (gateAt C a).inputs.toFinset.card := Finset.card_image_le
          _ ≤ (gateAt C a).inputs.length := List.toFinset_card_le _
          _ = 2 := hC.2.2 _ hg
      have hsub : F ⊆ (Q.biUnion inputs) \ Q := by
        intro j hj
        obtain ⟨hjlt, hjand, hjreach⟩ := hF j hj
        rw [hout] at hjreach
        have hne : j ≠ r := by
          intro he
          subst j
          rw [hor] at hjand
          cases hjand
        obtain ⟨a, ha, hop, hre, hja⟩ := parent_reach n C r j hjreach hne
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr
          ⟨a, (memQ a).mpr ⟨ha, hop, hre⟩, hin a j hja⟩, ?_⟩
        intro hjQ
        have he := ((memQ j).mp hjQ).2.1
        rw [hjand] at he
        cases he
      have hb := exit_bound Q r hrQ inputs hfanin hparent
      have hcard : Set.ncard {i : ℕ | i < C.gates.length ∧
          (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i} = Q.card := by
        have he : {i : ℕ | i < C.gates.length ∧
            (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i} = (Q : Set ℕ) := by
          ext i
          simp only [Set.mem_setOf_eq, Finset.mem_coe, memQ, hout]
        rw [he, Set.ncard_coe_finset]
      rw [hcard]
      exact le_trans (Finset.card_le_card hsub) hb
    · have hsub : F ⊆ {r} := by
        intro j hj
        have hjreach := (hF j hj).2.2
        rw [hout] at hjreach
        rcases ((orReaches_iff n C r j).mp hjreach).2 with he | he
        · exact Finset.mem_singleton.mpr he
        · exact (hor he.1).elim
      have hc := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hc
      omega
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
    simp [he]
