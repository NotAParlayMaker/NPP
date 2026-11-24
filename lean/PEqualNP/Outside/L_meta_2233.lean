import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

open PEqualNP.CleanedNonEdge in
lemma mem_le (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ x, x ∈ (orSets n C).getD k [] → x ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx
    rcases (orSets_mem_iff n C k x hk).mp hx with h | ⟨_, w, _, hn, hlt, hx2⟩
    · omega
    · have := ih (w - n) (by omega) (by omega) x hx2
      omega

open PEqualNP.CleanedNonEdge in
lemma parent (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ x, x ∈ (orSets n C).getD k [] → x ≠ k →
      ∃ p, p ∈ (orSets n C).getD k [] ∧ (gateAt C p).op = GateOp.or ∧
        n + x ∈ (gateAt C p).inputs := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx hne
    rcases (orSets_mem_iff n C k x hk).mp hx with h | ⟨hop, w, hw, hn, hlt, hx2⟩
    · exact absurd h hne
    · by_cases hxw : x = w - n
      · refine ⟨k, (orSets_mem_iff n C k k hk).mpr (Or.inl rfl), hop, ?_⟩
        have : n + x = w := by omega
        rw [this]; exact hw
      · obtain ⟨p, hp, hpop, hpin⟩ := ih (w - n) (by omega) (by omega) x hx2 hxw
        exact ⟨p, (orSets_mem_iff n C k p hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hp⟩), hpop, hpin⟩

open PEqualNP.CleanedNonEdge in
lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp [orSets, orFold_length]

open PEqualNP.CleanedNonEdge in
lemma main (n : ℕ) (C : Circuit) (F : Finset ℕ)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j) :
    F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} + 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty F with hE | ⟨j0, hj0⟩
  · simp [hE]
  obtain ⟨_, _, hno, hj0r⟩ := hF j0 hj0
  have hr : C.output - n < C.gates.length := by
    by_contra hcon
    have : (orSets n C).getD (C.output - n) [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_length]; omega)]
      rfl
    rw [this] at hj0r
    simp at hj0r
  set r := C.output - n with hrdef
  set S : Finset ℕ := ((orSets n C).getD r []).toFinset with hS
  set O : Finset ℕ := S.filter (fun i => (gateAt C i).op = GateOp.or) with hO
  have hT : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = (O : Set ℕ) := by
    ext i
    simp only [Set.mem_setOf_eq, hO, hS, Finset.coe_filter, List.mem_toFinset, OrReaches]
    constructor
    · rintro ⟨_, hop, _, hi⟩
      exact ⟨hi, hop⟩
    · rintro ⟨hi, hop⟩
      have := mem_le n C r hr i hi
      exact ⟨by omega, hop, hno, hi⟩
  rw [hT, Set.ncard_coe_finset]
  have hOS : O ⊆ S := Finset.filter_subset _ _
  have hFS : F ⊆ S \ O := by
    intro j hj
    obtain ⟨_, hop, _, hjr⟩ := hF j hj
    rw [Finset.mem_sdiff]
    refine ⟨by rw [hS, List.mem_toFinset]; exact hjr, ?_⟩
    rw [hO, Finset.mem_filter]
    rintro ⟨_, hor⟩
    rw [hop] at hor
    cases hor
  have hc1 := Finset.card_le_card hFS
  have hc2 := Finset.card_sdiff_add_card_eq_card hOS
  have hrS : r ∈ S := by
    rw [hS, List.mem_toFinset]
    exact (orSets_mem_iff n C r r hr).mpr (Or.inl rfl)
  have hsub : S.erase r ⊆ (O ×ˢ Finset.range 2).image
      (fun p : ℕ × ℕ => (gateAt C p.1).inputs.getD p.2 0 - n) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hxr, hxS⟩ := hx
    rw [hS, List.mem_toFinset] at hxS
    obtain ⟨p, hp, hpop, hpin⟩ := parent n C r hr x hxS hxr
    have hpr := mem_le n C r hr p hp
    have hplen : p < C.gates.length := by omega
    have hlen : (gateAt C p).inputs.length = 2 := by
      rw [gateAt_eq C p hplen]
      exact h2 _ (List.getElem_mem hplen)
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hpin
    rw [Finset.mem_image]
    refine ⟨(p, i), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_range, hO, Finset.mem_filter, hS, List.mem_toFinset]
      exact ⟨⟨hp, hpop⟩, by omega⟩
    · show (gateAt C p).inputs.getD i 0 - n = x
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hix]
      omega
  have hc3 := Finset.card_le_card hsub
  have hc4 : ((O ×ˢ Finset.range 2).image
      (fun p : ℕ × ℕ => (gateAt C p.1).inputs.getD p.2 0 - n)).card ≤ O.card * 2 := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_range]
  rw [Finset.card_erase_of_mem hrS] at hc3
  omega

end PEqualNP.Outside.L_meta_2233

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hA hF
  exact PEqualNP.Outside.L_meta_2233.main n C F hA.2.2 hF
