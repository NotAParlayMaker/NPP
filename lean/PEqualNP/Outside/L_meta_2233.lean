import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

namespace PEqualNP.Outside.L_meta_2233

-- The closure recurrence below is adapted from the project's L-meta-1505.
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


lemma reachableReader (n : ℕ) (C : Circuit) (x : ℕ) : ∀ k,
    k < C.gates.length → x ∈ (orSets n C).getD k [] → x ≠ k →
    ∃ p < C.gates.length, p ∈ (orSets n C).getD k [] ∧
      (gateAt C p).op = .or ∧ n + x ∈ (gateAt C p).inputs := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hx hne
    rcases (orSets_mem_iff n C k x hk).1 hx with heq | ⟨hop, w, hw, hn, hlt, hxw⟩
    · exact (hne heq).elim
    by_cases he : x = w - n
    · refine ⟨k, hk, (orSets_mem_iff n C k k hk).2 (Or.inl rfl), hop, ?_⟩
      have eq : n + x = w := by omega
      exact eq ▸ hw
    · obtain ⟨p, hp, hreach, hpor, hread⟩ :=
        ih (w - n) (by omega) (by omega) hxw he
      exact ⟨p, hp, (orSets_mem_iff n C k p hk).2 (Or.inr ⟨hop, w, hw, hn, hlt, hreach⟩),
        hpor, hread⟩

end PEqualNP.Outside.L_meta_2233

open PEqualNP.Outside.L_meta_2233

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hAO hF
  classical
  let Root := C.output - n
  let S := (Finset.range C.gates.length).filter fun i =>
    (gateAt C i).op = .or ∧ OrReaches n C C.output i
  let X := F ∪ S
  have hset : (S : Set ℕ) = {i | i < C.gates.length ∧
      (gateAt C i).op = .or ∧ OrReaches n C C.output i} := by
    ext i
    simp [S]
  rw [← hset, Set.ncard_coe_finset]
  by_cases hFE : F.Nonempty
  · obtain ⟨x, hx⟩ := hFE
    have hout : n ≤ C.output := (hF x hx).2.2.1
    have hRoot : Root < C.gates.length := by
      have hm := (hF x hx).2.2.2
      change x ∈ (orSets n C).getD Root [] at hm
      by_contra! h
      have hlen : (orSets n C).length = C.gates.length := by simp [orSets, orFold_length]
      have hnone : (orSets n C)[Root]? = none := List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hnone] at hm
    let inputs (j : ℕ) := (gateAt C j).inputs.toFinset
    let embed : ℕ ↪ ℕ := ⟨fun j => n + j, fun _ _ h => Nat.add_left_cancel h⟩
    have hsub : (X.erase Root).map embed ⊆ S.biUnion inputs := by
      intro w hw
      rcases Finset.mem_map.mp hw with ⟨j, hj, rfl⟩
      have hreach : OrReaches n C C.output j := by
        rcases Finset.mem_union.mp (Finset.mem_erase.mp hj).2 with hjF | hjS
        · exact (hF j hjF).2.2
        · exact (Finset.mem_filter.mp hjS).2.2
      obtain ⟨p, hp, hpreach, hpor, hread⟩ :=
        reachableReader n C j Root hRoot hreach.2 (Finset.mem_erase.mp hj).1
      apply Finset.mem_biUnion.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, hpor, hout, hpreach⟩, ?_⟩
      exact List.mem_toFinset.mpr hread
    have hcount : (X.erase Root).card ≤ S.card * 2 := by
      calc
        (X.erase Root).card = ((X.erase Root).map embed).card := (Finset.card_map _).symm
        _ ≤ (S.biUnion inputs).card := Finset.card_le_card hsub
        _ ≤ S.card * 2 := by
          apply Finset.card_biUnion_le_card_mul
          intro p hp
          have ph : p < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
          have hpg : gateAt C p ∈ C.gates := by simp [gateAt_eq C p ph]
          exact (List.toFinset_card_le _).trans (le_of_eq (hAO.2.2 _ hpg))
    have hUnion : X.card = F.card + S.card := by
      apply Finset.card_union_of_disjoint
      apply Finset.disjoint_left.mpr
      intro j hjF hjS
      have heq := (hF j hjF).2.1.symm.trans (Finset.mem_filter.mp hjS).2.1
      cases heq
    have hErase : X.card ≤ (X.erase Root).card + 1 := by
      have hSub : X ⊆ insert Root (X.erase Root) := by
        intro i hi
        by_cases h : i = Root
        · exact Finset.mem_insert.mpr (Or.inl h)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨h, hi⟩))
      exact (Finset.card_le_card hSub).trans (Finset.card_insert_le _ _)
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hFE]
