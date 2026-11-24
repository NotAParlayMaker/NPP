import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma orStep_length (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (orStep n cs g).length = cs.length + 1 := by
  unfold orStep
  simp

lemma orSets_foldl_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, orStep_length, List.length_cons]
    omega

lemma orSets_len (n : ℕ) (C : Circuit) :
    (orSets n C).length = C.gates.length := by
  unfold orSets
  rw [orSets_foldl_len]
  simp

lemma orSets_foldl_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [orStep_length]; omega)]
    unfold orStep
    exact List.getD_append _ _ _ _ hk

lemma orSets_getD_or (n : ℕ) (C : Circuit) (u : ℕ) (hu : u < C.gates.length)
    (hop : (gateAt C u).op = GateOp.or) :
    (orSets n C).getD u [] =
      u :: ((gateAt C u).inputs.filter (fun w => decide (n ≤ w ∧ w < n + u))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  let cs1 : List (List ℕ) := (C.gates.take u).foldl (orStep n) []
  have hcs1_len : cs1.length = u := by
    dsimp only [cs1]
    rw [orSets_foldl_len, List.length_nil, Nat.zero_add, List.length_take]
    omega
  have hsplit : orSets n C = (C.gates.drop (u + 1)).foldl (orStep n) (orStep n cs1 C.gates[u]) := by
    unfold orSets
    conv_lhs => rw [← List.take_append_drop u C.gates, List.drop_eq_getElem_cons hu, List.foldl_append, List.foldl_cons]
  have hget : (orSets n C).getD u [] = (orStep n cs1 C.gates[u]).getD u [] := by
    rw [hsplit]
    exact orSets_foldl_getD_lt n (C.gates.drop (u + 1)) (orStep n cs1 C.gates[u]) u
      (by rw [orStep_length, hcs1_len]; omega)
  have hgate : gateAt C u = C.gates[u] := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hu]
  have hop' : C.gates[u].op = GateOp.or := by rw [← hgate]; exact hop
  rw [hget, orStep]
  rw [List.getD_append_right _ _ _ _ (by rw [hcs1_len]), hcs1_len, Nat.sub_self,
    List.getD_cons_zero, hgate]
  simp only [hop', ↓reduceIte, List.cons.injEq, true_and]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hwlt : w - n < cs1.length := by rw [hcs1_len]; omega
  unfold orSets
  conv_rhs => rw [← List.take_append_drop u C.gates, List.foldl_append]
  exact (orSets_foldl_getD_lt n (C.gates.drop u) cs1 (w - n) hwlt).symm

lemma orSets_getD_ne_or (n : ℕ) (C : Circuit) (u : ℕ) (hu : u < C.gates.length)
    (hop : (gateAt C u).op ≠ GateOp.or) :
    (orSets n C).getD u [] = [u] := by
  let cs1 : List (List ℕ) := (C.gates.take u).foldl (orStep n) []
  have hcs1_len : cs1.length = u := by
    dsimp only [cs1]
    rw [orSets_foldl_len, List.length_nil, Nat.zero_add, List.length_take]
    omega
  have hsplit : orSets n C = (C.gates.drop (u + 1)).foldl (orStep n) (orStep n cs1 C.gates[u]) := by
    unfold orSets
    conv_lhs => rw [← List.take_append_drop u C.gates, List.drop_eq_getElem_cons hu, List.foldl_append, List.foldl_cons]
  have hget : (orSets n C).getD u [] = (orStep n cs1 C.gates[u]).getD u [] := by
    rw [hsplit]
    exact orSets_foldl_getD_lt n (C.gates.drop (u + 1)) (orStep n cs1 C.gates[u]) u
      (by rw [orStep_length, hcs1_len]; omega)
  have hgate : gateAt C u = C.gates[u] := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hu]
  have hop' : C.gates[u].op ≠ GateOp.or := by rw [← hgate]; exact hop
  rw [hget, orStep]
  rw [List.getD_append_right _ _ _ _ (by rw [hcs1_len]), hcs1_len, Nat.sub_self,
    List.getD_cons_zero]
  simp [hop']

lemma mem_orSets_self (n : ℕ) (C : Circuit) (u : ℕ) (hu : u < C.gates.length) :
    u ∈ (orSets n C).getD u [] := by
  by_cases hop : (gateAt C u).op = GateOp.or
  · rw [orSets_getD_or n C u hu hop]
    simp
  · rw [orSets_getD_ne_or n C u hu hop]
    simp

lemma mem_orSets_step (n : ℕ) (C : Circuit) :
    ∀ u < C.gates.length, ∀ x ∈ (orSets n C).getD u [],
      x = u ∨ ∃ h ∈ (orSets n C).getD u [],
        h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧ n + x ∈ (gateAt C h).inputs := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu x hx
    by_cases hop : (gateAt C u).op = GateOp.or
    · rw [orSets_getD_or n C u hu hop] at hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · right
        simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hx
        rcases hx with ⟨w, ⟨hwin, hwn, hwu⟩, hxw⟩
        have hvlt : w - n < u := by omega
        have hvlen : w - n < C.gates.length := by omega
        rcases ih (w - n) hvlt hvlen x hxw with rfl | ⟨h, hh_mem, hh_lt, hh_op, hh_in⟩
        · refine ⟨u, mem_orSets_self n C u hu, hu, hop, ?_⟩
          have heqw : n + (w - n) = w := by omega
          rw [heqw]
          exact hwin
        · refine ⟨h, ?_, hh_lt, hh_op, hh_in⟩
          rw [orSets_getD_or n C u hu hop]
          simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          right
          exact ⟨w, ⟨hwin, hwn, hwu⟩, hh_mem⟩
    · rw [orSets_getD_ne_or n C u hu hop, List.mem_singleton] at hx
      exact Or.inl hx

theorem main (n : ℕ) (C : Circuit) (F : Finset ℕ) (hAO : IsAO2 n C)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j) :
    F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i} + 1 := by
  classical
  let D : Finset ℕ :=
    (Finset.range C.gates.length).filter (fun i => (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i)
  have hncard : Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i} = D.card := by
    have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i} = (D : Set ℕ) := by
      ext i
      simp [D]
    rw [hset, Set.ncard_coe_finset]
  rw [hncard]
  by_cases hF0 : F = ∅
  · simp [hF0]
  · obtain ⟨j0, hj0⟩ := Finset.nonempty_iff_ne_empty.mpr hF0
    have hj0_or := (hF j0 hj0).2.2
    unfold OrReaches at hj0_or
    rcases hj0_or with ⟨hCn, hj0_mem⟩
    have hu_lt : C.output - n < C.gates.length := by
      by_contra hnot
      have hlen : (orSets n C).length ≤ C.output - n := by
        rw [orSets_len]
        omega
      rw [List.getD_eq_default _ _ hlen] at hj0_mem
      cases hj0_mem
    let u := C.output - n
    have hdisj : Disjoint F D := by
      rw [Finset.disjoint_left]
      intro j hjF hjD
      have hand := (hF j hjF).2.1
      have hor := (Finset.mem_filter.mp hjD).2.1
      rw [hand] at hor
      cases hor
    let X := F ∪ D
    have hXcard : X.card = F.card + D.card := Finset.card_union_of_disjoint hdisj
    let X' := X.erase u
    have hX'card : X.card - 1 ≤ X'.card := by
      by_cases huX : u ∈ X
      · have h1 := Finset.card_erase_add_one huX
        change X'.card + 1 = X.card at h1
        omega
      · dsimp only [X']
        rw [Finset.erase_eq_of_notMem huX]
        exact Nat.sub_le X.card 1
    let img := X'.image (fun x => n + x)
    have himg_card : img.card = X'.card :=
      Finset.card_image_of_injective _ (fun a b h => by omega)
    let target := D.biUnion (fun h => (gateAt C h).inputs.toFinset)
    have himg_sub : img ⊆ target := by
      intro y hy
      rw [Finset.mem_image] at hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [Finset.mem_erase] at hx
      rcases hx with ⟨hne, hxX⟩
      have hx_or : x ∈ (orSets n C).getD u [] := by
        rcases Finset.mem_union.mp hxX with hxF | hxD
        · exact (hF x hxF).2.2.2
        · exact (Finset.mem_filter.mp hxD).2.2.2
      rcases mem_orSets_step n C u hu_lt x hx_or with rfl | ⟨h, hh_mem, hh_lt, hh_op, hh_in⟩
      · exact (hne rfl).elim
      · rw [Finset.mem_biUnion]
        refine ⟨h, ?_, List.mem_toFinset.mpr hh_in⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr hh_lt, hh_op, ⟨hCn, hh_mem⟩⟩
    have htarget_card : target.card ≤ 2 * D.card := by
      calc
        target.card ≤ ∑ h ∈ D, (gateAt C h).inputs.toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ h ∈ D, (gateAt C h).inputs.length := by
          apply Finset.sum_le_sum
          intro h _
          exact List.toFinset_card_le _
        _ = ∑ _ ∈ D, 2 := by
          apply Finset.sum_congr rfl
          intro h hhD
          have hh_lt : h < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hhD).1
          unfold gateAt
          rw [List.getD_eq_getElem _ _ hh_lt]
          exact hAO.2.2 C.gates[h] (List.getElem_mem hh_lt)
        _ = 2 * D.card := by simp [Nat.mul_comm]
    have hle := le_trans (Finset.card_le_card himg_sub) htarget_card
    omega

end PEqualNP.Outside.L_meta_2233

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 :=
  PEqualNP.Outside.L_meta_2233.main
