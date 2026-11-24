import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3358

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_step_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl stepWire acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (stepWire acc g)]
    simp [stepWire]
    omega

private lemma foldl_step_getD (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl stepWire acc).getD i false = acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepWire acc g).length := by
      simp [stepWire]
      omega
    rw [ih (stepWire acc g) hi']
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private def effInputs (C : Circuit) (j : ℕ) : List ℕ :=
  let g := C.gates.getD j ⟨GateOp.or, []⟩
  (match g.op with
   | GateOp.not => g.inputs.take 1
   | _ => g.inputs).filter (· < 17 + j)

private lemma effInputs_lt {C : Circuit} {j w : ℕ} (hw : w ∈ effInputs C j) :
    w < 17 + j := by
  simp only [effInputs, List.mem_filter, decide_eq_true_eq] at hw
  exact hw.2

private lemma effInputs_len_le {C : Circuit} (hF : FanInTwo C) {j : ℕ} (hj : j < C.gates.length) :
    (effInputs C j).length ≤ 2 := by
  have hg : C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hlen : C.gates[j].inputs.length ≤ 2 := (hF C.gates[j] (List.getElem_mem hj)).2
  dsimp [effInputs]
  rw [hg]
  refine le_trans (List.length_filter_le _ _) ?_
  cases C.gates[j].op <;> simp [hlen]

private lemma effInputs_not_len_le {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (hnot : (C.gates.get ⟨j, hj⟩).op = GateOp.not) :
    (effInputs C j).length ≤ 1 := by
  have hg : C.gates.getD j ⟨GateOp.or, []⟩ = C.gates.get ⟨j, hj⟩ := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  dsimp [effInputs]
  rw [hg, hnot]
  exact le_trans (List.length_filter_le _ _) (by simp)

private lemma wires_getD_gate_congr (C : Circuit) (x10 x11 : List Bool)
    (hx10 : x10.length = 17) (hx11 : x11.length = 17) (j : ℕ) (hj : j < C.gates.length)
    (hdep : ∀ i ∈ effInputs C j, (C.wires x10).getD i false = (C.wires x11).getD i false) :
    (C.wires x10).getD (17 + j) false = (C.wires x11).getD (17 + j) false := by
  have htake : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have hdrop : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    conv_lhs => rw [← List.take_append_drop j C.gates, hdrop]
  have hgate_eval : ∀ x : List Bool, x.length = 17 →
      (C.wires x).getD (17 + j) false =
        C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
          if i < 17 + j then (C.wires x).getD i false else false) := by
    intro x hx
    let acc := (C.gates.take j).foldl stepWire x
    have hlen : acc.length = 17 + j := by
      dsimp [acc]
      rw [foldl_step_len, hx, List.length_take_of_le (Nat.le_of_lt hj)]
    have hwires : C.wires x = (C.gates.drop (j + 1)).foldl stepWire (stepWire acc C.gates[j]) := by
      rw [wires_eq_foldl]
      conv_lhs => rw [htake]
      rw [List.foldl_append, List.foldl_cons]
    have hget : (C.wires x).getD (17 + j) false = (stepWire acc C.gates[j]).getD (17 + j) false := by
      rw [hwires]
      apply foldl_step_getD
      simp [stepWire, hlen]
    rw [hget]
    have hlast : (stepWire acc C.gates[j]).getD (17 + j) false =
        C.gates[j].op.eval (C.gates[j].inputs.map fun i => acc.getD i false) := by
      simp [stepWire, hlen, List.getD_eq_getElem?_getD]
    rw [hlast]
    congr 1
    apply List.map_congr_left
    intro i _
    by_cases hi : i < 17 + j
    · simp only [hi, ↓reduceIte]
      have hi_acc : i < acc.length := by omega
      rw [hwires]
      have h1 : ((C.gates.drop (j + 1)).foldl stepWire (stepWire acc C.gates[j])).getD i false =
          (stepWire acc C.gates[j]).getD i false :=
        foldl_step_getD _ _ i (by simp [stepWire]; omega)
      rw [h1]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi_acc]
    · simp only [hi, ↓reduceIte]
      have hnot : ¬ i < acc.length := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hnot)]
  rw [hgate_eval x10 hx10, hgate_eval x11 hx11]
  have hg : C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  cases hop : C.gates[j].op
  · congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hilt : i < 17 + j
    · simp only [hilt, ↓reduceIte]
      apply hdep
      simp only [effInputs, hg, hop, List.mem_filter, decide_eq_true_eq]
      exact ⟨hi, hilt⟩
    · simp [hilt]
  · congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hilt : i < 17 + j
    · simp only [hilt, ↓reduceIte]
      apply hdep
      simp only [effInputs, hg, hop, List.mem_filter, decide_eq_true_eq]
      exact ⟨hi, hilt⟩
    · simp [hilt]
  · cases hinp : C.gates[j].inputs with
    | nil => rfl
    | cons a as =>
      simp only [List.map_cons, GateOp.eval, List.headD_cons]
      by_cases halt : a < 17 + j
      · simp only [halt, ↓reduceIte]
        congr 1
        apply hdep
        simp only [effInputs, hg, hop, hinp, List.take_succ_cons, List.take_zero,
          List.mem_filter, List.mem_singleton, decide_eq_true_eq]
        exact ⟨trivial, halt⟩
      · simp [halt]
  · congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hilt : i < 17 + j
    · simp only [hilt, ↓reduceIte]
      apply hdep
      simp only [effInputs, hg, hop, List.mem_filter, decide_eq_true_eq]
      exact ⟨hi, hilt⟩
    · simp [hilt]
  · congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hilt : i < 17 + j
    · simp only [hilt, ↓reduceIte]
      apply hdep
      simp only [effInputs, hg, hop, List.mem_filter, decide_eq_true_eq]
      exact ⟨hi, hilt⟩
    · simp [hilt]

private def reachStep (C : Circuit) (S : Finset ℕ) : Finset ℕ :=
  S ∪ S.biUnion (fun j => ((effInputs C j).filter (17 ≤ ·)).toFinset.image (· - 17))

private lemma reachStep_subset (C : Circuit) (S : Finset ℕ) : S ⊆ reachStep C S :=
  Finset.subset_union_left

private lemma reachStep_iter_subset (C : Circuit) (n : ℕ) (S : Finset ℕ) :
    S ⊆ (reachStep C)^[n] S := by
  induction n with
  | zero => exact Finset.Subset.rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact Finset.Subset.trans ih (reachStep_subset C _)

private lemma reachStep_subset_range (C : Circuit) {S : Finset ℕ}
    (hS : S ⊆ Finset.range C.gates.length) :
    reachStep C S ⊆ Finset.range C.gates.length := by
  intro x hx
  simp only [reachStep, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx
  rcases hx with hx | ⟨j, hj, w, ⟨hw1, _⟩, rfl⟩
  · exact hS hx
  · have hjlt := Finset.mem_range.mp (hS hj)
    have hwlt := effInputs_lt hw1
    exact Finset.mem_range.mpr (by omega)

private lemma reachStep_iter_subset_range (C : Circuit) (n : ℕ) {S : Finset ℕ}
    (hS : S ⊆ Finset.range C.gates.length) :
    (reachStep C)^[n] S ⊆ Finset.range C.gates.length := by
  induction n with
  | zero => exact hS
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact reachStep_subset_range C ih

private def reach (C : Circuit) (r : ℕ) : Finset ℕ :=
  if r < C.gates.length then (reachStep C)^[C.gates.length] {r} else ∅

private lemma reach_self {C : Circuit} {r : ℕ} (hr : r < C.gates.length) :
    r ∈ reach C r := by
  simp only [reach, hr, ↓reduceIte]
  exact reachStep_iter_subset C C.gates.length {r} (Finset.mem_singleton_self r)

private lemma reach_subset_range {C : Circuit} (r : ℕ) :
    reach C r ⊆ Finset.range C.gates.length := by
  by_cases hr : r < C.gates.length
  · simp only [reach, hr, ↓reduceIte]
    apply reachStep_iter_subset_range
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_range.mpr hr
  · simp [reach, hr]

private lemma reachStep_iter_fixed (C : Circuit) (r : ℕ) (hr : r < C.gates.length) :
    reachStep C ((reachStep C)^[C.gates.length] {r}) = (reachStep C)^[C.gates.length] {r} := by
  by_contra hne
  have hlt_all : ∀ n ≤ C.gates.length,
      (reachStep C)^[n] {r} ≠ reachStep C ((reachStep C)^[n] {r}) := by
    intro n hn heq
    apply hne
    have hconst : ∀ k, (reachStep C)^[n + k] {r} = (reachStep C)^[n] {r} := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [← Nat.add_assoc, Function.iterate_succ_apply', ih, ← heq]
    have hN : (reachStep C)^[C.gates.length] {r} = (reachStep C)^[n] {r} := by
      have := hconst (C.gates.length - n)
      rwa [Nat.add_sub_of_le hn] at this
    rw [hN, ← heq]
  have hcard : ∀ n ≤ C.gates.length, n + 1 ≤ ((reachStep C)^[n] {r}).card := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hn_le : n ≤ C.gates.length := Nat.le_of_lt hn
      have hne_n := hlt_all n hn_le
      have hss : (reachStep C)^[n] {r} ⊂ (reachStep C)^[n + 1] {r} := by
        rw [Function.iterate_succ_apply']
        exact Finset.ssubset_iff_subset_ne.mpr ⟨reachStep_subset C _, hne_n⟩
      have hlt_card := Finset.card_lt_card hss
      have := ih hn_le
      omega
  have h1 := hcard C.gates.length le_rfl
  have h2 : ((reachStep C)^[C.gates.length] {r}).card ≤ (Finset.range C.gates.length).card := by
    apply Finset.card_le_card
    apply reachStep_iter_subset_range
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_range.mpr hr
  rw [Finset.card_range] at h2
  omega

private lemma reach_closed {C : Circuit} {r j w : ℕ} (hj : j ∈ reach C r)
    (hw : w ∈ effInputs C j) (hw17 : 17 ≤ w) :
    w - 17 ∈ reach C r := by
  by_cases hr : r < C.gates.length
  · simp only [reach, hr, ↓reduceIte] at hj ⊢
    rw [← reachStep_iter_fixed C r hr]
    simp only [reachStep, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
      List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact Or.inr ⟨j, hj, w, ⟨hw, hw17⟩, rfl⟩
  · simp [reach, hr] at hj

private lemma reach_parent {C : Circuit} {r j : ℕ} (hj : j ∈ reach C r) :
    j = r ∨ ∃ k ∈ reach C r, 17 + j ∈ effInputs C k := by
  by_cases hr : r < C.gates.length
  · simp only [reach, hr, ↓reduceIte] at hj ⊢
    have hgen : ∀ n, ∀ x ∈ (reachStep C)^[n] {r},
        x = r ∨ ∃ k ∈ (reachStep C)^[n] {r}, 17 + x ∈ effInputs C k := by
      intro n
      induction n with
      | zero =>
        intro x hx
        rw [Function.iterate_zero, id_eq, Finset.mem_singleton] at hx
        exact Or.inl hx
      | succ n ih =>
        intro x hx
        rw [Function.iterate_succ_apply'] at hx
        simp only [reachStep, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
          List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx
        rcases hx with hx | ⟨k, hk, w, ⟨hw1, hw2⟩, rfl⟩
        · rcases ih x hx with rfl | ⟨k, hk, hmem⟩
          · exact Or.inl rfl
          · right
            refine ⟨k, ?_, hmem⟩
            rw [Function.iterate_succ_apply']
            exact reachStep_subset C _ hk
        · right
          refine ⟨k, ?_, ?_⟩
          · rw [Function.iterate_succ_apply']
            exact reachStep_subset C _ hk
          · have : 17 + (w - 17) = w := by omega
            rwa [this]
    exact hgen C.gates.length j hj
  · simp [reach, hr] at hj

private lemma reach_card_inputs_le {C : Circuit} (hF : FanInTwo C) (hsize : C.size ≤ 7)
    (x4 x5 : Fin C.gates.length) (hx45 : x4 < x5)
    (hx4 : (C.gates.get x4).op = GateOp.not) (hx5 : (C.gates.get x5).op = GateOp.not)
    (r : ℕ) (hr : r < C.gates.length) :
    ((reach C r).biUnion (fun j => ((effInputs C j).filter (· < 17)).toFinset)).card ≤ 6 := by
  let S := reach C r
  let x9 := S.biUnion (fun j => ((effInputs C j).filter (· < 17)).toFinset)
  change x9.card ≤ 6
  let pairs := S.biUnion (fun k => ((effInputs C k).map (fun i => (k, i))).toFinset)
  have hpairs_le : pairs.card ≤ ∑ k ∈ S, (effInputs C k).length := by
    refine le_trans Finset.card_biUnion_le ?_
    refine Finset.sum_le_sum ?_
    intro k _
    exact List.toFinset_card_le _ |>.trans (by simp)
  have hsum_le : ∑ k ∈ S, (effInputs C k).length ≤
      2 * S.card - (S ∩ ({x4.val, x5.val} : Finset ℕ)).card := by
    let N := S ∩ ({x4.val, x5.val} : Finset ℕ)
    have hsplit : ∑ k ∈ S, (effInputs C k).length =
        (∑ k ∈ N, (effInputs C k).length) + (∑ k ∈ S \ N, (effInputs C k).length) := by
      rw [← Finset.sum_sdiff (Finset.inter_subset_left : N ⊆ S)]
      rw [add_comm]
    have hN : ∑ k ∈ N, (effInputs C k).length ≤ ∑ _k ∈ N, 1 := by
      refine Finset.sum_le_sum ?_
      intro k hk
      have hk_in : k ∈ ({x4.val, x5.val} : Finset ℕ) := (Finset.mem_inter.mp hk).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk_in
      rcases hk_in with rfl | rfl
      · exact effInputs_not_len_le x4.isLt hx4
      · exact effInputs_not_len_le x5.isLt hx5
    have hSN : ∑ k ∈ S \ N, (effInputs C k).length ≤ ∑ _k ∈ S \ N, 2 := by
      refine Finset.sum_le_sum ?_
      intro k hk
      have hkS : k ∈ S := (Finset.mem_sdiff.mp hk).1
      have hk_lt : k < C.gates.length := Finset.mem_range.mp (reach_subset_range r hkS)
      exact effInputs_len_le hF hk_lt
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hN hSN
    have hcard_sdiff : (S \ N).card + N.card = S.card := by
      simp [N]
    have hN_le : N.card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
    dsimp only [N] at hsplit hcard_sdiff hN_le hN hSN
    omega
  have hx9_le : x9.card + (S.erase r).card ≤ pairs.card := by
    let k1 : ∀ p : x9, ℕ := fun p => Classical.choose (Finset.mem_biUnion.mp p.2)
    let A1 : Finset (ℕ × ℕ) := x9.attach.image (fun p => (k1 p, p.1))
    let A2 : Finset (ℕ × ℕ) := (S.erase r).attach.image (fun j =>
      (Classical.choose (Or.resolve_left (reach_parent (Finset.mem_erase.mp j.2).2)
        (Finset.mem_erase.mp j.2).1), 17 + j.1))
    have hA1_card : A1.card = x9.card := by
      rw [← Finset.card_attach (s := x9)]
      apply Finset.card_image_of_injOn
      intro p1 _ p2 _ heq
      exact Subtype.ext (congrArg Prod.snd heq)
    have hA2_card : A2.card = (S.erase r).card := by
      rw [← Finset.card_attach (s := S.erase r)]
      apply Finset.card_image_of_injOn
      intro j1 _ j2 _ heq
      have hsnd := congrArg Prod.snd heq
      dsimp at hsnd
      exact Subtype.ext (by omega)
    have hA1_sub : A1 ⊆ pairs := by
      intro xy hxy
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hxy
      have hspec := Classical.choose_spec (Finset.mem_biUnion.mp p.2)
      have hmem := List.mem_toFinset.mp hspec.2
      simp only [List.mem_filter, decide_eq_true_eq] at hmem
      simp only [pairs, Finset.mem_biUnion, List.mem_toFinset, List.mem_map]
      exact ⟨k1 p, hspec.1, p.1, hmem.1, rfl⟩
    have hA2_sub : A2 ⊆ pairs := by
      intro xy hxy
      obtain ⟨⟨j, hj⟩, _, rfl⟩ := Finset.mem_image.mp hxy
      have hj_ne := (Finset.mem_erase.mp hj).1
      have hj_S := (Finset.mem_erase.mp hj).2
      have hspec := Classical.choose_spec (Or.resolve_left (reach_parent hj_S) hj_ne)
      simp only [pairs, Finset.mem_biUnion, List.mem_toFinset, List.mem_map]
      exact ⟨_, hspec.1, 17 + j, hspec.2, rfl⟩
    have hA12_disj : Disjoint A1 A2 := by
      rw [Finset.disjoint_left]
      intro xy hxy1 hxy2
      obtain ⟨⟨p, hp⟩, _, rfl⟩ := Finset.mem_image.mp hxy1
      obtain ⟨⟨j, hj⟩, _, heq⟩ := Finset.mem_image.mp hxy2
      have hsnd := congrArg Prod.snd heq
      dsimp at hsnd
      have hspec := Classical.choose_spec (Finset.mem_biUnion.mp hp)
      have hmem := List.mem_toFinset.mp hspec.2
      simp only [List.mem_filter, decide_eq_true_eq] at hmem
      omega
    calc
      x9.card + (S.erase r).card = A1.card + A2.card := by rw [hA1_card, hA2_card]
      _ = (A1 ∪ A2).card := (Finset.card_union_of_disjoint hA12_disj).symm
      _ ≤ pairs.card := Finset.card_le_card (Finset.union_subset hA1_sub hA2_sub)
  have hr_S : r ∈ S := reach_self hr
  have hS_erase : (S.erase r).card = S.card - 1 := Finset.card_erase_of_mem hr_S
  have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨r, hr_S⟩
  have hS_le : S.card ≤ C.gates.length := by
    simpa using Finset.card_le_card (reach_subset_range r)
  have hgates_le : C.gates.length ≤ 7 := hsize
  have h1 : S.card = 6 → 1 ≤ (S ∩ ({x4.val, x5.val} : Finset ℕ)).card := by
    intro hm6
    by_contra h0
    have h0' : (S ∩ ({x4.val, x5.val} : Finset ℕ)).card = 0 := by omega
    have hdisj : Disjoint S ({x4.val, x5.val} : Finset ℕ) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0')
    have hunion : (S ∪ ({x4.val, x5.val} : Finset ℕ)).card = 8 := by
      rw [Finset.card_union_of_disjoint hdisj, hm6,
        Finset.card_pair (Fin.val_ne_of_ne hx45.ne)]
    have hsub : S ∪ ({x4.val, x5.val} : Finset ℕ) ⊆ Finset.range C.gates.length := by
      apply Finset.union_subset (reach_subset_range r)
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range, hunion] at hcard
    omega
  have h2 : S.card = 7 → 2 ≤ (S ∩ ({x4.val, x5.val} : Finset ℕ)).card := by
    intro hm7
    have hsub : ({x4.val, x5.val} : Finset ℕ) ⊆ S := by
      have hS_eq : S = Finset.range C.gates.length :=
        Finset.eq_of_subset_of_card_le (reach_subset_range r) (by simp; omega)
      rw [hS_eq]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp
    have hsub2 : ({x4.val, x5.val} : Finset ℕ) ⊆ S ∩ ({x4.val, x5.val} : Finset ℕ) :=
      Finset.subset_inter hsub Finset.Subset.rfl
    have hcard2 := Finset.card_le_card hsub2
    rw [Finset.card_pair (Fin.val_ne_of_ne hx45.ne)] at hcard2
    exact hcard2
  by_cases hm6 : S.card = 6
  · have := h1 hm6; omega
  · by_cases hm7 : S.card = 7
    · have := h2 hm7; omega
    · omega

end PEqualNP.Outside.L_meta_3358

theorem PEqualNP.Outside.L_meta_3358 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (7 : ℕ) → ∀ (x4 x5 : Fin x1.gates.length), x4 < x5 → (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ x9 ⊆ Finset.range (17 : ℕ), x9.card ≤ (6 : ℕ) ∧ ∀ (x10 x11 : List Bool), x10.length = (17 : ℕ) → x11.length = (17 : ℕ) → (∀ x14 ∈ x9, x10.getD x14 Bool.false = x11.getD x14 Bool.false) → x1.eval x10 = x1.eval x11 := by
  intro x1 hF hsize x4 x5 hx45 hx4 hx5
  by_cases hout17 : x1.output < 17
  · refine ⟨{x1.output}, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_singleton] at hz
      subst hz
      exact Finset.mem_range.mpr hout17
    · simp
    · intro x10 x11 hx10 hx11 hagree
      have h10 : x1.eval x10 = x10.getD x1.output false := by
        dsimp [PEqualNP.CircuitLowerBounds.Circuit.eval]
        rw [PEqualNP.Outside.L_meta_3358.wires_eq_foldl]
        exact PEqualNP.Outside.L_meta_3358.foldl_step_getD x1.gates x10 x1.output (by omega)
      have h11 : x1.eval x11 = x11.getD x1.output false := by
        dsimp [PEqualNP.CircuitLowerBounds.Circuit.eval]
        rw [PEqualNP.Outside.L_meta_3358.wires_eq_foldl]
        exact PEqualNP.Outside.L_meta_3358.foldl_step_getD x1.gates x11 x1.output (by omega)
      rw [h10, h11]
      exact hagree x1.output (Finset.mem_singleton_self _)
  · by_cases hout_hi : 17 + x1.gates.length ≤ x1.output
    · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      intro x10 x11 hx10 hx11 _
      have hlen10 : (x1.wires x10).length = 17 + x1.gates.length := by
        rw [PEqualNP.Outside.L_meta_3358.wires_eq_foldl,
          PEqualNP.Outside.L_meta_3358.foldl_step_len, hx10]
      have hlen11 : (x1.wires x11).length = 17 + x1.gates.length := by
        rw [PEqualNP.Outside.L_meta_3358.wires_eq_foldl,
          PEqualNP.Outside.L_meta_3358.foldl_step_len, hx11]
      dsimp [PEqualNP.CircuitLowerBounds.Circuit.eval]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    · let r := x1.output - 17
      have hr : r < x1.gates.length := by omega
      let S := PEqualNP.Outside.L_meta_3358.reach x1 r
      let x9 := S.biUnion (fun j =>
        ((PEqualNP.Outside.L_meta_3358.effInputs x1 j).filter (· < 17)).toFinset)
      refine ⟨x9, ?_, ?_, ?_⟩
      · intro z hz
        simp only [x9, Finset.mem_biUnion, List.mem_toFinset, List.mem_filter,
          decide_eq_true_eq] at hz
        rcases hz with ⟨_, _, _, hz17⟩
        exact Finset.mem_range.mpr hz17
      · exact PEqualNP.Outside.L_meta_3358.reach_card_inputs_le hF hsize x4 x5 hx45 hx4 hx5 r hr
      · intro x10 x11 hx10 hx11 hagree
        have hw_eq : ∀ w : ℕ, (w < 17 → w ∈ x9) → (17 ≤ w → w - 17 ∈ S) →
            (x1.wires x10).getD w false = (x1.wires x11).getD w false := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw1 hw2
            by_cases hw17 : w < 17
            · rw [PEqualNP.Outside.L_meta_3358.wires_eq_foldl x1 x10,
                PEqualNP.Outside.L_meta_3358.wires_eq_foldl x1 x11,
                PEqualNP.Outside.L_meta_3358.foldl_step_getD x1.gates x10 w (by omega),
                PEqualNP.Outside.L_meta_3358.foldl_step_getD x1.gates x11 w (by omega)]
              exact hagree w (hw1 hw17)
            · have hge17 : 17 ≤ w := Nat.le_of_not_lt hw17
              let j := w - 17
              have hj_S : j ∈ S := hw2 hge17
              have hj_lt : j < x1.gates.length :=
                Finset.mem_range.mp (PEqualNP.Outside.L_meta_3358.reach_subset_range r hj_S)
              have hw_eq_j : w = 17 + j := by omega
              rw [hw_eq_j]
              apply PEqualNP.Outside.L_meta_3358.wires_getD_gate_congr x1 x10 x11 hx10 hx11 j hj_lt
              intro i hi
              have hilt : i < 17 + j := PEqualNP.Outside.L_meta_3358.effInputs_lt hi
              apply ih i (by omega)
              · intro hi17
                simp only [x9, Finset.mem_biUnion, List.mem_toFinset, List.mem_filter,
                  decide_eq_true_eq]
                exact ⟨j, hj_S, hi, hi17⟩
              · intro hi17
                exact PEqualNP.Outside.L_meta_3358.reach_closed hj_S hi hi17
        dsimp [PEqualNP.CircuitLowerBounds.Circuit.eval]
        apply hw_eq x1.output (fun h => absurd h hout17)
        intro _
        exact PEqualNP.Outside.L_meta_3358.reach_self hr
