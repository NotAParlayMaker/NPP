import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3124

private def wireDeps (x1 : List ℕ) (i : ℕ) : Finset (Fin 9) :=
  if h : i < 9 then {⟨i, h⟩}
  else if i = 9 then {0}
  else if i = 10 then
    (x1.foldr (fun j acc =>
      (if hj : j < 9 then {⟨j, hj⟩} else if j = 9 then {0} else ∅) ∪ acc) ∅)
  else ∅

private lemma wireDeps_card_le_two_base (l : List ℕ) (hl : l.length ≤ 2) :
    (l.foldr (fun j acc =>
      (if hj : j < 9 then {⟨j, hj⟩} else if j = 9 then {0} else (∅ : Finset (Fin 9))) ∪ acc) ∅).card ≤ 2 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp
  · simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
    split_ifs <;> simp
  · simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
    have ha : (if hj : a < 9 then ({⟨a, hj⟩} : Finset (Fin 9)) else if a = 9 then {0} else ∅).card ≤ 1 := by
      split_ifs <;> simp
    have hb : (if hj : b < 9 then ({⟨b, hj⟩} : Finset (Fin 9)) else if b = 9 then {0} else ∅).card ≤ 1 := by
      split_ifs <;> simp
    exact le_trans (Finset.card_union_le _ _) (by omega)
  · simp at hl

private lemma ind_number_petersen_minus_one :
    ∀ S : Finset (Fin 9), S.card ≤ 4 →
      let x7 : Fin 9 → Bool := fun v => decide (v ∉ S)
      (x7 0 && x7 1 || x7 1 && x7 2 || x7 2 && x7 3 || x7 3 && x7 4 || x7 4 && x7 0 ||
        x7 0 && x7 5 || x7 1 && x7 6 || x7 2 && x7 7 || x7 3 && x7 8 ||
        x7 5 && x7 7 || x7 6 && x7 8 || x7 8 && x7 5) = Bool.true := by
  intro S hS
  by_contra h
  have h58 : (S ∩ {5, 6, 7, 8}).card ≥ 2 := by
    by_cases h5 : (5 : Fin 9) ∈ S
    · by_cases h8 : (8 : Fin 9) ∈ S
      · have : ({5, 8} : Finset (Fin 9)) ⊆ S ∩ {5, 6, 7, 8} := by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [*]
        exact le_trans (by decide : ({5, 8} : Finset (Fin 9)).card ≥ 2) (Finset.card_le_card this)
      · have h6 : (6 : Fin 9) ∈ S := by by_contra h6; apply h; simp [h8, h6]
        have : ({5, 6} : Finset (Fin 9)) ⊆ S ∩ {5, 6, 7, 8} := by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [*]
        exact le_trans (by decide : ({5, 6} : Finset (Fin 9)).card ≥ 2) (Finset.card_le_card this)
    · have h7 : (7 : Fin 9) ∈ S := by by_contra h7; apply h; simp [h5, h7]
      have h8 : (8 : Fin 9) ∈ S := by by_contra h8; apply h; simp [h5, h8]
      have : ({7, 8} : Finset (Fin 9)) ⊆ S ∩ {5, 6, 7, 8} := by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [*]
      exact le_trans (by decide : ({7, 8} : Finset (Fin 9)).card ≥ 2) (Finset.card_le_card this)
  have h04 : (S ∩ {0, 1, 2, 3, 4}).card ≥ 3 := by
    by_contra hlt
    by_cases h0 : (0 : Fin 9) ∈ S <;> by_cases h1 : (1 : Fin 9) ∈ S <;> by_cases h2 : (2 : Fin 9) ∈ S <;>
      by_cases h3 : (3 : Fin 9) ∈ S <;> by_cases h4 : (4 : Fin 9) ∈ S
    all_goals
      try (apply h; simp [h0, h1, h2, h3, h4]; done)
    all_goals
      exfalso
      apply hlt
      -- 5choose3+ cases where >=3 are in S:
      have : ∀ (s : Finset (Fin 9)), s ⊆ S ∩ {0, 1, 2, 3, 4} → s.card ≥ 3 → (S ∩ {0, 1, 2, 3, 4}).card ≥ 3 :=
        fun s hs hsc => le_trans hsc (Finset.card_le_card hs)
      first
      | exact this {0, 1, 2} (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [*]) (by decide)
      | exact this {0, 1, 3} (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [*]) (by decide)
      | exact this {0, 1, 4} (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [*]) (by decide)
      | exact this {0, 2, 3} (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [*]) (by decide)
      | exact this {0, 2, 4} (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [*]) (by decide)
      | exact this {0, 3, 4} (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [*]) (by decide)
      | exact this {1, 2, 3} (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [*]) (by decide)
      | exact this {1, 2, 4} (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [*]) (by decide)
      | exact this {1, 3, 4} (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [*]) (by decide)
      | exact this {2, 3, 4} (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [*]) (by decide)
  have hdisj : Disjoint (S ∩ {0, 1, 2, 3, 4}) (S ∩ {5, 6, 7, 8}) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp at hx1 hx2
    omega
  have hunion : (S ∩ {0, 1, 2, 3, 4}) ∪ (S ∩ {5, 6, 7, 8}) ⊆ S :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hcard_union := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj] at hcard_union
  omega

private lemma getD_pair (y : Fin 9 → Bool) (b : Bool) (j : ℕ) :
    (List.ofFn y ++ [b]).getD j Bool.false =
      if h : j < 9 then y ⟨j, h⟩ else if j = 9 then b else Bool.false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h9 : j < 9
  · rw [dif_pos h9, List.getElem?_append_left (by simp [h9])]
    simp [h9]
  · rw [dif_neg h9]
    by_cases heq9 : j = 9
    · subst heq9
      rw [if_pos rfl, List.getElem?_append_right (by simp)]
      simp
    · rw [if_neg heq9, List.getElem?_append_right (by simp; omega)]
      simp [List.getElem?_eq_none (by omega : 1 ≤ j - 9)]

private lemma getD_triple (y : Fin 9 → Bool) (b c : Bool) (j : ℕ) :
    (List.ofFn y ++ [b] ++ [c]).getD j Bool.false =
      if h : j < 9 then y ⟨j, h⟩ else if j = 9 then b else if j = 10 then c else Bool.false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h9 : j < 9
  · rw [dif_pos h9, List.getElem?_append_left (by simp [h9]), List.getElem?_append_left (by simp [h9])]
    simp [h9]
  · rw [dif_neg h9]
    by_cases heq9 : j = 9
    · subst heq9
      rw [if_pos rfl, List.getElem?_append_left (by simp), List.getElem?_append_right (by simp)]
      simp
    · rw [if_neg heq9]
      by_cases heq10 : j = 10
      · subst heq10
        rw [if_pos rfl, List.getElem?_append_right (by simp)]
        simp
      · rw [if_neg heq10, List.getElem?_append_right (by simp; omega)]
        simp [List.getElem?_eq_none (by omega : 1 ≤ j - 10)]

private lemma getD_agree (x1 : List ℕ) (S : Finset (Fin 9))
    (y0 y1 : Fin 9 → Bool) (hy : ∀ v ∈ S, y0 v = y1 v)
    (i : ℕ) (hi : wireDeps x1 i ⊆ S) :
    let x8_0 := List.ofFn y0 ++ [!y0 0]
    let x8_1 := List.ofFn y1 ++ [!y1 0]
    (x8_0 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun j => x8_0.getD j Bool.false) x1)]).getD i Bool.false =
    (x8_1 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun j => x8_1.getD j Bool.false) x1)]).getD i Bool.false := by
  have h8 : ∀ j : ℕ, (if hj : j < 9 then ({⟨j, hj⟩} : Finset (Fin 9)) else if j = 9 then {0} else ∅) ⊆ S →
      (List.ofFn y0 ++ [!y0 0]).getD j Bool.false = (List.ofFn y1 ++ [!y1 0]).getD j Bool.false := by
    intro j hj
    rw [getD_pair, getD_pair]
    by_cases h9 : j < 9
    · simp only [dif_pos h9]
      exact hy ⟨j, h9⟩ (hj (by simp [h9]))
    · simp only [dif_neg h9]
      by_cases heq9 : j = 9
      · subst heq9
        simp only [ite_true]
        rw [hy 0 (hj (by simp))]
      · simp [heq9]
  rw [getD_triple, getD_triple]
  by_cases hi9 : i < 9
  · simp only [dif_pos hi9]
    exact hy ⟨i, hi9⟩ (hi (by simp [wireDeps, hi9]))
  · simp only [dif_neg hi9]
    by_cases heq9 : i = 9
    · subst heq9
      simp only [ite_true]
      rw [hy 0 (hi (by simp [wireDeps]))]
    · simp only [if_neg heq9]
      by_cases heq10 : i = 10
      · subst heq10
        simp only [ite_true]
        congr 1
        apply List.map_congr_left
        intro j hj
        apply h8 j
        intro x hx
        apply hi
        simp only [wireDeps, dif_neg (by omega : ¬ (10 : ℕ) < 9), if_neg (by omega : (10 : ℕ) ≠ 9), ite_true]
        have hfold : ∀ (L : List ℕ), j ∈ L →
            x ∈ L.foldr (fun k acc => (if hk : k < 9 then ({⟨k, hk⟩} : Finset (Fin 9)) else if k = 9 then {0} else ∅) ∪ acc) ∅ := by
          intro L hL
          induction L with
          | nil => simp at hL
          | cons k ks ih =>
            simp only [List.mem_cons] at hL
            simp only [List.foldr_cons, Finset.mem_union]
            rcases hL with rfl | hmem
            · exact Or.inl hx
            · exact Or.inr (ih hmem)
        exact hfold x1 hj
      · simp [heq10]

end PEqualNP.Outside.L_meta_3124

theorem PEqualNP.Outside.L_meta_3124 :
  ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (¬∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) → ∃ (x7 : Fin (9 : ℕ) → Bool), have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))]; x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen x3 hfan hsz hno1
  have hle1 : x3.gates.length ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    exact hno1 ⟨x3.gates[1], getElem?_pos x3.gates 1 hgt⟩
  have hcard1 : ∀ i : ℕ, (PEqualNP.Outside.L_meta_3124.wireDeps x1 i).card ≤ 2 := by
    intro i
    simp only [PEqualNP.Outside.L_meta_3124.wireDeps]
    split_ifs
    · simp
    · simp
    · exact PEqualNP.Outside.L_meta_3124.wireDeps_card_le_two_base x1 hlen
    · simp
  let S : Finset (Fin 9) :=
    if x3.output < 11 then PEqualNP.Outside.L_meta_3124.wireDeps x1 x3.output
    else match x3.gates with
      | [] => ∅
      | g :: _ => g.inputs.foldr (fun i acc => PEqualNP.Outside.L_meta_3124.wireDeps x1 i ∪ acc) ∅
  have hS : S.card ≤ 4 := by
    by_cases hout : x3.output < 11
    · simp only [S, if_pos hout]
      exact le_trans (hcard1 x3.output) (by omega)
    · simp only [S, if_neg hout]
      rcases hgs : x3.gates with _ | ⟨g, gs⟩
      · simp
      · have hg_len : g.inputs.length ≤ 2 := (hfan g (by simp [hgs])).2
        have hfold_card : ∀ (L : List ℕ), (L.foldr (fun i acc => PEqualNP.Outside.L_meta_3124.wireDeps x1 i ∪ acc) ∅).card ≤ 2 * L.length := by
          intro L
          induction L with
          | nil => simp
          | cons k ks ih =>
            simp only [List.foldr_cons, List.length_cons]
            exact le_trans (Finset.card_union_le _ _) (by have := hcard1 k; omega)
        exact le_trans (hfold_card g.inputs) (by omega)
  let y0 : Fin 9 → Bool := fun _ => Bool.false
  let y1 : Fin 9 → Bool := fun v => decide (v ∉ S)
  have hy : ∀ v ∈ S, y0 v = y1 v := by
    intro v hv
    simp [y0, y1, hv]
  have heval_eq :
      let x8_0 := List.ofFn y0 ++ [!y0 0]
      let x8_1 := List.ofFn y1 ++ [!y1 0]
      x3.eval (x8_0 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => x8_0.getD x9 Bool.false) x1)]) =
      x3.eval (x8_1 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => x8_1.getD x9 Bool.false) x1)]) := by
    rcases hgs : x3.gates with _ | ⟨g, gs⟩
    · simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, hgs, List.foldl_nil]
      by_cases hout : x3.output < 11
      · apply PEqualNP.Outside.L_meta_3124.getD_agree x1 S y0 y1 hy x3.output
        simp [S, hout]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    · have hgs_nil : gs = [] := by
        simp only [hgs, List.length_cons] at hle1
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hgs_nil
      by_cases hout11 : x3.output = 11
      · have hout_not_lt : ¬ x3.output < 11 := by omega
        simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, hgs,
          List.foldl_cons, List.foldl_nil]
        have hmap : List.map (fun i => (List.ofFn y0 ++ [!y0 0] ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => (List.ofFn y0 ++ [!y0 0]).getD x9 Bool.false) x1)]).getD i Bool.false) g.inputs =
            List.map (fun i => (List.ofFn y1 ++ [!y1 0] ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => (List.ofFn y1 ++ [!y1 0]).getD x9 Bool.false) x1)]).getD i Bool.false) g.inputs := by
          apply List.map_congr_left
          intro i hi
          apply PEqualNP.Outside.L_meta_3124.getD_agree x1 S y0 y1 hy i
          intro x hx
          simp only [S, if_neg hout_not_lt, hgs]
          have hfold : ∀ (L : List ℕ), i ∈ L → x ∈ L.foldr (fun k acc => PEqualNP.Outside.L_meta_3124.wireDeps x1 k ∪ acc) ∅ := by
            intro L hL
            induction L with
            | nil => simp at hL
            | cons k ks ih =>
              simp only [List.mem_cons] at hL
              simp only [List.foldr_cons, Finset.mem_union]
              rcases hL with rfl | hmem
              · exact Or.inl hx
              · exact Or.inr (ih hmem)
          exact hfold g.inputs hi
        rw [hmap, hout11]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp : (List.ofFn y0 ++ [!y0 0] ++ [_]).length ≤ 11),
          List.getElem?_append_right (by simp : (List.ofFn y1 ++ [!y1 0] ++ [_]).length ≤ 11)]
        simp [List.length_append, List.length_ofFn]
      · by_cases hout_gt : 11 < x3.output
        · simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, hgs,
            List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
        · have hout_lt11 : x3.output < 11 := by omega
          simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, hgs,
            List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by simp [hout_lt11] : x3.output < (List.ofFn y0 ++ [!y0 0] ++ [_]).length),
            List.getElem?_append_left (by simp [hout_lt11] : x3.output < (List.ofFn y1 ++ [!y1 0] ++ [_]).length)]
          have := PEqualNP.Outside.L_meta_3124.getD_agree x1 S y0 y1 hy x3.output (by simp [S, hout_lt11])
          simpa [List.getD_eq_getElem?_getD] using this
  by_cases hy0 :
      (let x8 := List.ofFn y0 ++ [!y0 0]
       x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => x8.getD x9 Bool.false) x1)])) = Bool.false
  · refine ⟨y1, ?_⟩
    dsimp only
    rw [← heval_eq, hy0, PEqualNP.Outside.L_meta_3124.ind_number_petersen_minus_one S hS]
    decide
  · refine ⟨y0, ?_⟩
    dsimp only
    have hy0t : (let x8 := List.ofFn y0 ++ [!y0 0]
       x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => x8.getD x9 Bool.false) x1)])) = Bool.true := by
      cases h : x3.eval (List.ofFn y0 ++ [!y0 0] ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => (List.ofFn y0 ++ [!y0 0]).getD x9 Bool.false) x1)]) <;> simp_all
    rw [hy0t]
    simp [y0]
