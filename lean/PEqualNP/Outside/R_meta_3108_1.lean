import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3108_1

def targetFun (x7 : Fin 9 → Bool) : Bool :=
  x7 0 && x7 1 || x7 1 && x7 2 || x7 2 && x7 3 || x7 3 && x7 4 || x7 4 && x7 0 ||
    x7 0 && x7 5 || x7 1 && x7 6 || x7 2 && x7 7 || x7 3 && x7 8 ||
    x7 5 && x7 7 || x7 6 && x7 8 || x7 8 && x7 5

private def wireDeps (x1 : List ℕ) (i : ℕ) : Finset (Fin 9) :=
  if h : i < 9 then {⟨i, h⟩}
  else if i = 9 then {0, 2}
  else if i = 10 then
    x1.foldr (fun j acc =>
      (if hj : j < 9 then {⟨j, hj⟩} else if j = 9 then {0, 2} else ∅) ∪ acc) ∅
  else ∅

private lemma wireDeps_card_le_four (x1 : List ℕ) (hlen : x1.length ≤ 2) (i : ℕ) :
    (wireDeps x1 i).card ≤ 4 := by
  unfold wireDeps
  split_ifs
  · simp
  · exact le_trans Finset.card_le_two (by omega)
  · rcases x1 with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp
    · simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
      split_ifs <;> simp [Finset.card_le_two]
    · simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
      have ha : (if hj : a < 9 then ({⟨a, hj⟩} : Finset (Fin 9)) else if a = 9 then {0, 2} else ∅).card ≤ 2 := by
        split_ifs <;> simp [Finset.card_le_two]
      have hb : (if hj : b < 9 then ({⟨b, hj⟩} : Finset (Fin 9)) else if b = 9 then {0, 2} else ∅).card ≤ 2 := by
        split_ifs <;> simp [Finset.card_le_two]
      exact le_trans (Finset.card_union_le _ _) (by omega)
    · simp at hlen
  · simp

private lemma ind_number_le_four (S : Finset (Fin 9)) (hS : S.card ≤ 4) :
    targetFun (fun v => decide (v ∉ S)) = Bool.true := by
  by_contra h
  have h58 : (S ∩ {5, 6, 7, 8}).card ≥ 2 := by
    by_cases h5 : (5 : Fin 9) ∈ S
    · by_cases h8 : (8 : Fin 9) ∈ S
      · have : ({5, 8} : Finset (Fin 9)) ⊆ S ∩ {5, 6, 7, 8} := by
          intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [*]
        exact le_trans (by decide : ({5, 8} : Finset (Fin 9)).card ≥ 2) (Finset.card_le_card this)
      · have h6 : (6 : Fin 9) ∈ S := by by_contra h6; apply h; simp [targetFun, h8, h6]
        have : ({5, 6} : Finset (Fin 9)) ⊆ S ∩ {5, 6, 7, 8} := by
          intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [*]
        exact le_trans (by decide : ({5, 6} : Finset (Fin 9)).card ≥ 2) (Finset.card_le_card this)
    · have h7 : (7 : Fin 9) ∈ S := by by_contra h7; apply h; simp [targetFun, h5, h7]
      have h8 : (8 : Fin 9) ∈ S := by by_contra h8; apply h; simp [targetFun, h5, h8]
      have : ({7, 8} : Finset (Fin 9)) ⊆ S ∩ {5, 6, 7, 8} := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [*]
      exact le_trans (by decide : ({7, 8} : Finset (Fin 9)).card ≥ 2) (Finset.card_le_card this)
  have h04 : (S ∩ {0, 1, 2, 3, 4}).card ≥ 3 := by
    by_contra hlt
    by_cases h0 : (0 : Fin 9) ∈ S <;> by_cases h1 : (1 : Fin 9) ∈ S <;> by_cases h2 : (2 : Fin 9) ∈ S <;>
      by_cases h3 : (3 : Fin 9) ∈ S <;> by_cases h4 : (4 : Fin 9) ∈ S
    all_goals
      try (apply h; simp [targetFun, h0, h1, h2, h3, h4]; done)
    all_goals
      have hsub : ∀ (a b c : Fin 9), a ∈ S → b ∈ S → c ∈ S →
          ({a, b, c} : Finset (Fin 9)).card = 3 →
          ({a, b, c} : Finset (Fin 9)) ⊆ {0, 1, 2, 3, 4} → False := by
        intro a b c ha hb hc hcard hs
        have hle : ({a, b, c} : Finset (Fin 9)) ⊆ S ∩ {0, 1, 2, 3, 4} := by
          intro x hx
          refine Finset.mem_inter.mpr ⟨?_, hs hx⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        have := Finset.card_le_card hle
        omega
      first
      | exact hsub 0 1 2 h0 h1 h2 (by decide) (by decide)
      | exact hsub 0 1 3 h0 h1 h3 (by decide) (by decide)
      | exact hsub 0 1 4 h0 h1 h4 (by decide) (by decide)
      | exact hsub 0 2 3 h0 h2 h3 (by decide) (by decide)
      | exact hsub 0 2 4 h0 h2 h4 (by decide) (by decide)
      | exact hsub 0 3 4 h0 h3 h4 (by decide) (by decide)
      | exact hsub 1 2 3 h1 h2 h3 (by decide) (by decide)
      | exact hsub 1 2 4 h1 h2 h4 (by decide) (by decide)
      | exact hsub 1 3 4 h1 h3 h4 (by decide) (by decide)
      | exact hsub 2 3 4 h2 h3 h4 (by decide) (by decide)
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
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega
  · rw [dif_neg h9]
    by_cases heq9 : j = 9
    · subst heq9
      rw [if_pos rfl, List.getElem?_append_right (by simp)]
      simp
    · rw [if_neg heq9, List.getElem?_append_right (by simp; omega)]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl

private lemma getD_triple (y : Fin 9 → Bool) (b c : Bool) (j : ℕ) :
    (List.ofFn y ++ [b] ++ [c]).getD j Bool.false =
      if h : j < 9 then y ⟨j, h⟩ else if j = 9 then b else if j = 10 then c else Bool.false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h9 : j < 9
  · rw [dif_pos h9, List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega
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
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl

private lemma getD_agree (x1 : List ℕ) (S : Finset (Fin 9))
    (y0 y1 : Fin 9 → Bool) (hy : ∀ v ∈ S, y0 v = y1 v)
    (i : ℕ) (hi : wireDeps x1 i ⊆ S) :
    let x8_0 := List.ofFn y0 ++ [y0 0 && y0 2]
    let x8_1 := List.ofFn y1 ++ [y1 0 && y1 2]
    (x8_0 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun j => x8_0.getD j Bool.false) x1)]).getD i Bool.false =
    (x8_1 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun j => x8_1.getD j Bool.false) x1)]).getD i Bool.false := by
  have h8 : ∀ j : ℕ, (if hj : j < 9 then ({⟨j, hj⟩} : Finset (Fin 9)) else if j = 9 then {0, 2} else ∅) ⊆ S →
      (List.ofFn y0 ++ [y0 0 && y0 2]).getD j Bool.false = (List.ofFn y1 ++ [y1 0 && y1 2]).getD j Bool.false := by
    intro j hj
    rw [getD_pair, getD_pair]
    by_cases h9 : j < 9
    · simp only [dif_pos h9]
      exact hy ⟨j, h9⟩ (hj (by simp [h9]))
    · simp only [dif_neg h9]
      by_cases heq9 : j = 9
      · subst heq9
        simp only [ite_true]
        rw [hy 0 (hj (by simp)), hy 2 (hj (by simp))]
      · simp [heq9]
  dsimp only
  rw [getD_triple, getD_triple]
  by_cases hi9 : i < 9
  · simp only [dif_pos hi9]
    exact hy ⟨i, hi9⟩ (hi (by simp [wireDeps, hi9]))
  · simp only [dif_neg hi9]
    by_cases heq9 : i = 9
    · subst heq9
      simp only [ite_true]
      rw [hy 0 (hi (by simp [wireDeps])), hy 2 (hi (by simp [wireDeps]))]
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
            x ∈ L.foldr (fun k acc => (if hk : k < 9 then ({⟨k, hk⟩} : Finset (Fin 9)) else if k = 9 then {0, 2} else ∅) ∪ acc) ∅ := by
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

private lemma wires_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map (fun i => acc[i]?.getD false))]) init).length =
      init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

private lemma wires_getD_lt (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool)
    (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map (fun j => acc.getD j false))]) init).getD i false =
      init.getD i false := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (init ++ [_]) (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem main
    (h_not : ∀ (x1 : List ℕ), x1.length ≤ 2 →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x3 →
      x3.size ≤ 13 →
      List.countP (fun x6 => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun _ => Bool.false) Bool.false x6.op) x3.gates = 1 →
      11 ≤ x3.output →
      x3.output < 11 + x3.gates.length →
      ∀ (g0 : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate),
      x3.gates = g0 :: gs →
      g0.op = PEqualNP.CircuitLowerBounds.GateOp.not →
      ∃ (x7 : Fin 9 → Bool),
        have x8 : List Bool := List.ofFn x7 ++ [x7 0 && x7 2]
        x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => x8.getD x9 Bool.false) x1)]) ≠ targetFun x7)
    (h_mon : ∀ (x1 : List ℕ), x1.length ≤ 2 →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x3 →
      x3.size ≤ 13 →
      List.countP (fun x6 => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun _ => Bool.false) Bool.false x6.op) x3.gates = 1 →
      11 ≤ x3.output →
      x3.output < 11 + x3.gates.length →
      ∀ (g0 : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate),
      x3.gates = g0 :: gs →
      (g0.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g0.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∃ (x7 : Fin 9 → Bool),
        have x8 : List Bool := List.ofFn x7 ++ [x7 0 && x7 2]
        x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => x8.getD x9 Bool.false) x1)]) ≠ targetFun x7) :
    ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x7 : ℕ) => Bool.false) Bool.false x6.op) x3.gates = (1 : ℕ) → ∃ (x7 : Fin (9 : ℕ) → Bool), have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ))]; x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen x3 hfan hsz hcnt
  by_cases hout11 : x3.output < 11
  · let S := wireDeps x1 x3.output
    have hS : S.card ≤ 4 := wireDeps_card_le_four x1 hlen x3.output
    let y0 : Fin 9 → Bool := fun _ => Bool.false
    let y1 : Fin 9 → Bool := fun v => decide (v ∉ S)
    have hy : ∀ v ∈ S, y0 v = y1 v := by intro v hv; simp [y0, y1, hv]
    have heval : x3.eval (List.ofFn y0 ++ [y0 0 && y0 2] ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => (List.ofFn y0 ++ [y0 0 && y0 2]).getD x9 Bool.false) x1)]) =
        x3.eval (List.ofFn y1 ++ [y1 0 && y1 2] ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => (List.ofFn y1 ++ [y1 0 && y1 2]).getD x9 Bool.false) x1)]) := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
      rw [wires_getD_lt x3.gates _ x3.output (by simp [hout11]),
          wires_getD_lt x3.gates _ x3.output (by simp [hout11])]
      exact getD_agree x1 S y0 y1 hy x3.output (fun _ h => h)
    by_cases hy0 : x3.eval (List.ofFn y0 ++ [y0 0 && y0 2] ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => (List.ofFn y0 ++ [y0 0 && y0 2]).getD x9 Bool.false) x1)]) = Bool.false
    · refine ⟨y1, ?_⟩
      dsimp only
      change _ ≠ targetFun y1
      rw [← heval, hy0, ind_number_le_four S hS]
      decide
    · refine ⟨y0, ?_⟩
      dsimp only
      have hfalse : targetFun y0 = Bool.false := by simp [targetFun, y0]
      change _ ≠ targetFun y0
      rw [hfalse]
      exact hy0
  · by_cases hout_hi : 11 + x3.gates.length ≤ x3.output
    · refine ⟨fun _ => Bool.true, ?_⟩
      dsimp only
      change _ ≠ targetFun (fun _ => Bool.true)
      have heval_false : x3.eval (List.ofFn (fun _ : Fin 9 => Bool.true) ++ [Bool.true && Bool.true] ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x9 => (List.ofFn (fun _ : Fin 9 => Bool.true) ++ [Bool.true && Bool.true]).getD x9 Bool.false) x1)]) = Bool.false := by
        simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
          List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none]
        · rfl
        · rw [wires_length]
          simp [hout_hi]
      rw [heval_false]
      decide
    · have hout_ge : 11 ≤ x3.output := by omega
      have hout_lt : x3.output < 11 + x3.gates.length := by omega
      rcases hgs : x3.gates with _ | ⟨g0, gs⟩
      · simp [hgs] at hcnt
      · have hfan0 := (hfan g0 (by simp [hgs])).1
        rcases hfan0 with hg_and | hg_or | hg_not
        · exact h_mon x1 hlen x3 hfan hsz hcnt hout_ge hout_lt g0 gs hgs (Or.inl hg_and)
        · exact h_mon x1 hlen x3 hfan hsz hcnt hout_ge hout_lt g0 gs hgs (Or.inr hg_or)
        · exact h_not x1 hlen x3 hfan hsz hcnt hout_ge hout_lt g0 gs hgs hg_not

end PEqualNP.Outside.R_meta_3108_1
