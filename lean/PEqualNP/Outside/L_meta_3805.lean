import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

namespace PEqualNP.Outside.L_meta_3805

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp (config := {congrConsts := false})
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp (config := {congrConsts := false}) [stepWire]
    omega

private lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp (config := {congrConsts := false}) only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp (config := {congrConsts := false}) at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp (config := {congrConsts := false}) only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp (config := {congrConsts := false}) [stepWire]; omega)]
        simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa (config := {congrConsts := false}) using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp (config := {congrConsts := false}) [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp (config := {congrConsts := false}) only [List.getElem_cons_succ]
      rw [e]
      exact key

private def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

private lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  dsimp only [gateAt]; simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, hj]

private lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

private lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

private lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

private lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

private lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  dsimp only [GateOp.eval]
  simp (config := {congrConsts := false}) only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

private lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  dsimp only [GateOp.eval]
  simp (config := {congrConsts := false}) only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

private lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp (config := {congrConsts := false})) u.isLt]
  simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD]

private lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

private lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp (config := {congrConsts := false}) [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd,
        Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    · simp (config := {congrConsts := false}) [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd,
        Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
  have h5 := hg a _ hcyc
  simp (config := {congrConsts := false}) at h5

private lemma noFourCycle_of_girth5 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) : NoFourCycle G := by
  intro a b hab
  by_contra hlt
  simp (config := {congrConsts := false}) only [not_le] at hlt
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hlt
  rw [Finset.mem_filter] at hc hd
  exact no4 G hg a c b d hc.2.1 hc.2.2.symm hd.2.2 hd.2.1.symm hab hcd

private lemma no4_common {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hno : NoFourCycle G)
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : G.Adj a c) (hbc : G.Adj b c) (had : G.Adj a d) (hbd : G.Adj b d) : False := by
  have hle := hno a b hab
  have h1 : c ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hac, hbc⟩
  have h2 : d ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, had, hbd⟩
  exact hcd (Finset.card_le_one.mp hle c h1 d h2)

private lemma biclique_star {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hno : NoFourCycle G)
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp (config := {congrConsts := false}) only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact no4_common hno hac hbd (hab a ha b hb) (hab c hc b hb) (hab a ha d hd) (hab c hc d hd)

private def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

private lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

private lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

private lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp (config := {congrConsts := false})
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    dsimp only [orStep]; simp (config := {congrConsts := false})
    omega

private lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp (config := {congrConsts := false})
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp (config := {congrConsts := false})
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      dsimp only [orStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp (config := {congrConsts := false}); omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]; exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          dsimp only [orStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp (config := {congrConsts := false}) [hlen, hop]
        rw [e2]
        simp (config := {congrConsts := false}) only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp (config := {congrConsts := false}), Or.inl h3⟩
          · refine ⟨by simp (config := {congrConsts := false}), Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]; exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          dsimp only [orStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp (config := {congrConsts := false}) [hlen, hop]
        rw [e2]
        simp (config := {congrConsts := false}) only [List.mem_singleton]
        constructor
        · intro h3; exact ⟨by simp (config := {congrConsts := false}), Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        dsimp only [orStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp (config := {congrConsts := false}); omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp (config := {congrConsts := false}) at h0
      · rintro ⟨h0, _⟩; simp (config := {congrConsts := false}) at h0; omega

private lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  delta OrReaches orSets gateAt
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

private lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
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

private lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
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

private lemma orReaches_trans {n : ℕ} {C : Circuit} {w h j : ℕ}
    (h1 : OrReaches n C w h) (h2 : OrReaches n C (n + h) j) : OrReaches n C w j := by
  obtain ⟨r1, _⟩ := orReaches_reach h w h1
  obtain ⟨r2, hj⟩ := orReaches_reach j (n + h) h2
  exact reach_orReaches (r1.trans r2) j rfl hj

private lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  dsimp only [orIn] at hu
  simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

private lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ orIn n C p := by
  dsimp only [orIn]
  simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

private lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} {w k : ℕ}
    (h : OrReaches n C w k) : orIn n C (n + k) ⊆ orIn n C w := by
  intro u hu
  exact reach_mem_orIn u ((orReaches_reach k w h).1.trans (mem_orIn_reach u hu))

private lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp (config := {congrConsts := false})
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    dsimp only [coneStep]; simp (config := {congrConsts := false})
    omega

private lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp (config := {congrConsts := false})
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp (config := {congrConsts := false})
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      dsimp only [coneStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp (config := {congrConsts := false}); omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]; exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3; exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        dsimp only [coneStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp (config := {congrConsts := false}) [hlen]
      rw [e2, e1]
      simp (config := {congrConsts := false}) only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp (config := {congrConsts := false}), w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]; exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        dsimp only [coneStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp (config := {congrConsts := false}); omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp (config := {congrConsts := false}) at h0
      · rintro ⟨h0, _⟩; simp (config := {congrConsts := false}) at h0; omega

private lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  delta InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]; exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]; exact h3

private lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

private lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

private lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

private lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  dsimp only [pairInput]; simp (config := {congrConsts := false})

private lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  dsimp only [pairInput]; simp (config := {congrConsts := false})

private lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  dsimp only [pairInput]; simp (config := {congrConsts := false})

private lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  dsimp only [graphFun]
  simp (config := {congrConsts := false}) only [Finset.notMem_empty, false_and, exists_false,
    decide_false, Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

private def tripleInput {n : ℕ} (u v w : Fin n) : Fin n → Bool :=
  fun z => decide (z = u ∨ z = v ∨ z = w)

private lemma tripleInput_one {n : ℕ} (u v w : Fin n) : tripleInput u v w u = true := by
  dsimp only [tripleInput]; simp (config := {congrConsts := false})

private lemma tripleInput_two {n : ℕ} (u v w : Fin n) : tripleInput u v w v = true := by
  dsimp only [tripleInput]; simp (config := {congrConsts := false})

private lemma tripleInput_three {n : ℕ} (u v w : Fin n) : tripleInput u v w w = true := by
  dsimp only [tripleInput]; simp (config := {congrConsts := false})

private lemma tripleInput_true {n : ℕ} (u v w z : Fin n) :
    tripleInput u v w z = true ↔ z = u ∨ z = v ∨ z = w := by
  dsimp only [tripleInput]; simp (config := {congrConsts := false})

private lemma graphFun_triple {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v w : Fin n) :
    graphFun G ∅ (tripleInput u v w) = true → G.Adj u v ∨ G.Adj u w ∨ G.Adj v w := by
  dsimp only [graphFun]
  simp (config := {congrConsts := false}) only [Finset.notMem_empty, false_and, exists_false,
    decide_false, Bool.false_or, decide_eq_true_eq, tripleInput_true]
  rintro ⟨a, b, hab, ha, hb⟩
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (G.irrefl hab).elim
  · exact Or.inl hab
  · exact Or.inr (Or.inl hab)
  · exact Or.inl hab.symm
  · exact (G.irrefl hab).elim
  · exact Or.inr (Or.inr hab)
  · exact Or.inr (Or.inl hab.symm)
  · exact Or.inr (Or.inr hab.symm)
  · exact (G.irrefl hab).elim

private lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp (config := {congrConsts := false})) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

private lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp (config := {congrConsts := false})) hr (by rw [val_ofFn]; exact ht)

private lemma operands {n : ℕ} {C : Circuit} (model : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (w : ℕ) :
    w ∈ (gateAt C j).inputs ↔ ∃ b : Fin 2, opnd C j b = w := by
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (model.2.2 _ (gateAt_mem hj))
  rw [hpq]
  constructor
  · simp (config := {congrConsts := false}) only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl)
    · exact ⟨0, by dsimp only [opnd]; simp (config := {congrConsts := false}) [hpq]⟩
    · exact ⟨1, by dsimp only [opnd]; simp (config := {congrConsts := false}) [hpq]⟩
  · rintro ⟨b, rfl⟩
    fin_cases b <;> (dsimp only [opnd]; simp (config := {congrConsts := false}) [hpq])

private lemma opnd_lt {n : ℕ} {C : Circuit} (model : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (b : Fin 2) : opnd C j b < n + j :=
  model.2.1 j hj (opnd C j b) ((operands model hj _).mpr ⟨b, rfl⟩)

private lemma andValues {n : ℕ} {C : Circuit} (model : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (ha : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C j x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C j b) = true := by
  change val C (List.ofFn x) (n + j) = true ↔ _
  rw [val_and (n := n) (by simp (config := {congrConsts := false})) hj ha]
  constructor
  · intro hall b
    exact (hall _ ((operands model hj _).mpr ⟨b, rfl⟩)).2
  · intro hall w hw
    obtain ⟨b, e⟩ := (operands model hj w).mp hw
    exact ⟨model.2.1 j hj w hw, e ▸ hall b⟩

private lemma junkGate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    {j : ℕ} (hj : j ∈ junk G C) :
    j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
  delta junk gatesWhere at hj
  have hm := Finset.mem_filter.mp hj
  exact ⟨Finset.mem_range.mp hm.1, hm.2.1⟩

private lemma topGate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  dsimp only [tops, gatesWhere] at ha
  simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_range] at ha
  exact ha

private lemma junkUp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (model : IsAO2 n C) {j : ℕ} (hj : j ∈ junk G C) (x : Fin n → Bool)
    (hx : ∀ b : Fin 2, ∃ u ∈ side (n := n) C j b, x u = true) :
    gateVal n C j x = true := by
  obtain ⟨hj', hop⟩ := junkGate G hj
  apply (andValues model hj' hop x).mpr
  intro b
  obtain ⟨u, hu, hux⟩ := hx b
  exact reach_var_val x _ u (mem_orIn_reach u hu) hux

private lemma junkDown {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (model : IsAO2 n C) (top : PEqualNP.TopForm.TopForm G C)
    (anti : ∀ g ∈ junk G C, ∀ h ∈ junk G C, ¬ InCone n C g h)
    {j : ℕ} (hj : j ∈ junk G C) (u v : Fin n)
    (hx : gateVal n C j (pairInput u v) = true) (b : Fin 2) :
    u ∈ side (n := n) C j b ∨ v ∈ side (n := n) C j b := by
  obtain ⟨hj', hop⟩ := junkGate G hj
  let w := opnd C j b
  have hw : w ∈ (gateAt C j).inputs := (operands model hj' _).mpr ⟨b, rfl⟩
  have hv := (andValues model hj' hop _).mp hx b
  rcases operand_trace (C := C) u v w hv with ⟨t, ht, hr⟩ | ⟨h, hh, hhor, hr, _⟩
  · rcases ht with rfl | rfl
    · exact Or.inl (reach_mem_orIn _ hr)
    · exact Or.inr (reach_mem_orIn _ hr)
  have ha := (model.1 _ (gateAt_mem hh)).resolve_right hhor
  have hc : InCone n C h j := operand_cone hj' hw (model.2.1 j hj' w hw) hr
  have hnot : ¬ BelowF G C h := fun hbelow => top h hh j hj' ha hbelow hop hc
  have hd : IsDirtyAnd n G C h := by
    delta IsDirtyAnd IsDirty
    refine ⟨ha, hh, ?_⟩
    by_contra hne
    apply hnot
    intro x hx
    by_contra hfx
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
  have hhj : h ∈ junk G C :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hd⟩
  exact (anti h hhj j hj hc).elim

private lemma topsSafe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (model : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (x : Fin n → Bool)
    (hx : ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true) :
    graphFun G ∅ x = true := by
  obtain ⟨hidx, hop, hbelow⟩ := topGate G ha
  exact hbelow x ((andValues model hidx hop x).mpr hx)

private lemma topContact_wmax {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (model : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (u : Fin n) (hu : u ∈ side C a b) (hj : OrReaches n C (opnd C a (1 - b)) j) :
    u ∈ wmax G C j := by
  dsimp only [wmax]
  simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro x hx hxu
  apply topsSafe G model ha x
  intro i
  have hfin : i = b ∨ i = 1 - b := by fin_cases b <;> fin_cases i <;> decide
  rcases hfin with rfl | rfl
  · exact reach_var_val x _ u (mem_orIn_reach u hu) hxu
  · exact orStep_up (n := n) (by simp (config := {congrConsts := false})) (orReaches_reach j _ hj).1 hx

private lemma wmax_adj_of_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (model : IsAO2 n C) {j : ℕ} (hj : j ∈ junk G C) {u v : Fin n}
    (hu : u ∈ wmax G C j)
    (h0 : u ∈ side C j 0 ∨ v ∈ side C j 0) (h1 : u ∈ side C j 1 ∨ v ∈ side C j 1) :
    G.Adj u v := by
  dsimp only [wmax] at hu
  simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  apply (graphFun_pair G u v).mp
  refine hu (pairInput u v) (junkUp G model hj _ ?_) (pairInput_left u v)
  intro b
  fin_cases b
  · rcases h0 with h | h
    · exact ⟨u, h, pairInput_left u v⟩
    · exact ⟨v, h, pairInput_right u v⟩
  · rcases h1 with h | h
    · exact ⟨u, h, pairInput_left u v⟩
    · exact ⟨v, h, pairInput_right u v⟩

private lemma wmax_not_both_sides {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (model : IsAO2 n C) {j : ℕ} (hj : j ∈ junk G C) {u : Fin n}
    (hu : u ∈ wmax G C j) (h0 : u ∈ side C j 0) (h1 : u ∈ side C j 1) : False :=
  G.irrefl (wmax_adj_of_pair G model hj hu (Or.inl h0) (Or.inl h1))

private lemma three_vertex_witness_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (model : IsAO2 n C) (hno : NoFourCycle G)
    {j : ℕ} (hj : j ∈ junk G C) {u : Fin n} (hu : u ∈ wmax G C j) :
    ∃ c : Fin 2, ((side C j c).filter (fun w => ¬ G.Adj u w)).card ≤ 1 := by
  let A := (side C j 0).filter (fun w => ¬ G.Adj u w)
  let B := (side C j 1).filter (fun w => ¬ G.Adj u w)
  have hbic : A.card ≤ 1 ∨ B.card ≤ 1 := by
    refine biclique_star hno A B ?_
    intro w1 hw1 w2 hw2
    rw [Finset.mem_filter] at hw1 hw2
    have hgw : graphFun G ∅ (tripleInput u w1 w2) = true := by
      dsimp only [wmax] at hu
      simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      refine hu (tripleInput u w1 w2) (junkUp G model hj _ ?_) (tripleInput_one u w1 w2)
      intro b
      fin_cases b
      · exact ⟨w1, hw1.1, tripleInput_two u w1 w2⟩
      · exact ⟨w2, hw2.1, tripleInput_three u w1 w2⟩
    rcases graphFun_triple G u w1 w2 hgw with h | h | h
    · exact (hw1.2 h).elim
    · exact (hw2.2 h).elim
    · exact h
  rcases hbic with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

private lemma three_vertex_witness_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (model : IsAO2 n C) (hno : NoFourCycle G)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) {j : ℕ} (hj : j ∈ junk G C)
    (hor : OrReaches n C (opnd C a (1 - b)) j) (c : Fin 2)
    {v : Fin n} (hv : v ∈ side C j (1 - c)) :
    ((side C a b).filter (fun w => ¬ G.Adj v w)).card ≤ 1 ∨
    ((side C j c).filter (fun w => ¬ G.Adj v w)).card ≤ 1 := by
  let A := (side C a b).filter (fun w => ¬ G.Adj v w)
  let B := (side C j c).filter (fun w => ¬ G.Adj v w)
  refine biclique_star hno A B ?_
  intro w1 hw1 w2 hw2
  rw [Finset.mem_filter] at hw1 hw2
  have hgw : graphFun G ∅ (tripleInput v w1 w2) = true := by
    apply topsSafe G model ha (tripleInput v w1 w2)
    intro i
    have hfin : i = b ∨ i = 1 - b := by fin_cases b <;> fin_cases i <;> decide
    rcases hfin with rfl | rfl
    · exact reach_var_val _ _ w1 (mem_orIn_reach w1 hw1.1) (tripleInput_two v w1 w2)
    · have hjv : gateVal n C j (tripleInput v w1 w2) = true := by
        apply junkUp G model hj
        intro d
        have hfin2 : d = c ∨ d = 1 - c := by fin_cases c <;> fin_cases d <;> decide
        rcases hfin2 with rfl | rfl
        · exact ⟨w2, hw2.1, tripleInput_three v w1 w2⟩
        · exact ⟨v, hv, tripleInput_one v w1 w2⟩
      exact orStep_up (n := n) (by simp (config := {congrConsts := false}))
        (orReaches_reach j _ hor).1 hjv
  rcases graphFun_triple G v w1 w2 hgw with h | h | h
  · exact (hw1.2 h).elim
  · exact (hw2.2 h).elim
  · exact h

private lemma exists_outlier_of_filter_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (u : Fin n)
    (hle : (S.filter (fun w => ¬ G.Adj u w)).card ≤ 1) :
    ∃ z : Fin n, ∀ w ∈ S, w ≠ z → G.Adj u w := by
  by_cases hem : (S.filter (fun w => ¬ G.Adj u w)).Nonempty
  · obtain ⟨z, hz⟩ := hem
    refine ⟨z, fun w hw hne => ?_⟩
    by_contra hna
    have hw' : w ∈ S.filter (fun w => ¬ G.Adj u w) := Finset.mem_filter.mpr ⟨hw, hna⟩
    exact hne (Finset.card_le_one.mp hle w hw' z hz)
  · refine ⟨u, fun w hw _ => ?_⟩
    by_contra hna
    exact hem ⟨w, Finset.mem_filter.mpr ⟨hw, hna⟩⟩

private lemma orIn_or_gate {n : ℕ} {C : Circuit} (model : IsAO2 n C) {k : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) :
    orIn n C (n + k) = orIn n C (opnd C k 0) ∪ orIn n C (opnd C k 1) := by
  ext i
  rw [Finset.mem_union]
  constructor
  · intro hi
    have hr := mem_orIn_reach i hi
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hstep, hrest⟩
    · exfalso; have := i.isLt; omega
    · obtain ⟨k', hk', heq, _, hin, _⟩ := hstep
      have hkk : k' = k := by omega
      subst hkk
      obtain ⟨d, hd⟩ := (operands model hk c).mp hin
      rw [← hd] at hrest
      fin_cases d
      · exact Or.inl (reach_mem_orIn i hrest)
      · exact Or.inr (reach_mem_orIn i hrest)
  · rintro (hi | hi)
    · have hr := mem_orIn_reach i hi
      exact reach_mem_orIn i (Relation.ReflTransGen.head
        ⟨k, hk, rfl, hop, (operands model hk _).mpr ⟨0, rfl⟩, opnd_lt model hk 0⟩ hr)
    · have hr := mem_orIn_reach i hi
      exact reach_mem_orIn i (Relation.ReflTransGen.head
        ⟨k, hk, rfl, hop, (operands model hk _).mpr ⟨1, rfl⟩, opnd_lt model hk 1⟩ hr)

private lemma orIn_card_ge_two_is_or {n : ℕ} {C : Circuit} {w : ℕ}
    (hcard : 2 ≤ (orIn n C w).card) :
    ∃ k < C.gates.length, w = n + k ∧ (gateAt C k).op = GateOp.or := by
  by_cases hw : w < n
  · exfalso
    have hsub : orIn n C w ⊆ {⟨w, hw⟩} := by
      intro i hi
      rw [Finset.mem_singleton]
      have hr := mem_orIn_reach i hi
      rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, hstep, _⟩
      · exact Fin.ext heq.symm
      · obtain ⟨k, _, rfl, _, _, _⟩ := hstep; omega
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h1
    omega
  · obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (orIn n C w).card)
    have hr := mem_orIn_reach v hv
    rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, hstep, _⟩
    · exfalso; have := v.isLt; omega
    · obtain ⟨k, hk, rfl, hop, _, _⟩ := hstep
      exact ⟨k, hk, rfl, hop⟩

private lemma branching_or_step {n : ℕ} {C : Circuit} (model : IsAO2 n C) :
    ∀ (w : ℕ) (v : Fin n), v ∈ orIn n C w → 2 ≤ (orIn n C w).card →
      ∃ k < C.gates.length, ∃ d : Fin 2,
        OrReaches n C w k ∧ 2 ≤ (orIn n C (n + k)).card ∧ orIn n C (opnd C k d) = {v} := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv hcard
    obtain ⟨k, hk, rfl, hop⟩ := orIn_card_ge_two_is_or hcard
    have hv' := hv
    rw [orIn_or_gate model hk hop, Finset.mem_union] at hv'
    obtain ⟨d, hvd⟩ : ∃ d : Fin 2, v ∈ orIn n C (opnd C k d) := by
      rcases hv' with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    by_cases hsub : 2 ≤ (orIn n C (opnd C k d)).card
    · obtain ⟨k', hk', d', hr', hc', heq'⟩ := ih (opnd C k d) (opnd_lt model hk d) v hvd hsub
      have hreach : OrReaches n C (n + k) k' :=
        (orReaches_iff n C k k').mpr ⟨hk, Or.inr ⟨hop, opnd C k d,
          (operands model hk _).mpr ⟨d, rfl⟩, opnd_lt model hk d, hr'⟩⟩
      exact ⟨k', hk', d', hreach, hc', heq'⟩
    · have hsing : orIn n C (opnd C k d) = {v} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        exact ⟨hvd, fun y hy => Finset.card_le_one.mp (by omega) y hy v hvd⟩
      exact ⟨k, hk, d, (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hcard, hsing⟩

open Classical in
private lemma branching_or_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (model : IsAO2 n C) (hno : NoFourCycle G) (E : Finset (Sym2 (Fin n))) :
    (E.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ w : ℕ,
      v ∈ orIn n C w ∧ 2 ≤ (orIn n C w).card ∧ ∀ y ∈ orIn n C w, G.Adj u y).card ≤
      2 * C.size := by
  classical
  let E0 := E.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ w : ℕ,
    v ∈ orIn n C w ∧ 2 ≤ (orIn n C w).card ∧ ∀ y ∈ orIn n C w, G.Adj u y
  have key : ∀ e ∈ E0,
      ∃ p : ℕ × Fin 2, p ∈ Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2)) ∧
        ∃ a b : Fin n, e = s(a, b) ∧ 2 ≤ (orIn n C (n + p.1)).card ∧
          (∀ x12 ∈ orIn n C (n + p.1), G.Adj a x12) ∧
          orIn n C (opnd C p.1 p.2) = {b} := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨_, u, v, hab, w, hv, hcard, hadj⟩ := he
    obtain ⟨k, hk, d, hor, hkc, hsing⟩ := branching_or_step model w v hv hcard
    refine ⟨(k, d), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk, Finset.mem_univ _⟩,
      u, v, hab, hkc, ?_, hsing⟩
    intro y hy
    exact hadj y (orIn_subset_of_orReaches hor hy)
  choose f hf using key
  have hle := Finset.card_le_card_of_injOn (s := E0.attach)
    (t := Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2)))
    (fun e => f e.1 e.2) (fun e _ => (hf e.1 e.2).1) (by
      intro e1 _ e2 _ heq
      obtain ⟨a, b, hab, hc, hadj, hb⟩ := (hf e1.1 e1.2).2
      obtain ⟨a', b', hab', hc', hadj', hb'⟩ := (hf e2.1 e2.2).2
      have heq' : f e1.1 e1.2 = f e2.1 e2.2 := heq
      rw [heq'] at hc hadj hb
      have hbb : b = b' := Finset.singleton_injective (hb.symm.trans hb')
      obtain ⟨c, hcm, d, hdm, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 < (orIn n C (n + (f e2.1 e2.2).1)).card)
      have hcard := hno c d hcd
      have haa : a = a' := by
        refine Finset.card_le_one.mp hcard a ?_ a' ?_
        · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, (hadj c hcm).symm, (hadj d hdm).symm⟩
        · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, (hadj' c hcm).symm, (hadj' d hdm).symm⟩
      apply Subtype.ext
      rw [hab, hab', haa, hbb])
  rw [Finset.card_attach, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin] at hle
  dsimp only [E0, Circuit.size] at hle ⊢
  omega

private lemma one_outlier_or_dag_step {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (model : IsAO2 n C) :
    ∀ (w : ℕ) (u v z : Fin n),
      v ∈ orIn n C w → v ≠ z → 2 ≤ ((orIn n C w).erase z).card →
      (∀ y ∈ orIn n C w, y ≠ z → G.Adj u y) →
      ∃ k < C.gates.length, ∃ d : Fin 2,
        v ∈ orIn n C (opnd C k d) ∧ (orIn n C (opnd C k d)).erase z = {v} ∧
        v ∈ orIn n C (n + k) ∧
        2 ≤ ((orIn n C (n + k)).erase z).card ∧
        ∀ y ∈ orIn n C (n + k), y ≠ z → G.Adj u y := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro u v z hv hne hcard hadj
    have hcard2 : 2 ≤ (orIn n C w).card := hcard.trans (Finset.card_erase_le (a := z) (s := orIn n C w))
    obtain ⟨k, hk, rfl, hop⟩ := orIn_card_ge_two_is_or hcard2
    have hv' := hv
    rw [orIn_or_gate model hk hop, Finset.mem_union] at hv'
    obtain ⟨d, hvd⟩ : ∃ d : Fin 2, v ∈ orIn n C (opnd C k d) := by
      rcases hv' with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hsub : orIn n C (opnd C k d) ⊆ orIn n C (n + k) := by
      rw [orIn_or_gate model hk hop]
      fin_cases d
      · exact Finset.subset_union_left
      · exact Finset.subset_union_right
    by_cases h2 : 2 ≤ ((orIn n C (opnd C k d)).erase z).card
    · exact ih (opnd C k d) (opnd_lt model hk d) u v z hvd hne h2
        (fun y hy hyn => hadj y (hsub hy) hyn)
    · have hsing : (orIn n C (opnd C k d)).erase z = {v} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        have hvmem : v ∈ (orIn n C (opnd C k d)).erase z := Finset.mem_erase.mpr ⟨hne, hvd⟩
        exact ⟨hvmem, fun y hy => Finset.card_le_one.mp (by omega) y hy v hvmem⟩
      exact ⟨k, hk, d, hvd, hsing, hv, hcard, hadj⟩

private lemma one_outlier_fiber_le_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hno : NoFourCycle G) (k : ℕ) (d : Fin 2)
    (F : Finset (Sym2 (Fin n)))
    (hF : ∀ e ∈ F, ∃ u v z : Fin n, e = s(u, v) ∧
      v ∈ orIn n C (opnd C k d) ∧ (orIn n C (opnd C k d)).erase z = {v} ∧
      v ∈ orIn n C (n + k) ∧
      2 ≤ ((orIn n C (n + k)).erase z).card ∧ ∀ y ∈ orIn n C (n + k), y ≠ z → G.Adj u y) :
    F.card ≤ 2 := by
  by_contra hlt
  simp (config := {congrConsts := false}) only [not_le] at hlt
  obtain ⟨e1, he1, F', hF'⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
  have hpos : 1 < (F.erase e1).card := by
    have := Finset.card_erase_add_one he1
    omega
  obtain ⟨e2, he2', e3, he3', he23⟩ := Finset.one_lt_card.mp hpos
  have he2 : e2 ∈ F := (Finset.mem_erase.mp he2').2
  have he12 : e1 ≠ e2 := (Finset.mem_erase.mp he2').1.symm
  have he3 : e3 ∈ F := (Finset.mem_erase.mp he3').2
  have he13 : e1 ≠ e3 := (Finset.mem_erase.mp he3').1.symm
  obtain ⟨u1, v1, z1, rfl, hv1, hs1, hv1B, hc1, ha1⟩ := hF e1 he1
  obtain ⟨u2, v2, z2, rfl, hv2, hs2, hv2B, hc2, ha2⟩ := hF e2 he2
  obtain ⟨u3, v3, z3, rfl, hv3, hs3, hv3B, hc3, ha3⟩ := hF e3 he3
  let A := orIn n C (opnd C k d)
  let B := orIn n C (n + k)
  have hvne1 : v1 ≠ z1 := by
    have hmem : v1 ∈ A.erase z1 := by rw [hs1]; exact Finset.mem_singleton_self v1
    exact (Finset.mem_erase.mp hmem).1
  have hvne2 : v2 ≠ z2 := by
    have hmem : v2 ∈ A.erase z2 := by rw [hs2]; exact Finset.mem_singleton_self v2
    exact (Finset.mem_erase.mp hmem).1
  have hvne3 : v3 ≠ z3 := by
    have hmem : v3 ∈ A.erase z3 := by rw [hs3]; exact Finset.mem_singleton_self v3
    exact (Finset.mem_erase.mp hmem).1
  have hA_card : A.card ≤ 2 := by
    have hs1' : (A.erase z1).card = 1 := by rw [hs1, Finset.card_singleton]
    by_cases hz1 : z1 ∈ A
    · have := Finset.card_erase_add_one hz1; omega
    · rw [Finset.erase_eq_of_notMem hz1] at hs1'; omega
  have hsame : ∀ (ua ub va za zb : Fin n),
      A.erase za = {va} → A.erase zb = {va} →
      va ∈ B → A.card = 2 → 2 ≤ (B.erase za).card →
      (∀ y ∈ B, y ≠ za → G.Adj ua y) →
      (∀ y ∈ B, y ≠ zb → G.Adj ub y) →
      s(ua, va) ≠ s(ub, va) → False := by
    intro ua ub va za zb hsa hsb hvaB hA2 hB2 hua hub hne
    have hu_ne : ua ≠ ub := fun h => hne (by rw [h])
    have hza : za ∈ A := by
      by_contra hnz
      rw [Finset.erase_eq_of_notMem hnz] at hsa
      have := congrArg Finset.card hsa
      rw [Finset.card_singleton] at this
      omega
    have hzb : zb ∈ A := by
      by_contra hnz
      rw [Finset.erase_eq_of_notMem hnz] at hsb
      have := congrArg Finset.card hsb
      rw [Finset.card_singleton] at this
      omega
    have hz_eq : za = zb := by
      by_contra hzn
      have hz1 : za ∈ A.erase zb := Finset.mem_erase.mpr ⟨hzn, hza⟩
      rw [hsb, Finset.mem_singleton] at hz1
      have hmem : va ∈ A.erase za := by rw [hsa]; exact Finset.mem_singleton_self va
      exact (Finset.mem_erase.mp hmem).1 hz1.symm
    subst hz_eq
    have hvne : va ≠ za := by
      have hmem : va ∈ A.erase za := by rw [hsa]; exact Finset.mem_singleton_self va
      exact (Finset.mem_erase.mp hmem).1
    have hva_er : va ∈ B.erase za := Finset.mem_erase.mpr ⟨hvne, hvaB⟩
    have hpos_er : 0 < ((B.erase za).erase va).card := by
      have := Finset.card_erase_add_one hva_er; omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos_er
    have hy_ne_v : y ≠ va := (Finset.mem_erase.mp hy).1
    have hy_er : y ∈ B.erase za := (Finset.mem_erase.mp hy).2
    have hy_ne_z : y ≠ za := (Finset.mem_erase.mp hy_er).1
    have hy_B : y ∈ B := (Finset.mem_erase.mp hy_er).2
    exact no4_common hno hu_ne hy_ne_v.symm
      (hua va hvaB hvne) (hub va hvaB hvne) (hua y hy_B hy_ne_z) (hub y hy_B hy_ne_z)
  by_cases hA1 : A.card ≤ 1
  · have hv12 : v1 = v2 := Finset.card_le_one.mp hA1 v1 hv1 v2 hv2
    have hv13 : v1 = v3 := Finset.card_le_one.mp hA1 v1 hv1 v3 hv3
    subst hv12; subst hv13
    have hu12 : u1 ≠ u2 := fun h => he12 (by rw [h])
    have hu13 : u1 ≠ u3 := fun h => he13 (by rw [h])
    have hu23 : u2 ≠ u3 := fun h => he23 (by rw [h])
    have hv1_er : v1 ∈ B.erase z1 := Finset.mem_erase.mpr ⟨hvne1, hv1B⟩
    have hc1B : 2 ≤ (B.erase z1).card := hc1
    have hpos1 : 0 < ((B.erase z1).erase v1).card := by
      have := Finset.card_erase_add_one hv1_er; omega
    obtain ⟨y1, hy1⟩ := Finset.card_pos.mp hpos1
    have hy1_nv : y1 ≠ v1 := (Finset.mem_erase.mp hy1).1
    have hy1_er : y1 ∈ B.erase z1 := (Finset.mem_erase.mp hy1).2
    have hy1_nz1 : y1 ≠ z1 := (Finset.mem_erase.mp hy1_er).1
    have hy1_B : y1 ∈ B := (Finset.mem_erase.mp hy1_er).2
    have hadj_u1_v : G.Adj u1 v1 := ha1 v1 hv1B hvne1
    have hadj_u1_y1 : G.Adj u1 y1 := ha1 y1 hy1_B hy1_nz1
    have hy1_z2 : y1 = z2 := by
      by_contra hnz
      exact no4_common hno hu12 hy1_nv.symm
        hadj_u1_v (ha2 v1 hv2B hvne2) hadj_u1_y1 (ha2 y1 hy1_B hnz)
    have hy1_z3 : y1 = z3 := by
      by_contra hnz
      exact no4_common hno hu13 hy1_nv.symm
        hadj_u1_v (ha3 v1 hv3B hvne3) hadj_u1_y1 (ha3 y1 hy1_B hnz)
    have hz23 : z2 = z3 := hy1_z2.symm.trans hy1_z3
    have hv2_er : v1 ∈ B.erase z2 := Finset.mem_erase.mpr ⟨hvne2, hv2B⟩
    have hc2B : 2 ≤ (B.erase z2).card := hc2
    have hpos2 : 0 < ((B.erase z2).erase v1).card := by
      have := Finset.card_erase_add_one hv2_er; omega
    obtain ⟨y2, hy2⟩ := Finset.card_pos.mp hpos2
    have hy2_nv : y2 ≠ v1 := (Finset.mem_erase.mp hy2).1
    have hy2_er : y2 ∈ B.erase z2 := (Finset.mem_erase.mp hy2).2
    have hy2_nz2 : y2 ≠ z2 := (Finset.mem_erase.mp hy2_er).1
    have hy2_B : y2 ∈ B := (Finset.mem_erase.mp hy2_er).2
    have hy2_nz3 : y2 ≠ z3 := hz23 ▸ hy2_nz2
    exact no4_common hno hu23 hy2_nv.symm
      (ha2 v1 hv2B hvne2) (ha3 v1 hv3B hvne3) (ha2 y2 hy2_B hy2_nz2) (ha3 y2 hy2_B hy2_nz3)
  · have hA2 : A.card = 2 := by omega
    by_cases hv12 : v1 = v2
    · rw [← hv12] at hs2
      exact hsame u1 u2 v1 z1 z2 hs1 hs2 hv1B hA2 hc1 ha1 ha2 (fun h => he12 (by rw [← hv12]; exact h))
    · by_cases hv13 : v1 = v3
      · rw [← hv13] at hs3
        exact hsame u1 u3 v1 z1 z3 hs1 hs3 hv1B hA2 hc1 ha1 ha3 (fun h => he13 (by rw [← hv13]; exact h))
      · have hv23 : v2 = v3 := by
          by_contra hv23
          have hsub : {v1, v2, v3} ⊆ A := by
            intro x hx
            simp (config := {congrConsts := false}) only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> assumption
          have hc3' := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem (by simp [hv12, hv13]),
            Finset.card_insert_of_notMem (by simp [hv23]), Finset.card_singleton] at hc3'
          omega
        rw [← hv23] at hs3
        exact hsame u2 u3 v2 z2 z3 hs2 hs3 hv2B hA2 hc2 ha2 ha3 (fun h => he23 (by rw [← hv23]; exact h))

open Classical in
private lemma one_outlier_or_dag_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (model : IsAO2 n C) (hno : NoFourCycle G) (E : Finset (Sym2 (Fin n))) :
    (E.filter fun e => ∃ u v z : Fin n, ∃ w : ℕ, e = s(u, v) ∧
      v ∈ orIn n C w ∧ v ≠ z ∧ 2 ≤ ((orIn n C w).erase z).card ∧
      ∀ y ∈ orIn n C w, y ≠ z → G.Adj u y).card ≤ 4 * C.size := by
  classical
  let E0 := E.filter fun e => ∃ u v z : Fin n, ∃ w : ℕ, e = s(u, v) ∧
    v ∈ orIn n C w ∧ v ≠ z ∧ 2 ≤ ((orIn n C w).erase z).card ∧
    ∀ y ∈ orIn n C w, y ≠ z → G.Adj u y
  let F : ℕ × Fin 2 → Finset (Sym2 (Fin n)) := fun p =>
    E0.filter fun e => ∃ u v z : Fin n, e = s(u, v) ∧
      v ∈ orIn n C (opnd C p.1 p.2) ∧ (orIn n C (opnd C p.1 p.2)).erase z = {v} ∧
      v ∈ orIn n C (n + p.1) ∧
      2 ≤ ((orIn n C (n + p.1)).erase z).card ∧ ∀ y ∈ orIn n C (n + p.1), y ≠ z → G.Adj u y
  have hsub : E0 ⊆ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))).biUnion F := by
    intro e he
    have he' := he
    rw [Finset.mem_filter] at he'
    obtain ⟨_, u, v, z, w, rfl, hv, hne, hc, hadj⟩ := he'
    obtain ⟨k, hk, d, hvd, hsing, hvB, hcB, haB⟩ := one_outlier_or_dag_step G model w u v z hv hne hc hadj
    refine Finset.mem_biUnion.mpr ⟨(k, d),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk, Finset.mem_univ _⟩,
      Finset.mem_filter.mpr ⟨he, u, v, z, rfl, hvd, hsing, hvB, hcB, haB⟩⟩
  have hfib : ∀ p ∈ Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2)), (F p).card ≤ 2 := by
    intro p _
    refine one_outlier_fiber_le_two G (C := C) hno p.1 p.2 (F p) ?_
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hbi := (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le_card_mul (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))) F 2 hfib)
  rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin] at hbi
  dsimp only [E0, Circuit.size] at hbi ⊢
  omega

open Classical in
private lemma case1_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (model : IsAO2 n C) (hno : NoFourCycle G) :
    ((Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
      ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
      v ∈ side C j 0 ∧ v ∈ side C j 1).card ≤ 12 * C.size := by
  classical
  let S_J : ℕ → Finset (Fin n) := fun j => side C j 0 ∩ side C j 1
  let T_J : ℕ → Finset (Fin n) := fun j =>
    Finset.univ.filter fun u => ∃ a ∈ tops G C, ∃ b : Fin 2,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j
  have hbic : ∀ j ∈ junk G C, (S_J j).card ≤ 1 ∨ (T_J j).card ≤ 1 := by
    intro j hj
    have hst : (T_J j).card ≤ 1 ∨ (S_J j).card ≤ 1 := by
      refine biclique_star hno (T_J j) (S_J j) ?_
      intro u hu v hv
      rw [Finset.mem_filter] at hu
      obtain ⟨_, a, ha, b, hus, hor⟩ := hu
      rw [Finset.mem_inter] at hv
      exact wmax_adj_of_pair G model hj (topContact_wmax G model ha b u hus hor) (Or.inr hv.1) (Or.inr hv.2)
    exact hst.symm
  let E1a := (Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    v ∈ S_J j ∧ (S_J j).card ≤ 1
  let E1b := (Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    v ∈ S_J j ∧ (T_J j).card ≤ 1
  have hsplit : ((Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
      ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
      v ∈ side C j 0 ∧ v ∈ side C j 1) ⊆ E1a ∪ E1b := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heU, u, v, rfl, a, ha, b, j, hj, hus, hor, hv0, hv1⟩ := he
    have hvS : v ∈ S_J j := Finset.mem_inter.mpr ⟨hv0, hv1⟩
    rw [Finset.mem_union]
    rcases hbic j hj with hS | hT
    · exact Or.inl (Finset.mem_filter.mpr ⟨heU, u, v, rfl, a, ha, b, j, hj, hus, hor, hvS, hS⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨heU, u, v, rfl, a, ha, b, j, hj, hus, hor, hvS, hT⟩)
  -- Bound E1a ≤ 6 * C.size
  let E1a_br := E1a.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    v ∈ S_J j ∧ (S_J j).card ≤ 1 ∧ 2 ≤ (side (n := n) C a b).card
  let E1a_sg := E1a.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    v ∈ S_J j ∧ (S_J j).card ≤ 1 ∧ (side (n := n) C a b).card ≤ 1
  have h1a_br : E1a_br.card ≤ 2 * C.size := by
    have hsub : E1a_br ⊆ E1a.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ w : ℕ,
        v ∈ orIn n C w ∧ 2 ≤ (orIn n C w).card ∧ ∀ y ∈ orIn n C w, G.Adj u y := by
      intro e he
      rw [Finset.mem_filter] at he ⊢
      refine ⟨he.1, ?_⟩
      obtain ⟨u, v, rfl, a, ha, b, j, hj, hus, hor, hvS, hSc, h2⟩ := he.2
      refine ⟨v, u, Sym2.eq_swap, opnd C a b, hus, h2, fun y hy => ?_⟩
      have hyT : y ∈ T_J j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, b, hy, hor⟩
      have hvw := wmax_adj_of_pair G model hj (topContact_wmax G model ha b y hy hor)
        (Or.inr (Finset.mem_inter.mp hvS).1) (Or.inr (Finset.mem_inter.mp hvS).2)
      exact hvw.symm
    have hb := branching_or_bound G model hno E1a
    exact (Finset.card_le_card hsub).trans (by convert hb)
  let U_A : ℕ → Finset (Fin n) := fun h =>
    Finset.univ.filter fun u => ∃ a ∈ tops G C, ∃ b : Fin 2,
      side C a b = {u} ∧ OrReaches n C (opnd C a (1 - b)) h
  let V_J : ℕ → Finset (Fin n) := fun h =>
    Finset.univ.filter fun v => ∃ j ∈ junk G C,
      S_J j = {v} ∧ OrReaches n C (n + h) j
  have hUV : ∀ h, (U_A h).card ≤ 1 ∨ (V_J h).card ≤ 1 := by
    intro h
    refine biclique_star hno (U_A h) (V_J h) ?_
    intro u hu v hv
    rw [Finset.mem_filter] at hu hv
    obtain ⟨_, a, ha, b, hsa, hora⟩ := hu
    obtain ⟨_, j, hj, hsj, horj⟩ := hv
    have hor : OrReaches n C (opnd C a (1 - b)) j := orReaches_trans hora horj
    have hu_side : u ∈ side C a b := by rw [hsa]; exact Finset.mem_singleton_self u
    have hv_S : v ∈ S_J j := by rw [hsj]; exact Finset.mem_singleton_self v
    rw [Finset.mem_inter] at hv_S
    exact wmax_adj_of_pair G model hj (topContact_wmax G model ha b u hu_side hor)
      (Or.inr hv_S.1) (Or.inr hv_S.2)
  let E1a_sg1 := ((tops G C ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun p => (side (n := n) C p.1 p.2).card ≤ 1 ∧ (V_J (opnd C p.1 (1 - p.2) - n)).card ≤ 1).biUnion
    fun p => (side (n := n) C p.1 p.2 ×ˢ V_J (opnd C p.1 (1 - p.2) - n)).image fun q => s(q.1, q.2)
  let E1a_sg2 := ((Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun p => (U_A p.1).card ≤ 1 ∧ (V_J (opnd C p.1 p.2 - n)).card ≤ 1).biUnion
    fun p => (U_A p.1 ×ˢ V_J (opnd C p.1 p.2 - n)).image fun q => s(q.1, q.2)
  have h1a_sg_sub : E1a_sg ⊆ E1a_sg1 ∪ E1a_sg2 := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨_, u, v, rfl, a, ha, b, j, hj, hus, hor, hvS, hSc, h1⟩ := he
    have hsa : side C a b = {u} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨hus, fun y hy => Finset.card_le_one.mp h1 y hy u hus⟩
    have hsj : S_J j = {v} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨hvS, fun y hy => Finset.card_le_one.mp hSc y hy v hvS⟩
    have hnw : n ≤ opnd C a (1 - b) := hor.1
    have hlt_a : opnd C a (1 - b) < n + a := opnd_lt model (topGate G ha).1 (1 - b)
    let h0 := opnd C a (1 - b) - n
    have hh0_eq : n + h0 = opnd C a (1 - b) := by omega
    have hor0 : OrReaches n C (n + h0) j := hh0_eq ▸ hor
    have hv0 : v ∈ V_J h0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, hsj, hor0⟩
    rw [Finset.mem_union]
    by_cases hV0 : (V_J h0).card ≤ 1
    · left
      refine Finset.mem_biUnion.mpr ⟨(a, b), ?_, Finset.mem_image.mpr ⟨(u, v),
        Finset.mem_product.mpr ⟨hus, hv0⟩, rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩, h1, hV0⟩
    · right
      let K := (Finset.range C.gates.length).filter fun k =>
        OrReaches n C (n + h0) k ∧ OrReaches n C (n + k) j ∧ 2 ≤ (V_J k).card
      have hh0_len : h0 < C.gates.length := by
        have := (topGate G ha).1; omega
      have hK_ne : K.Nonempty := ⟨h0, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hh0_len, (orReaches_iff n C h0 h0).mpr ⟨hh0_len, Or.inl rfl⟩,
          hor0, by omega⟩⟩
      let h' := K.min' hK_ne
      have hh'_mem := K.min'_mem hK_ne
      rw [Finset.mem_filter, Finset.mem_range] at hh'_mem
      obtain ⟨hh'_len, hor_h0_h', hor_h'_j, hV_h'⟩ := hh'_mem
      have hV_j : (V_J j).card ≤ 1 := by
        have hsub_j : V_J j ⊆ {v} := by
          intro v' hv'
          rw [Finset.mem_filter] at hv'
          obtain ⟨_, j', hj', hsj', horj'⟩ := hv'
          obtain ⟨_, hcases⟩ := (orReaches_iff n C j j').mp horj'
          rcases hcases with rfl | ⟨hopj, _⟩
          · rw [Finset.mem_singleton]
            exact Finset.singleton_injective (hsj'.symm.trans hsj)
          · exfalso; have := (junkGate G hj).2; rw [hopj] at this; cases this
        exact (Finset.card_le_card hsub_j).trans (by rw [Finset.card_singleton])
      have hne_j : h' ≠ j := fun h => by
        have hV' : 2 ≤ (V_J h').card := hV_h'
        rw [h] at hV'
        omega
      obtain ⟨_, hcases⟩ := (orReaches_iff n C h' j).mp hor_h'_j
      rcases hcases with h_eq | ⟨hop', i, hin, hilt, hor_i_j⟩
      · exact (hne_j h_eq.symm).elim
      obtain ⟨d, hd⟩ := (operands model hh'_len i).mp hin
      rw [← hd] at hor_i_j hilt
      have hni : n ≤ opnd C h' d := hor_i_j.1
      let h'' := opnd C h' d - n
      have hh''_eq : n + h'' = opnd C h' d := by omega
      have hh''_lt : h'' < h' := by dsimp only [h', h''] at hilt hni hh''_eq ⊢; omega
      have hh''_len : h'' < C.gates.length := by omega
      have hor_h''_j : OrReaches n C (n + h'') j := hh''_eq ▸ hor_i_j
      have hor_h'_h'' : OrReaches n C (n + h') h'' :=
        (orReaches_iff n C h' h'').mpr ⟨hh'_len, Or.inr ⟨hop', opnd C h' d,
          (operands model hh'_len _).mpr ⟨d, rfl⟩, hilt,
          hh''_eq ▸ (orReaches_iff n C h'' h'').mpr ⟨hh''_len, Or.inl rfl⟩⟩⟩
      have hor_h0_h'' : OrReaches n C (n + h0) h'' := orReaches_trans hor_h0_h' hor_h'_h''
      have hV_h'' : (V_J h'').card ≤ 1 := by
        by_contra hcon
        have hmem_K : h'' ∈ K := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hh''_len, hor_h0_h'', hor_h''_j, by omega⟩
        have hle := K.min'_le h'' hmem_K
        change h' ≤ h'' at hle
        omega
      have hU_h' : (U_A h').card ≤ 1 := (hUV h').resolve_right (Nat.not_le_of_lt hV_h')
      have hu_h' : u ∈ U_A h' := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, a, ha, b, hsa, hh0_eq ▸ hor_h0_h'⟩
      have hv_h'' : v ∈ V_J h'' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, hsj, hor_h''_j⟩
      refine Finset.mem_biUnion.mpr ⟨(h', d), ?_, Finset.mem_image.mpr ⟨(u, v),
        Finset.mem_product.mpr ⟨hu_h', hv_h''⟩, rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hh'_len, Finset.mem_univ _⟩,
        hU_h', hV_h''⟩
  have h1a_sg1 : E1a_sg1.card ≤ 2 * C.size := by
    have hbi := Finset.card_biUnion_le_card_mul
      ((tops G C ×ˢ (Finset.univ : Finset (Fin 2))).filter
        fun p => (side (n := n) C p.1 p.2).card ≤ 1 ∧ (V_J (opnd C p.1 (1 - p.2) - n)).card ≤ 1)
      (fun p => (side (n := n) C p.1 p.2 ×ˢ V_J (opnd C p.1 (1 - p.2) - n)).image fun q => s(q.1, q.2)) 1
      (fun p hp => by
        rw [Finset.mem_filter] at hp
        have hi : ((side (n := n) C p.1 p.2 ×ˢ V_J (opnd C p.1 (1 - p.2) - n)).image fun q => s(q.1, q.2)).card ≤
            (side (n := n) C p.1 p.2 ×ˢ V_J (opnd C p.1 (1 - p.2) - n)).card := Finset.card_image_le
        rw [Finset.card_product] at hi
        have : (side (n := n) C p.1 p.2).card * (V_J (opnd C p.1 (1 - p.2) - n)).card ≤ 1 * 1 :=
          Nat.mul_le_mul hp.2.1 hp.2.2
        omega)
    change E1a_sg1.card ≤ _ at hbi
    have htop_le : (tops G C).card ≤ C.gates.length := by
      delta tops gatesWhere
      convert (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    have hflt := Finset.card_filter_le (tops G C ×ˢ (Finset.univ : Finset (Fin 2)))
      (fun p => (side (n := n) C p.1 p.2).card ≤ 1 ∧ (V_J (opnd C p.1 (1 - p.2) - n)).card ≤ 1)
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hflt
    dsimp only [Circuit.size]
    omega
  have h1a_sg2 : E1a_sg2.card ≤ 2 * C.size := by
    have hbi := Finset.card_biUnion_le_card_mul
      ((Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))).filter
        fun p => (U_A p.1).card ≤ 1 ∧ (V_J (opnd C p.1 p.2 - n)).card ≤ 1)
      (fun p => (U_A p.1 ×ˢ V_J (opnd C p.1 p.2 - n)).image fun q => s(q.1, q.2)) 1
      (fun p hp => by
        rw [Finset.mem_filter] at hp
        have hi : ((U_A p.1 ×ˢ V_J (opnd C p.1 p.2 - n)).image fun q => s(q.1, q.2)).card ≤
            (U_A p.1 ×ˢ V_J (opnd C p.1 p.2 - n)).card := Finset.card_image_le
        rw [Finset.card_product] at hi
        have : (U_A p.1).card * (V_J (opnd C p.1 p.2 - n)).card ≤ 1 * 1 :=
          Nat.mul_le_mul hp.2.1 hp.2.2
        omega)
    change E1a_sg2.card ≤ _ at hbi
    have hflt := Finset.card_filter_le (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2)))
      (fun p => (U_A p.1).card ≤ 1 ∧ (V_J (opnd C p.1 p.2 - n)).card ≤ 1)
    rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin] at hflt
    dsimp only [Circuit.size]
    omega
  have h1a_sub : E1a ⊆ E1a_br ∪ E1a_sg := by
    intro e he
    have he' := he
    rw [Finset.mem_filter] at he'
    obtain ⟨_, u, v, rfl, a, ha, b, j, hj, hus, hor, hvS, hSc⟩ := he'
    rw [Finset.mem_union]
    by_cases h2 : 2 ≤ (side (n := n) C a b).card
    · exact Or.inl (Finset.mem_filter.mpr ⟨he, u, v, rfl, a, ha, b, j, hj, hus, hor, hvS, hSc, h2⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨he, u, v, rfl, a, ha, b, j, hj, hus, hor, hvS, hSc, by omega⟩)
  have h1a : E1a.card ≤ 6 * C.size := by
    have h1 := (Finset.card_le_card h1a_sub).trans (Finset.card_union_le _ _)
    have h2 := (Finset.card_le_card h1a_sg_sub).trans (Finset.card_union_le _ _)
    omega
  -- Bound E1b ≤ 6 * C.size
  let J1b := (junk G C).filter fun j => (T_J j).Nonempty ∧ (T_J j).card ≤ 1
  have hJ1b_wit : ∀ j ∈ J1b, ∃ u : Fin n, ∃ c : Fin 2, ∃ z : Fin n,
      T_J j = {u} ∧ ∀ w ∈ side C j c, w ≠ z → G.Adj u w := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hj_junk, ⟨u, hu⟩, hTc⟩ := hj
    have hTu : T_J j = {u} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨hu, fun y hy => Finset.card_le_one.mp hTc y hy u hu⟩
    rw [Finset.mem_filter] at hu
    obtain ⟨_, a, ha, b, hus, hor⟩ := hu
    obtain ⟨c, hcle⟩ := three_vertex_witness_junk G model hno hj_junk
      (topContact_wmax G model ha b u hus hor)
    obtain ⟨z, hz⟩ := exists_outlier_of_filter_le_one G (side C j c) u hcle
    exact ⟨u, c, z, hTu, hz⟩
  choose uJ cJ zJ hJ1b_spec using hJ1b_wit
  let E1b_out := J1b.attach.biUnion fun j => {s(uJ j.1 j.2, zJ j.1 j.2)}
  let E1b_small := J1b.attach.biUnion fun j =>
    ((side C j.1 (cJ j.1 j.2)).erase (zJ j.1 j.2)).filter
      (fun _ => ((side C j.1 (cJ j.1 j.2)).erase (zJ j.1 j.2)).card ≤ 1) |>.image
      fun v => s(uJ j.1 j.2, v)
  let E1b_dag := E1b.filter fun e => ∃ u v z : Fin n, ∃ w : ℕ, e = s(u, v) ∧
    v ∈ orIn n C w ∧ v ≠ z ∧ 2 ≤ ((orIn n C w).erase z).card ∧
    ∀ y ∈ orIn n C w, y ≠ z → G.Adj u y
  have h1b_sub : E1b ⊆ E1b_out ∪ E1b_small ∪ E1b_dag := by
    intro e he
    have he' := he
    rw [Finset.mem_filter] at he'
    obtain ⟨_, u, v, rfl, a, ha, b, j, hj, hus, hor, hvS, hTc⟩ := he'
    have huT : u ∈ T_J j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, b, hus, hor⟩
    have hj1b : j ∈ J1b := Finset.mem_filter.mpr ⟨hj, ⟨u, huT⟩, hTc⟩
    obtain ⟨hTu, hadj⟩ := hJ1b_spec j hj1b
    have hu_eq : u = uJ j hj1b := by
      rw [hTu, Finset.mem_singleton] at huT
      exact huT
    subst hu_eq
    have hv_side : v ∈ side C j (cJ j hj1b) := by
      rw [Finset.mem_inter] at hvS
      have hc2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
      rcases hc2 (cJ j hj1b) with hc | hc <;> rw [hc]
      · exact hvS.1
      · exact hvS.2
    rw [Finset.mem_union, Finset.mem_union]
    by_cases hvz : v = zJ j hj1b
    · left; left
      subst hvz
      exact Finset.mem_biUnion.mpr ⟨⟨j, hj1b⟩, Finset.mem_attach _ _, Finset.mem_singleton_self _⟩
    · by_cases hsc : ((side C j (cJ j hj1b)).erase (zJ j hj1b)).card ≤ 1
      · left; right
        refine Finset.mem_biUnion.mpr ⟨⟨j, hj1b⟩, Finset.mem_attach _ _,
          Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hvz, hv_side⟩, hsc⟩, rfl⟩⟩
      · right
        exact Finset.mem_filter.mpr ⟨he, uJ j hj1b, v, zJ j hj1b, opnd C j (cJ j hj1b), rfl,
          hv_side, hvz, (by dsimp only [side] at hsc; omega), hadj⟩
  have hJ1b_card : J1b.card ≤ C.size := by
    have h1 : J1b.card ≤ (junk G C).card := Finset.card_filter_le _ _
    have h2 : (junk G C).card ≤ C.gates.length :=
      (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    dsimp only [Circuit.size]
    omega
  have h1b_out : E1b_out.card ≤ C.size := by
    have hbi := Finset.card_biUnion_le_card_mul J1b.attach
      (fun j => {s(uJ j.1 j.2, zJ j.1 j.2)}) 1 (fun _ _ => by rw [Finset.card_singleton])
    change E1b_out.card ≤ _ at hbi
    rw [Finset.card_attach] at hbi
    omega
  have h1b_small : E1b_small.card ≤ C.size := by
    have hbi := Finset.card_biUnion_le_card_mul J1b.attach
      (fun j => (((side C j.1 (cJ j.1 j.2)).erase (zJ j.1 j.2)).filter
        (fun _ => ((side C j.1 (cJ j.1 j.2)).erase (zJ j.1 j.2)).card ≤ 1)).image
        fun v => s(uJ j.1 j.2, v)) 1
      (fun j _ => by
        refine (Finset.card_image_le).trans ?_
        by_cases hc : ((side C j.1 (cJ j.1 j.2)).erase (zJ j.1 j.2)).card ≤ 1
        · exact (Finset.card_filter_le _ _).trans hc
        · simp [hc])
    change E1b_small.card ≤ _ at hbi
    rw [Finset.card_attach] at hbi
    omega
  have h1b_dag : E1b_dag.card ≤ 4 * C.size := by
    have hb := one_outlier_or_dag_bound G model hno E1b
    convert hb
  have h1b : E1b.card ≤ 6 * C.size := by
    have h1 := (Finset.card_le_card h1b_sub).trans (Finset.card_union_le _ _)
    have h2 := Finset.card_union_le E1b_out E1b_small
    omega
  have htot := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  omega

open Classical in
private lemma case2_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (model : IsAO2 n C) (hno : NoFourCycle G) (c : Fin 2) :
    ((Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
      ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
      u ∈ side C j c ∧ v ∈ side C j (1 - c)).card ≤ 43 * C.size := by
  classical
  let P_J : ℕ → Finset (Fin n) := fun j => wmax G C j ∩ side C j c
  let Q_J : ℕ → Finset (Fin n) := fun j => side C j (1 - c)
  have hbic : ∀ j ∈ junk G C, (P_J j).card ≤ 1 ∨ (Q_J j).card ≤ 1 := by
    intro j hj
    refine biclique_star hno (P_J j) (Q_J j) ?_
    intro u hu v hv
    rw [Finset.mem_inter] at hu
    have hfin : (0 : Fin 2) = c ∧ (1 : Fin 2) = 1 - c ∨ (0 : Fin 2) = 1 - c ∧ (1 : Fin 2) = c := by
      fin_cases c <;> decide
    rcases hfin with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact wmax_adj_of_pair G model hj hu.1 (Or.inl (h0 ▸ hu.2)) (Or.inr (h1 ▸ hv))
    · exact wmax_adj_of_pair G model hj hu.1 (Or.inr (h0 ▸ hv)) (Or.inl (h1 ▸ hu.2))
  let E2b := (Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    u ∈ side C j c ∧ v ∈ side C j (1 - c) ∧ (P_J j).card ≤ 1
  let E2a := (Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    u ∈ side C j c ∧ v ∈ side C j (1 - c) ∧ (Q_J j).card ≤ 1
  have hsplit : ((Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
      ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
      u ∈ side C j c ∧ v ∈ side C j (1 - c)) ⊆ E2b ∪ E2a := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heU, u, v, rfl, a, ha, b, j, hj, hus, hor, huc, hvc⟩ := he
    rw [Finset.mem_union]
    rcases hbic j hj with hP | hQ
    · exact Or.inl (Finset.mem_filter.mpr ⟨heU, u, v, rfl, a, ha, b, j, hj, hus, hor, huc, hvc, hP⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨heU, u, v, rfl, a, ha, b, j, hj, hus, hor, huc, hvc, hQ⟩)
  -- Bound E2b ≤ 3 * C.size
  let E2b_sg := ((junk G C).filter fun j => (P_J j).card ≤ 1 ∧ (Q_J j).card ≤ 1).biUnion
    fun j => (P_J j ×ˢ Q_J j).image fun q => s(q.1, q.2)
  let E2b_br := E2b.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ w : ℕ,
    v ∈ orIn n C w ∧ 2 ≤ (orIn n C w).card ∧ ∀ y ∈ orIn n C w, G.Adj u y
  have h2b_sub : E2b ⊆ E2b_sg ∪ E2b_br := by
    intro e he
    have he' := he
    rw [Finset.mem_filter] at he'
    obtain ⟨_, u, v, rfl, a, ha, b, j, hj, hus, hor, huc, hvc, hPc⟩ := he'
    have huP : u ∈ P_J j := Finset.mem_inter.mpr ⟨topContact_wmax G model ha b u hus hor, huc⟩
    rw [Finset.mem_union]
    by_cases hQc : (Q_J j).card ≤ 1
    · left
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hPc, hQc⟩,
        Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨huP, hvc⟩, rfl⟩⟩
    · right
      refine Finset.mem_filter.mpr ⟨he, u, v, rfl, opnd C j (1 - c), hvc,
        (by dsimp only [Q_J, side] at hQc; omega), fun y hy => ?_⟩
      have hfin : (0 : Fin 2) = c ∧ (1 : Fin 2) = 1 - c ∨ (0 : Fin 2) = 1 - c ∧ (1 : Fin 2) = c := by
        fin_cases c <;> decide
      rcases hfin with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact wmax_adj_of_pair G model hj (Finset.mem_inter.mp huP).1 (Or.inl (h0 ▸ huc)) (Or.inr (h1 ▸ hy))
      · exact wmax_adj_of_pair G model hj (Finset.mem_inter.mp huP).1 (Or.inr (h0 ▸ hy)) (Or.inl (h1 ▸ huc))
  have hjunk_le : (junk G C).card ≤ C.size := by
    have := Finset.card_filter_le (Finset.range C.gates.length) (fun j => IsDirtyAnd n G C j)
    rw [Finset.card_range] at this
    exact this
  have h2b_sg : E2b_sg.card ≤ C.size := by
    have hbi := Finset.card_biUnion_le_card_mul
      ((junk G C).filter fun j => (P_J j).card ≤ 1 ∧ (Q_J j).card ≤ 1)
      (fun j => (P_J j ×ˢ Q_J j).image fun q => s(q.1, q.2)) 1
      (fun j hj => by
        rw [Finset.mem_filter] at hj
        have hi : ((P_J j ×ˢ Q_J j).image fun q => s(q.1, q.2)).card ≤ (P_J j ×ˢ Q_J j).card :=
          Finset.card_image_le
        rw [Finset.card_product] at hi
        have : (P_J j).card * (Q_J j).card ≤ 1 * 1 := Nat.mul_le_mul hj.2.1 hj.2.2
        omega)
    change E2b_sg.card ≤ _ at hbi
    have hflt := Finset.card_filter_le (junk G C) (fun j => (P_J j).card ≤ 1 ∧ (Q_J j).card ≤ 1)
    omega
  have h2b_br : E2b_br.card ≤ 2 * C.size := by
    have hb := branching_or_bound G model hno E2b
    convert hb
  have h2b : E2b.card ≤ 3 * C.size := by
    have := (Finset.card_le_card h2b_sub).trans (Finset.card_union_le _ _)
    omega
  -- Split E2a into J_alpha and J_beta
  let J_alpha := (junk G C).filter fun j => (Q_J j).card = 1 ∧
    ∃ v ∈ Q_J j, ((side C j c).filter (fun w => ¬ G.Adj v w)).card ≤ 1
  let J_beta := (junk G C).filter fun j => (Q_J j).card = 1 ∧
    ∀ v ∈ Q_J j, 2 ≤ ((side C j c).filter (fun w => ¬ G.Adj v w)).card
  let E2a_alpha := E2a.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ J_alpha, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    u ∈ side C j c ∧ Q_J j = {v}
  let E2a_beta := E2a.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ J_beta, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    u ∈ side C j c ∧ Q_J j = {v}
  have h2a_split : E2a ⊆ E2a_alpha ∪ E2a_beta := by
    intro e he
    have he' := he
    rw [Finset.mem_filter] at he'
    obtain ⟨_, u, v, rfl, a, ha, b, j, hj, hus, hor, huc, hvc, hQc⟩ := he'
    have hQ1 : (Q_J j).card = 1 := by
      have : 0 < (Q_J j).card := Finset.card_pos.mpr ⟨v, hvc⟩
      omega
    have hQs : Q_J j = {v} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨hvc, fun y hy => Finset.card_le_one.mp hQc y hy v hvc⟩
    rw [Finset.mem_union]
    by_cases hα : ((side C j c).filter (fun w => ¬ G.Adj v w)).card ≤ 1
    · left
      exact Finset.mem_filter.mpr ⟨he, u, v, rfl, a, ha, b, j,
        Finset.mem_filter.mpr ⟨hj, hQ1, v, hvc, hα⟩, hus, hor, huc, hQs⟩
    · right
      have hβ : ∀ v' ∈ Q_J j, 2 ≤ ((side C j c).filter (fun w => ¬ G.Adj v' w)).card := by
        intro v' hv'
        rw [hQs, Finset.mem_singleton] at hv'
        subst hv'
        omega
      exact Finset.mem_filter.mpr ⟨he, u, v, rfl, a, ha, b, j,
        Finset.mem_filter.mpr ⟨hj, hQ1, hβ⟩, hus, hor, huc, hQs⟩
  -- Bound E2a_alpha ≤ 6 * C.size
  have hJa_wit : ∀ j ∈ J_alpha, ∃ v : Fin n, ∃ z : Fin n,
      Q_J j = {v} ∧ ∀ w ∈ side C j c, w ≠ z → G.Adj v w := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨_, hQ1, v, hv, hle⟩ := hj
    have hQs : Q_J j = {v} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨hv, fun y hy => Finset.card_le_one.mp (by omega) y hy v hv⟩
    obtain ⟨z, hz⟩ := exists_outlier_of_filter_le_one G (side C j c) v hle
    exact ⟨v, z, hQs, hz⟩
  choose vJa zJa hJa_spec using hJa_wit
  let E2a_a_out := J_alpha.attach.biUnion fun j => {s(vJa j.1 j.2, zJa j.1 j.2)}
  let E2a_a_small := J_alpha.attach.biUnion fun j =>
    (((side C j.1 c).erase (zJa j.1 j.2)).filter
      (fun _ => ((side C j.1 c).erase (zJa j.1 j.2)).card ≤ 1)).image
      fun u => s(vJa j.1 j.2, u)
  let E2a_a_dag := E2a_alpha.filter fun e => ∃ u v z : Fin n, ∃ w : ℕ, e = s(u, v) ∧
    v ∈ orIn n C w ∧ v ≠ z ∧ 2 ≤ ((orIn n C w).erase z).card ∧
    ∀ y ∈ orIn n C w, y ≠ z → G.Adj u y
  have h2a_a_sub : E2a_alpha ⊆ E2a_a_out ∪ E2a_a_small ∪ E2a_a_dag := by
    intro e he
    have he' := he
    rw [Finset.mem_filter] at he'
    obtain ⟨_, u, v, rfl, a, ha, b, j, hj, hus, hor, huc, hQs⟩ := he'
    obtain ⟨hQs', hadj⟩ := hJa_spec j hj
    have hv_eq : v = vJa j hj := Finset.singleton_injective (hQs.symm.trans hQs')
    subst hv_eq
    rw [Finset.mem_union, Finset.mem_union]
    by_cases huz : u = zJa j hj
    · left; left
      subst huz
      exact Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, Finset.mem_attach _ _,
        by rw [Sym2.eq_swap]; exact Finset.mem_singleton_self _⟩
    · by_cases hsc : ((side C j c).erase (zJa j hj)).card ≤ 1
      · left; right
        refine Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, Finset.mem_attach _ _,
          Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨huz, huc⟩, hsc⟩, Sym2.eq_swap⟩⟩
      · right
        exact Finset.mem_filter.mpr ⟨he, vJa j hj, u, zJa j hj, opnd C j c, Sym2.eq_swap,
          huc, huz, (by dsimp only [side] at hsc; omega), hadj⟩
  have hJa_card : J_alpha.card ≤ C.size := (Finset.card_filter_le _ _).trans hjunk_le
  have h2a_a_out : E2a_a_out.card ≤ C.size := by
    have hbi := Finset.card_biUnion_le_card_mul J_alpha.attach
      (fun j => {s(vJa j.1 j.2, zJa j.1 j.2)}) 1 (fun _ _ => by rw [Finset.card_singleton])
    change E2a_a_out.card ≤ _ at hbi
    rw [Finset.card_attach] at hbi
    omega
  have h2a_a_small : E2a_a_small.card ≤ C.size := by
    have hbi := Finset.card_biUnion_le_card_mul J_alpha.attach
      (fun j => (((side C j.1 c).erase (zJa j.1 j.2)).filter
        (fun _ => ((side C j.1 c).erase (zJa j.1 j.2)).card ≤ 1)).image
        fun u => s(vJa j.1 j.2, u)) 1
      (fun j _ => by
        refine (Finset.card_image_le).trans ?_
        by_cases hc : ((side C j.1 c).erase (zJa j.1 j.2)).card ≤ 1
        · exact (Finset.card_filter_le _ _).trans hc
        · simp [hc])
    change E2a_a_small.card ≤ _ at hbi
    rw [Finset.card_attach] at hbi
    omega
  have h2a_a_dag : E2a_a_dag.card ≤ 4 * C.size := by
    have hb := one_outlier_or_dag_bound G model hno E2a_alpha
    convert hb
  have h2a_a : E2a_alpha.card ≤ 6 * C.size := by
    have h1 := (Finset.card_le_card h2a_a_sub).trans (Finset.card_union_le _ _)
    have h2 := Finset.card_union_le E2a_a_out E2a_a_small
    omega
  -- Bound E2a_beta ≤ 34 * C.size
  have hJb_top : ∀ {a : ℕ} {b : Fin 2} {j : ℕ} {v : Fin n},
      a ∈ tops G C → j ∈ J_beta → OrReaches n C (opnd C a (1 - b)) j → Q_J j = {v} →
      ((side C a b).filter (fun w => ¬ G.Adj v w)).card ≤ 1 := by
    intro a b j v ha hj hor hQs
    rw [Finset.mem_filter] at hj
    obtain ⟨hj_junk, _, hβ⟩ := hj
    have hv : v ∈ Q_J j := by rw [hQs]; exact Finset.mem_singleton_self v
    have h2 := hβ v hv
    rcases three_vertex_witness_top G model hno ha b hj_junk hor c hv with h | h
    · exact h
    · omega
  let E2a_b1 := E2a_beta.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ J_beta, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    Q_J j = {v} ∧ 4 ≤ (side (n := n) C a b).card
  let E2a_b2 := E2a_beta.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ J_beta, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    Q_J j = {v} ∧ (side (n := n) C a b).card ≤ 3
  have h2a_b1 : E2a_b1.card ≤ 4 * C.size := by
    have hsub : E2a_b1 ⊆ E2a_beta.filter fun e => ∃ u v z : Fin n, ∃ w : ℕ, e = s(u, v) ∧
        v ∈ orIn n C w ∧ v ≠ z ∧ 2 ≤ ((orIn n C w).erase z).card ∧
        ∀ y ∈ orIn n C w, y ≠ z → G.Adj u y := by
      intro e he
      rw [Finset.mem_filter] at he ⊢
      refine ⟨he.1, ?_⟩
      obtain ⟨u, v, rfl, a, ha, b, j, hj, hus, hor, hQs, h4⟩ := he.2
      have heU : s(u, v) ∈ Ustar G C := (Finset.mem_filter.mp (Finset.mem_filter.mp he.1).1).1
      have huv_adj : G.Adj v u := by
        have hmem := (Finset.mem_sdiff.mp heU).1
        rw [SimpleGraph.mem_edgeFinset] at hmem
        exact hmem.symm
      obtain ⟨z, hz⟩ := exists_outlier_of_filter_le_one G (side C a b) v
        (hJb_top ha hj hor hQs)
      by_cases huz : u = z
      · have hpos : 0 < ((side C a b).erase u).card := by
          have := Finset.card_erase_add_one hus; omega
        obtain ⟨z', hz'⟩ := Finset.card_pos.mp hpos
        have hzne : u ≠ z' := (Finset.mem_erase.mp hz').1.symm
        have hc2 : 2 ≤ ((side C a b).erase z').card := by
          have := Finset.card_erase_le (a := z') (s := side C a b)
          have := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hzne.symm, (Finset.mem_erase.mp hz').2⟩)
          by_cases hzm : z' ∈ side C a b
          · have := Finset.card_erase_add_one hzm; omega
          · rw [Finset.erase_eq_of_notMem hzm]; omega
        refine ⟨v, u, z', opnd C a b, Sym2.eq_swap, hus, hzne, hc2, fun y hy hyn => ?_⟩
        by_cases hyu : y = u
        · rw [hyu]; exact huv_adj
        · exact hz y hy (huz ▸ hyu)
      · have hc2 : 2 ≤ ((side C a b).erase z).card := by
          by_cases hzm : z ∈ side C a b
          · have := Finset.card_erase_add_one hzm; omega
          · rw [Finset.erase_eq_of_notMem hzm]; omega
        exact ⟨v, u, z, opnd C a b, Sym2.eq_swap, hus, huz, hc2, hz⟩
    have hb := one_outlier_or_dag_bound G model hno E2a_beta
    exact (Finset.card_le_card hsub).trans (by convert hb)
  have hJb_wmax_nonadj : ∀ {j : ℕ} {v : Fin n}, j ∈ J_beta → Q_J j = {v} →
      ∀ {u1 u2 : Fin n}, u1 ∈ wmax G C j → u2 ∈ wmax G C j →
      ¬ G.Adj u1 v → ¬ G.Adj u2 v → u1 = u2 := by
    intro j v hj hQs u1 u2 hw1 hw2 hna1 hna2
    rw [Finset.mem_filter] at hj
    obtain ⟨hj_junk, _, hβ⟩ := hj
    have hv : v ∈ Q_J j := by rw [hQs]; exact Finset.mem_singleton_self v
    have h2 := hβ v hv
    obtain ⟨z1, hz1, z2, hz2, hz12⟩ := Finset.one_lt_card.mp (by omega : 1 < ((side C j c).filter (fun w => ¬ G.Adj v w)).card)
    rw [Finset.mem_filter] at hz1 hz2
    have hadj_z : ∀ {u : Fin n}, u ∈ wmax G C j → ¬ G.Adj u v →
        ∀ {z : Fin n}, z ∈ side C j c → ¬ G.Adj v z → G.Adj u z := by
      intro u hu hna z hzc hzv
      have hgw : graphFun G ∅ (tripleInput u v z) = true := by
        dsimp only [wmax] at hu
        simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        refine hu (tripleInput u v z) (junkUp G model hj_junk _ ?_) (tripleInput_one u v z)
        intro d
        have hfin : d = c ∨ d = 1 - c := by fin_cases c <;> fin_cases d <;> decide
        rcases hfin with rfl | rfl
        · exact ⟨z, hzc, tripleInput_three u v z⟩
        · exact ⟨v, hv, tripleInput_two u v z⟩
      rcases graphFun_triple G u v z hgw with h | h | h
      · exact (hna h).elim
      · exact h
      · exact (hzv h).elim
    by_contra hne
    exact no4_common hno hne hz12
      (hadj_z hw1 hna1 hz1.1 hz1.2) (hadj_z hw2 hna2 hz1.1 hz1.2)
      (hadj_z hw1 hna1 hz2.1 hz2.2) (hadj_z hw2 hna2 hz2.1 hz2.2)
  let U_3 : ℕ → Finset (Fin n) := fun h =>
    Finset.univ.filter fun u => ∃ a ∈ tops G C, ∃ b : Fin 2,
      (side (n := n) C a b).card ≤ 3 ∧ u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) h
  let V'_J : ℕ → Finset (Fin n) := fun h =>
    Finset.univ.filter fun v => ∃ j ∈ J_beta,
      Q_J j = {v} ∧ OrReaches n C (n + h) j
  have hUV3 : ∀ h, (U_3 h).card ≤ 2 ∨ (V'_J h).card ≤ 3 := by
    intro h
    by_contra hcon
    simp (config := {congrConsts := false}) only [not_or, not_le] at hcon
    obtain ⟨u1, hu1, U', _⟩ := Finset.one_lt_card.mp (by omega : 1 < (U_3 h).card)
    have hpos : 1 < ((U_3 h).erase u1).card := by
      have := Finset.card_erase_add_one hu1; omega
    obtain ⟨u2, hu2', u3, hu3', hu23⟩ := Finset.one_lt_card.mp hpos
    have hu2 : u2 ∈ U_3 h := (Finset.mem_erase.mp hu2').2
    have hu12 : u1 ≠ u2 := (Finset.mem_erase.mp hu2').1.symm
    have hu3 : u3 ∈ U_3 h := (Finset.mem_erase.mp hu3').2
    have hu13 : u1 ≠ u3 := (Finset.mem_erase.mp hu3').1.symm
    rw [Finset.mem_filter] at hu1 hu2 hu3
    obtain ⟨_, a1, ha1, b1, _, hus1, hor1⟩ := hu1
    obtain ⟨_, a2, ha2, b2, _, hus2, hor2⟩ := hu2
    obtain ⟨_, a3, ha3, b3, _, hus3, hor3⟩ := hu3
    let C12 := Finset.univ.filter fun v : Fin n => G.Adj u1 v ∧ G.Adj u2 v
    let C13 := Finset.univ.filter fun v : Fin n => G.Adj u1 v ∧ G.Adj u3 v
    let C23 := Finset.univ.filter fun v : Fin n => G.Adj u2 v ∧ G.Adj u3 v
    have hVsub : V'_J h ⊆ C12 ∪ C13 ∪ C23 := by
      intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨_, j, hj, hQs, horj⟩ := hv
      have hw1 : u1 ∈ wmax G C j := topContact_wmax G model ha1 b1 u1 hus1 (orReaches_trans hor1 horj)
      have hw2 : u2 ∈ wmax G C j := topContact_wmax G model ha2 b2 u2 hus2 (orReaches_trans hor2 horj)
      have hw3 : u3 ∈ wmax G C j := topContact_wmax G model ha3 b3 u3 hus3 (orReaches_trans hor3 horj)
      rw [Finset.mem_union, Finset.mem_union]
      by_cases h1 : G.Adj u1 v
      · by_cases h2 : G.Adj u2 v
        · left; left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩
        · by_cases h3 : G.Adj u3 v
          · left; right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h3⟩
          · exact (hu23 (hJb_wmax_nonadj hj hQs hw2 hw3 h2 h3)).elim
      · by_cases h2 : G.Adj u2 v
        · by_cases h3 : G.Adj u3 v
          · right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, h3⟩
          · exact (hu13 (hJb_wmax_nonadj hj hQs hw1 hw3 h1 h3)).elim
        · exact (hu12 (hJb_wmax_nonadj hj hQs hw1 hw2 h1 h2)).elim
    have hc12 : C12.card ≤ 1 := hno u1 u2 hu12
    have hc13 : C13.card ≤ 1 := hno u1 u3 hu13
    have hc23 : C23.card ≤ 1 := hno u2 u3 hu23
    have hcard := (Finset.card_le_card hVsub).trans (Finset.card_union_le _ _)
    have hcard' := Finset.card_union_le C12 C13
    omega
  let E2a_b2_1 := ((tops G C ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun p => (side (n := n) C p.1 p.2).card ≤ 3 ∧ (V'_J (opnd C p.1 (1 - p.2) - n)).card ≤ 3).biUnion
    fun p => (side (n := n) C p.1 p.2 ×ˢ V'_J (opnd C p.1 (1 - p.2) - n)).image fun q => s(q.1, q.2)
  let E2a_b2_2 := ((Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun p => (U_3 p.1).card ≤ 2 ∧ (V'_J (opnd C p.1 p.2 - n)).card ≤ 3).biUnion
    fun p => (U_3 p.1 ×ˢ V'_J (opnd C p.1 p.2 - n)).image fun q => s(q.1, q.2)
  have h2a_b2_sub : E2a_b2 ⊆ E2a_b2_1 ∪ E2a_b2_2 := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨_, u, v, rfl, a, ha, b, j, hj, hus, hor, hQs, h3⟩ := he
    have hnw : n ≤ opnd C a (1 - b) := hor.1
    have hlt_a : opnd C a (1 - b) < n + a := opnd_lt model (topGate G ha).1 (1 - b)
    let h0 := opnd C a (1 - b) - n
    have hh0_eq : n + h0 = opnd C a (1 - b) := by omega
    have hor0 : OrReaches n C (n + h0) j := hh0_eq ▸ hor
    have hv0 : v ∈ V'_J h0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, hQs, hor0⟩
    rw [Finset.mem_union]
    by_cases hV0 : (V'_J h0).card ≤ 3
    · left
      refine Finset.mem_biUnion.mpr ⟨(a, b), ?_, Finset.mem_image.mpr ⟨(u, v),
        Finset.mem_product.mpr ⟨hus, hv0⟩, rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩, h3, hV0⟩
    · right
      let K := (Finset.range C.gates.length).filter fun k =>
        OrReaches n C (n + h0) k ∧ OrReaches n C (n + k) j ∧ 4 ≤ (V'_J k).card
      have hh0_len : h0 < C.gates.length := by have := (topGate G ha).1; omega
      have hK_ne : K.Nonempty := ⟨h0, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hh0_len, (orReaches_iff n C h0 h0).mpr ⟨hh0_len, Or.inl rfl⟩,
          hor0, by omega⟩⟩
      let h' := K.min' hK_ne
      have hh'_mem := K.min'_mem hK_ne
      rw [Finset.mem_filter, Finset.mem_range] at hh'_mem
      obtain ⟨hh'_len, hor_h0_h', hor_h'_j, hV_h'⟩ := hh'_mem
      have hj_junk : j ∈ junk G C := (Finset.mem_filter.mp hj).1
      have hV_j : (V'_J j).card ≤ 3 := by
        have hsub_j : V'_J j ⊆ {v} := by
          intro v' hv'
          rw [Finset.mem_filter] at hv'
          obtain ⟨_, j', hj', hQs', horj'⟩ := hv'
          obtain ⟨_, hcases⟩ := (orReaches_iff n C j j').mp horj'
          rcases hcases with rfl | ⟨hopj, _⟩
          · rw [Finset.mem_singleton]
            exact Finset.singleton_injective (hQs'.symm.trans hQs)
          · exfalso; have := (junkGate G hj_junk).2; rw [hopj] at this; cases this
        exact (Finset.card_le_card hsub_j).trans (by rw [Finset.card_singleton]; omega)
      have hne_j : h' ≠ j := fun h => by
        have hV' : 4 ≤ (V'_J h').card := hV_h'
        rw [h] at hV'
        omega
      obtain ⟨_, hcases⟩ := (orReaches_iff n C h' j).mp hor_h'_j
      rcases hcases with h_eq | ⟨hop', i, hin, hilt, hor_i_j⟩
      · exact (hne_j h_eq.symm).elim
      obtain ⟨d, hd⟩ := (operands model hh'_len i).mp hin
      rw [← hd] at hor_i_j hilt
      have hni : n ≤ opnd C h' d := hor_i_j.1
      let h'' := opnd C h' d - n
      have hh''_eq : n + h'' = opnd C h' d := by omega
      have hh''_lt : h'' < h' := by dsimp only [h', h''] at hilt hni hh''_eq ⊢; omega
      have hh''_len : h'' < C.gates.length := by omega
      have hor_h''_j : OrReaches n C (n + h'') j := hh''_eq ▸ hor_i_j
      have hor_h'_h'' : OrReaches n C (n + h') h'' :=
        (orReaches_iff n C h' h'').mpr ⟨hh'_len, Or.inr ⟨hop', opnd C h' d,
          (operands model hh'_len _).mpr ⟨d, rfl⟩, hilt,
          hh''_eq ▸ (orReaches_iff n C h'' h'').mpr ⟨hh''_len, Or.inl rfl⟩⟩⟩
      have hor_h0_h'' : OrReaches n C (n + h0) h'' := orReaches_trans hor_h0_h' hor_h'_h''
      have hV_h'' : (V'_J h'').card ≤ 3 := by
        by_contra hcon
        have hmem_K : h'' ∈ K := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hh''_len, hor_h0_h'', hor_h''_j, by omega⟩
        have hle := K.min'_le h'' hmem_K
        change h' ≤ h'' at hle
        omega
      have hU_h' : (U_3 h').card ≤ 2 := (hUV3 h').resolve_right (Nat.not_le_of_lt hV_h')
      have hu_h' : u ∈ U_3 h' := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, a, ha, b, h3, hus, hh0_eq ▸ hor_h0_h'⟩
      have hv_h'' : v ∈ V'_J h'' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, hQs, hor_h''_j⟩
      refine Finset.mem_biUnion.mpr ⟨(h', d), ?_, Finset.mem_image.mpr ⟨(u, v),
        Finset.mem_product.mpr ⟨hu_h', hv_h''⟩, rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hh'_len, Finset.mem_univ _⟩,
        hU_h', hV_h''⟩
  have h2a_b2_1 : E2a_b2_1.card ≤ 18 * C.size := by
    have hbi := Finset.card_biUnion_le_card_mul
      ((tops G C ×ˢ (Finset.univ : Finset (Fin 2))).filter
        fun p => (side (n := n) C p.1 p.2).card ≤ 3 ∧ (V'_J (opnd C p.1 (1 - p.2) - n)).card ≤ 3)
      (fun p => (side (n := n) C p.1 p.2 ×ˢ V'_J (opnd C p.1 (1 - p.2) - n)).image fun q => s(q.1, q.2)) 9
      (fun p hp => by
        rw [Finset.mem_filter] at hp
        have hi : ((side (n := n) C p.1 p.2 ×ˢ V'_J (opnd C p.1 (1 - p.2) - n)).image fun q => s(q.1, q.2)).card ≤
            (side (n := n) C p.1 p.2 ×ˢ V'_J (opnd C p.1 (1 - p.2) - n)).card := Finset.card_image_le
        rw [Finset.card_product] at hi
        have : (side (n := n) C p.1 p.2).card * (V'_J (opnd C p.1 (1 - p.2) - n)).card ≤ 3 * 3 :=
          Nat.mul_le_mul hp.2.1 hp.2.2
        omega)
    change E2a_b2_1.card ≤ _ at hbi
    have htop_le : (tops G C).card ≤ C.gates.length := by
      delta tops gatesWhere
      convert (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    have hflt := Finset.card_filter_le (tops G C ×ˢ (Finset.univ : Finset (Fin 2)))
      (fun p => (side (n := n) C p.1 p.2).card ≤ 3 ∧ (V'_J (opnd C p.1 (1 - p.2) - n)).card ≤ 3)
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hflt
    dsimp only [Circuit.size]
    omega
  have h2a_b2_2 : E2a_b2_2.card ≤ 12 * C.size := by
    have hbi := Finset.card_biUnion_le_card_mul
      ((Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))).filter
        fun p => (U_3 p.1).card ≤ 2 ∧ (V'_J (opnd C p.1 p.2 - n)).card ≤ 3)
      (fun p => (U_3 p.1 ×ˢ V'_J (opnd C p.1 p.2 - n)).image fun q => s(q.1, q.2)) 6
      (fun p hp => by
        rw [Finset.mem_filter] at hp
        have hi : ((U_3 p.1 ×ˢ V'_J (opnd C p.1 p.2 - n)).image fun q => s(q.1, q.2)).card ≤
            (U_3 p.1 ×ˢ V'_J (opnd C p.1 p.2 - n)).card := Finset.card_image_le
        rw [Finset.card_product] at hi
        have : (U_3 p.1).card * (V'_J (opnd C p.1 p.2 - n)).card ≤ 2 * 3 :=
          Nat.mul_le_mul hp.2.1 hp.2.2
        omega)
    change E2a_b2_2.card ≤ _ at hbi
    have hflt := Finset.card_filter_le (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2)))
      (fun p => (U_3 p.1).card ≤ 2 ∧ (V'_J (opnd C p.1 p.2 - n)).card ≤ 3)
    rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin] at hflt
    dsimp only [Circuit.size]
    omega
  have h2a_b2 : E2a_b2.card ≤ 30 * C.size := by
    have := (Finset.card_le_card h2a_b2_sub).trans (Finset.card_union_le _ _)
    omega
  have h2a_b_sub : E2a_beta ⊆ E2a_b1 ∪ E2a_b2 := by
    intro e he
    have he' := he
    rw [Finset.mem_filter] at he'
    obtain ⟨_, u, v, rfl, a, ha, b, j, hj, hus, hor, huc, hQs⟩ := he'
    rw [Finset.mem_union]
    by_cases h4 : 4 ≤ (side (n := n) C a b).card
    · exact Or.inl (Finset.mem_filter.mpr ⟨he, u, v, rfl, a, ha, b, j, hj, hus, hor, hQs, h4⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨he, u, v, rfl, a, ha, b, j, hj, hus, hor, hQs, by omega⟩)
  have h2a_b : E2a_beta.card ≤ 34 * C.size := by
    have := (Finset.card_le_card h2a_b_sub).trans (Finset.card_union_le _ _)
    omega
  have h2a : E2a.card ≤ 40 * C.size := by
    have := (Finset.card_le_card h2a_split).trans (Finset.card_union_le _ _)
    omega
  have htot := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  omega

private lemma main_bound : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2))
    [x4 : DecidableRel x3.Adj],
    (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
    x3.edgeFinset.Nonempty → ∀ (x7 : Circuit),
    IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (junk x3 x7).card →
    (∀ x11 ∈ junk x3 x7, ∀ x13 ∈ junk x3 x7, ¬ InCone x2 x7 x11 x13) →
    {x12 ∈ Ustar x3 x7 | ∃ (x13 : Fin x2) (x14 : Fin x2), x12 = s(x13, x14) ∧
      ∃ x15 ∈ tops x3 x7, ∃ (x16 : Fin 2), ∃ x17 ∈ junk x3 x7,
        x13 ∈ side x7 x15 x16 ∧ OrReaches x2 x7 (opnd x7 x15 ((1 : Fin 2) - x16)) x17 ∧
        gateVal x2 x7 x17 (pairInput x13 x14) = Bool.true}.card ≤ x1 * (x7.size + 1) := by
  refine ⟨98, fun n G _ hg _ C hL top _ anti => ?_⟩
  classical
  have model : IsAO2 n C := hL.1
  have hno : NoFourCycle G := noFourCycle_of_girth5 G hg
  let E1 := (Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    v ∈ side C j 0 ∧ v ∈ side C j 1
  let E20 := (Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    u ∈ side C j 0 ∧ v ∈ side C j (1 - 0)
  let E21 := (Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    ∃ j ∈ junk G C, u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) j ∧
    u ∈ side C j 1 ∧ v ∈ side C j (1 - 1)
  have hsub : {x12 ∈ Ustar G C | ∃ (x13 : Fin n) (x14 : Fin n), x12 = s(x13, x14) ∧
      ∃ x15 ∈ tops G C, ∃ (x16 : Fin 2), ∃ x17 ∈ junk G C,
        x13 ∈ side C x15 x16 ∧ OrReaches n C (opnd C x15 ((1 : Fin 2) - x16)) x17 ∧
        gateVal n C x17 (pairInput x13 x14) = Bool.true} ⊆ E1 ∪ E20 ∪ E21 := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heU, u, v, rfl, a, ha, b, j, hj, hus, hor, hgv⟩ := he
    have hw : u ∈ wmax G C j := topContact_wmax G model ha b u hus hor
    have hnb : ¬ (u ∈ side C j 0 ∧ u ∈ side C j 1) :=
      fun ⟨h0, h1⟩ => wmax_not_both_sides G model hj hw h0 h1
    have hj0 := junkDown G model top anti hj u v hgv 0
    have hj1 := junkDown G model top anti hj u v hgv 1
    rw [Finset.mem_union, Finset.mem_union]
    by_cases hv0 : v ∈ side C j 0
    · by_cases hv1 : v ∈ side C j 1
      · left; left
        exact Finset.mem_filter.mpr ⟨heU, u, v, rfl, a, ha, b, j, hj, hus, hor, hv0, hv1⟩
      · right
        have hu1 : u ∈ side C j 1 := hj1.resolve_right hv1
        exact Finset.mem_filter.mpr ⟨heU, u, v, rfl, a, ha, b, j, hj, hus, hor, hu1,
          by simpa only [show (1 : Fin 2) - 1 = 0 from by decide] using hv0⟩
    · left; right
      have hu0 : u ∈ side C j 0 := hj0.resolve_right hv0
      have hv1 : v ∈ side C j 1 := hj1.resolve_left (fun hu1 => hnb ⟨hu0, hu1⟩)
      exact Finset.mem_filter.mpr ⟨heU, u, v, rfl, a, ha, b, j, hj, hus, hor, hu0,
        by simpa only [show (1 : Fin 2) - 0 = 1 from by decide] using hv1⟩
  have h1 : E1.card ≤ 12 * C.size := by convert case1_bound G model hno
  have h20 : E20.card ≤ 43 * C.size := by convert case2_bound G model hno 0
  have h21 : E21.card ≤ 43 * C.size := by convert case2_bound G model hno 1
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard2 := Finset.card_union_le E1 E20
  omega

end PEqualNP.Outside.L_meta_3805

theorem PEqualNP.Outside.L_meta_3805 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∀ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x13 ∈ PEqualNP.TopForm.junk x3 x7, ¬PEqualNP.EdgeOwnership.InCone x2 x7 x11 x13) → {x12 ∈ PEqualNP.TopForm.Ustar x3 x7 | ∃ (x13 : Fin x2) (x14 : Fin x2), x12 = s(x13, x14) ∧ ∃ x15 ∈ PEqualNP.TopForm.tops x3 x7, ∃ (x16 : Fin (2 : ℕ)), ∃ x17 ∈ PEqualNP.TopForm.junk x3 x7, x13 ∈ PEqualNP.TopForm.side x7 x15 x16 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x15 ((1 : Fin (2 : ℕ)) - x16)) x17 ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x17 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true}.card ≤ x1 * (x7.size + (1 : ℕ)) :=
  PEqualNP.Outside.L_meta_3805.main_bound
