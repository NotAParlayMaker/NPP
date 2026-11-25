import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9004

open PEqualNP.CircuitLowerBounds

theorem getD_snoc_congr (w1 w2 : List Bool) (v : Bool) (i : ℕ) (hlen : w1.length = w2.length)
    (h : w1.getD i false = w2.getD i false) :
    (w1 ++ [v]).getD i false = (w2 ++ [v]).getD i false := by
  simp only [List.getD_eq_getElem?_getD] at h ⊢
  by_cases hi : i < w1.length
  · rw [List.getElem?_append_left hi, List.getElem?_append_left (by omega)]
    exact h
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hlen]

theorem getD_snoc_true (w : List Bool) (v : Bool) (i : ℕ) (h : w.getD i false = true) :
    (w ++ [v]).getD i false = true := by
  simp only [List.getD_eq_getElem?_getD] at h ⊢
  by_cases hi : i < w.length
  · rw [List.getElem?_append_left hi]
    exact h
  · rw [List.getElem?_eq_none (by omega)] at h
    simp at h

theorem getD_ofFn' {n : ℕ} (z : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn z).getD i false = z ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h, Option.getD_some]

theorem getD_ofFn_ge {n : ℕ} (z : Fin n → Bool) (i : ℕ) (h : n ≤ i) :
    (List.ofFn z).getD i false = false := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [List.length_ofFn]; exact h), Option.getD_none]

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp only [List.length_append, List.length_singleton]; omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi]

theorem gate_agree (p q r : ℕ) (g : Gate) (w1 w2 : List Bool)
    (hF : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hH : p ∈ List.take (bif g.op.eval [false] then 1 else 2) g.inputs →
       g.op = GateOp.or ∧ (g.inputs.Perm [p, q] ∨ g.inputs.Perm [p, r]))
    (hag : ∀ i, i ≠ p → w1.getD i false = w2.getD i false)
    (h1q : w1.getD q false = true) (h1r : w1.getD r false = true)
    (h2q : w2.getD q false = true) (h2r : w2.getD r false = true) :
    g.op.eval (g.inputs.map fun i => w1.getD i false)
      = g.op.eval (g.inputs.map fun i => w2.getD i false) := by
  obtain ⟨hop, hlen⟩ := hF
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  by_cases hp : p ∈ List.take (bif g.op.eval [false] then 1 else 2) g.inputs
  · obtain ⟨hor, hperm⟩ := hH hp
    have hT : ∀ w : List Bool, w.getD q false = true → w.getD r false = true →
        g.op.eval (g.inputs.map fun i => w.getD i false) = true := by
      intro w hq hr
      rw [hor]
      show (g.inputs.map fun i => w.getD i false).any id = true
      rw [List.any_eq_true]
      rcases hperm with h | h
      · exact ⟨w.getD q false, List.mem_map.mpr ⟨q, h.mem_iff.mpr (by simp), rfl⟩, hq⟩
      · exact ⟨w.getD r false, List.mem_map.mpr ⟨r, h.mem_iff.mpr (by simp), rfl⟩, hr⟩
    rw [hT w1 h1q h1r, hT w2 h2q h2r]
  · rcases hop with hop | hop | hop
    · rw [hop] at hp ⊢
      have hp' : p ∉ g.inputs := by
        have h2 : List.take 2 g.inputs = g.inputs := List.take_of_length_le hlen
        rw [← h2]
        exact hp
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (fun h => hp' (by rw [← h]; exact hi))
    · rw [hop] at hp ⊢
      have hp' : p ∉ g.inputs := by
        have h2 : List.take 2 g.inputs = g.inputs := List.take_of_length_le hlen
        rw [← h2]
        exact hp
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (fun h => hp' (by rw [← h]; exact hi))
    · rw [hop] at hp ⊢
      show (!((g.inputs.map fun i => w1.getD i false).headD false))
        = (!((g.inputs.map fun i => w2.getD i false).headD false))
      cases hin : g.inputs with
      | nil => rfl
      | cons a rest =>
        rw [hin] at hp
        have hap : a ≠ p := by
          intro h
          apply hp
          rw [h]
          show p ∈ List.take 1 (p :: rest)
          simp
        show (!(w1.getD a false)) = (!(w2.getD a false))
        rw [hag a hap]

theorem fold_agree (p q r : ℕ) : ∀ (gs : List Gate) (w1 w2 : List Bool),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ g ∈ gs, p ∈ List.take (bif g.op.eval [false] then 1 else 2) g.inputs →
       g.op = GateOp.or ∧ (g.inputs.Perm [p, q] ∨ g.inputs.Perm [p, r])) →
    w1.length = w2.length →
    (∀ i, i ≠ p → w1.getD i false = w2.getD i false) →
    w1.getD q false = true → w1.getD r false = true →
    w2.getD q false = true → w2.getD r false = true →
    ∀ i, i ≠ p →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD i false
       = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro w1 w2 _ _ _ hag _ _ _ _ i hi
    exact hag i hi
  | cons g gs ih =>
    intro w1 w2 hF hH hlen hag h1q h1r h2q h2r
    have hv := gate_agree p q r g w1 w2 (hF g List.mem_cons_self) (hH g List.mem_cons_self)
      hag h1q h1r h2q h2r
    simp only [List.foldl_cons]
    rw [hv]
    refine ih (w1 ++ [_]) (w2 ++ [_]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro g' hg'
      exact hF g' (List.mem_cons_of_mem _ hg')
    · intro g' hg'
      exact hH g' (List.mem_cons_of_mem _ hg')
    · simp only [List.length_append, List.length_singleton, hlen]
    · intro i hi
      exact getD_snoc_congr w1 w2 _ i hlen (hag i hi)
    · exact getD_snoc_true _ _ _ h1q
    · exact getD_snoc_true _ _ _ h1r
    · exact getD_snoc_true _ _ _ h2q
    · exact getD_snoc_true _ _ _ h2r

theorem no_four_cycle {V : Type} (G : SimpleGraph V)
    (hg : ∀ (x : V) (w : G.Walk x x), w.IsCycle → 7 ≤ w.length)
    (u v a b : V) (h1 : G.Adj u a) (h2 : G.Adj a v) (h3 : G.Adj v b) (h4 : G.Adj b u)
    (huv : u ≠ v) (hab : a ≠ b) : False := by
  have hua : u ≠ a := h1.ne
  have hav : a ≠ v := h2.ne
  have hvb : v ≠ b := h3.ne
  have hbu : b ≠ u := h4.ne
  have hc : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
      (SimpleGraph.Walk.cons h3 (SimpleGraph.Walk.cons h4 SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    simp [SimpleGraph.Walk.cons_isPath_iff, Sym2.eq_iff, hua, hav, hvb, hbu, huv, hab,
      hua.symm, hav.symm, hvb.symm, hbu.symm, huv.symm, hab.symm]
  have h7 := hg u _ hc
  simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h7
  omega

theorem key_adj {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
    (x6 x7 x8 : Fin n)
    (hA : ∀ u v : Fin n, K.Adj u v → u ∉ A)
    (h7 : x7 ∉ A) (h8 : x8 ∉ A)
    (hins : ∀ z z' : Fin n → Bool, (∀ i, i ≠ x6 → z i = z' i) → z x7 = true → z x8 = true →
      PEqualNP.MetaComplexity.NestedCover.graphFun K A z
        = PEqualNP.MetaComplexity.NestedCover.graphFun K A z')
    (hna : ¬ K.Adj x7 x8) (a : Fin n) (ha : K.Adj x6 a) : K.Adj a x7 ∨ K.Adj a x8 := by
  have hz := hins (fun i => decide (i = a ∨ i = x7 ∨ i = x8))
    (fun i => decide (i = x6 ∨ i = a ∨ i = x7 ∨ i = x8))
    (by intro i hi; simp [hi]) (by simp) (by simp)
  have h1 : PEqualNP.MetaComplexity.NestedCover.graphFun K A
      (fun i => decide (i = x6 ∨ i = a ∨ i = x7 ∨ i = x8)) = true := by
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    rw [Bool.or_eq_true]
    right
    rw [decide_eq_true_eq]
    exact ⟨x6, a, ha, by simp, by simp⟩
  rw [h1] at hz
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
    decide_eq_true_eq] at hz
  rcases hz with ⟨t, ht, hzt⟩ | ⟨u, v, huv, hu, hv⟩
  · exfalso
    rcases hzt with hzt | hzt | hzt
    · rw [hzt] at ht
      exact hA _ _ ha.symm ht
    · rw [hzt] at ht
      exact h7 ht
    · rw [hzt] at ht
      exact h8 ht
  · rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv] at huv
    · exact absurd rfl huv.ne
    · exact Or.inl huv
    · exact Or.inr huv
    · exact Or.inl huv.symm
    · exact absurd rfl huv.ne
    · exact absurd huv hna
    · exact Or.inr huv.symm
    · exact absurd huv.symm hna
    · exact absurd rfl huv.ne

theorem graph_part {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
    (x6 x7 x8 : Fin n)
    (hN : (K.neighborSet x6).ncard = 3)
    (hg : ∀ (x : Fin n) (w : K.Walk x x), w.IsCycle → 7 ≤ w.length)
    (hA : ∀ u v : Fin n, K.Adj u v → u ∉ A)
    (h7 : x7 ∉ A) (h8 : x8 ∉ A) (h67 : x6 ≠ x7) (h68 : x6 ≠ x8)
    (hins : ∀ z z' : Fin n → Bool, (∀ i, i ≠ x6 → z i = z' i) → z x7 = true → z x8 = true →
      PEqualNP.MetaComplexity.NestedCover.graphFun K A z
        = PEqualNP.MetaComplexity.NestedCover.graphFun K A z') :
    K.Adj x7 x8 := by
  by_contra hna
  obtain ⟨a, b, c, hab, hac, hbc, hS⟩ := Set.ncard_eq_three.mp hN
  have ha : K.Adj x6 a := by
    have hm : a ∈ K.neighborSet x6 := by rw [hS]; simp
    exact hm
  have hb : K.Adj x6 b := by
    have hm : b ∈ K.neighborSet x6 := by rw [hS]; simp
    exact hm
  have hc : K.Adj x6 c := by
    have hm : c ∈ K.neighborSet x6 := by rw [hS]; simp
    exact hm
  have key := key_adj K A x6 x7 x8 hA h7 h8 hins hna
  have c7 : ∀ s t : Fin n, s ≠ t → K.Adj x6 s → K.Adj x6 t → K.Adj s x7 → K.Adj t x7 → False :=
    fun s t hst h6s h6t hs7 ht7 =>
      no_four_cycle K hg x6 x7 s t h6s hs7 ht7.symm h6t.symm h67 hst
  have c8 : ∀ s t : Fin n, s ≠ t → K.Adj x6 s → K.Adj x6 t → K.Adj s x8 → K.Adj t x8 → False :=
    fun s t hst h6s h6t hs8 ht8 =>
      no_four_cycle K hg x6 x8 s t h6s hs8 ht8.symm h6t.symm h68 hst
  rcases key a ha with a7 | a8 <;> rcases key b hb with b7 | b8 <;>
    rcases key c hc with d7 | d8
  · exact c7 a b hab ha hb a7 b7
  · exact c7 a b hab ha hb a7 b7
  · exact c7 a c hac ha hc a7 d7
  · exact c8 b c hbc hb hc b8 d8
  · exact c7 b c hbc hb hc b7 d7
  · exact c8 a c hac ha hc a8 d8
  · exact c8 a b hab ha hb a8 b8
  · exact c8 a b hab ha hb a8 b8

theorem main (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1))
    (x5 : Circuit) (x6 x7 x8 : Fin x1)
    (hN : (x2.neighborSet x6).ncard = 3)
    (hg : ∀ (x10 : Fin x1) (x11 : x2.Walk x10 x10), x11.IsCycle → 7 ≤ x11.length)
    (hA : ∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∉ x4)
    (h6 : x6 ∉ x4) (h7 : x7 ∉ x4) (h8 : x8 ∉ x4) (h67 : x6 ≠ x7) (h68 : x6 ≠ x8)
    (hF : PEqualNP.MetaComplexity.FanInTwo x5)
    (hfun : PEqualNP.MetaComplexity.circuitFun x1 x5
      = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4)
    (hH : ∀ g ∈ x5.gates, (x6 : ℕ) ∈ List.take (bif g.op.eval [false] then 1 else 2) g.inputs →
      g.op = GateOp.or ∧ (g.inputs.Perm [(x6 : ℕ), (x7 : ℕ)] ∨ g.inputs.Perm [(x6 : ℕ), (x8 : ℕ)])) :
    x2.Adj x7 x8 := by
  by_cases ho : x5.output = (x6 : ℕ)
  · exfalso
    have hc : ∀ z : Fin x1 → Bool, PEqualNP.MetaComplexity.circuitFun x1 x5 z = z x6 := by
      intro z
      show (x5.wires (List.ofFn z)).getD x5.output false = z x6
      rw [ho]
      unfold Circuit.wires
      rw [fold_prefix x5.gates (List.ofFn z) (x6 : ℕ) (by rw [List.length_ofFn]; exact x6.isLt),
        getD_ofFn' z (x6 : ℕ) x6.isLt]
    have h1 : PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (fun i => decide (i = x6))
        = true := by
      rw [← congrFun hfun (fun i => decide (i = x6)), hc]
      simp
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
      decide_eq_true_eq] at h1
    rcases h1 with ⟨t, ht, hte⟩ | ⟨u, v, huv, hu, hv⟩
    · rw [hte] at ht
      exact h6 ht
    · rw [hu, hv] at huv
      exact huv.ne rfl
  · have hins : ∀ z z' : Fin x1 → Bool, (∀ i, i ≠ x6 → z i = z' i) → z x7 = true →
        z x8 = true →
        PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 z
          = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 z' := by
      intro z z' hzz hz7 hz8
      rw [← congrFun hfun z, ← congrFun hfun z']
      show (x5.wires (List.ofFn z)).getD x5.output false
        = (x5.wires (List.ofFn z')).getD x5.output false
      unfold Circuit.wires
      refine fold_agree (x6 : ℕ) (x7 : ℕ) (x8 : ℕ) x5.gates (List.ofFn z) (List.ofFn z')
        hF hH ?_ ?_ ?_ ?_ ?_ ?_ x5.output ho
      · rw [List.length_ofFn, List.length_ofFn]
      · intro i hi
        by_cases hlt : i < x1
        · rw [getD_ofFn' z i hlt, getD_ofFn' z' i hlt]
          exact hzz ⟨i, hlt⟩ (fun h => hi (congrArg Fin.val h))
        · rw [getD_ofFn_ge z i (by omega), getD_ofFn_ge z' i (by omega)]
      · rw [getD_ofFn' z (x7 : ℕ) x7.isLt]
        exact hz7
      · rw [getD_ofFn' z (x8 : ℕ) x8.isLt]
        exact hz8
      · rw [getD_ofFn' z' (x7 : ℕ) x7.isLt]
        exact (hzz x7 (Ne.symm h67)).symm.trans hz7
      · rw [getD_ofFn' z' (x8 : ℕ) x8.isLt]
        exact (hzz x8 (Ne.symm h68)).symm.trans hz8
    exact graph_part x2 x4 x6 x7 x8 hN hg hA h7 h8 h67 h68 hins

end PEqualNP.Outside.L_meta_9004

theorem PEqualNP.Outside.L_meta_9004 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 x8 : Fin x1), (x2.neighborSet x6).ncard = (3 : ℕ) → (∀ (x10 : Fin x1) (x11 : x2.Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) → (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∉ x4) → x6 ∉ x4 → x7 ∉ x4 → x8 ∉ x4 → x6 ≠ x7 → x6 ≠ x8 → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ x19 ∈ x5.gates, ↑x6 ∈ List.take (bif x19.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x19.inputs → x19.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x19.inputs.Perm [↑x6, ↑x7] ∨ x19.inputs.Perm [↑x6, ↑x8])) → x2.Adj x7 x8 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 hN hg hA h6 h7 h8 h67 h68 hF hfun hH
  exact PEqualNP.Outside.L_meta_9004.main x1 x2 x4 x5 x6 x7 x8 hN hg hA h6 h7 h8 h67 h68 hF hfun hH
