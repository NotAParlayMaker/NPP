import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1373_aux

open PEqualNP.CircuitLowerBounds

private def evalWires (gl : List Gate) (x : List Bool) : List Bool :=
  Circuit.wires ⟨gl, 0⟩ x

private lemma evalWires_nil (x : List Bool) : evalWires [] x = x := rfl

private lemma evalWires_append (gl1 gl2 : List Gate) (x : List Bool) :
    evalWires (gl1 ++ gl2) x = evalWires gl2 (evalWires gl1 x) := by
  simp [evalWires, Circuit.wires, List.foldl_append]

private lemma evalWires_cons (g : Gate) (gl : List Gate) (x : List Bool) :
    evalWires (g :: gl) x = evalWires gl (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

private lemma evalWires_length (gl : List Gate) (x : List Bool) :
    (evalWires gl x).length = x.length + gl.length := by
  induction gl generalizing x with
  | nil => simp [evalWires_nil]
  | cons g rest ih =>
    rw [evalWires_cons, ih]
    simp
    omega

private lemma evalWires_prefix_getD (gl1 gl2 : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gl1.length) :
    (evalWires (gl1 ++ gl2) x).getD i false = (evalWires gl1 x).getD i false := by
  rw [evalWires_append]
  have hlen : i < (evalWires gl1 x).length := by
    rw [evalWires_length]
    exact hi
  induction gl2 generalizing gl1 x with
  | nil => rfl
  | cons g rest ih =>
    have hstep : (evalWires [g] (evalWires gl1 x)).getD i false = (evalWires gl1 x).getD i false := by
      simp only [evalWires_cons, evalWires_nil, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
    have hlen' : i < (evalWires (gl1 ++ [g]) x).length := by
      rw [evalWires_length]
      simp
      omega
    have h1 := ih (gl1 ++ [g]) x (by simp; omega) hlen'
    rw [evalWires_append] at h1
    change (evalWires rest (evalWires [g] (evalWires gl1 x))).getD i false = _
    rw [h1, hstep]

private lemma evalWires_gate_getD (gl : List Gate) (j : ℕ) (hj : j < gl.length) (x : List Bool) :
    (evalWires gl x).getD (x.length + j) false =
      (gl[j]).op.eval ((gl[j]).inputs.map fun i => (evalWires (gl.take j) x).getD i false) := by
  have hsplit : gl = gl.take j ++ [gl[j]] ++ gl.drop (j + 1) := by
    have h1 := List.take_append_drop j gl
    have h2 : gl.drop j = gl[j] :: gl.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  conv_lhs => rw [hsplit]
  rw [evalWires_prefix_getD (gl.take j ++ [gl[j]]) (gl.drop (j + 1)) x (x.length + j)]
  · rw [evalWires_append, evalWires_cons, evalWires_nil]
    have hlen : (evalWires (gl.take j) x).length = x.length + j := by
      rw [evalWires_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
    rfl
  · simp only [List.length_append, List.length_take, List.length_singleton]
    omega

private lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hle : ∀ i, l1.getD i false = true → l2.getD i false = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨i, hi, rfl⟩
    have hi1 : i < l1.length := by omega
    have hget1 : l1.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi1]
      exact h1 l1[i] (List.getElem_mem hi1)
    have hget2 := hle i hget1
    rwa [List.getD_eq_getElem _ _ hi] at hget2
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    rcases h1 with ⟨b, hb, rfl⟩
    rcases List.mem_iff_getElem.mp hb with ⟨i, hi, hbi⟩
    have hi2 : i < l2.length := by omega
    have hget1 : l1.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]
      exact hbi
    have hget2 := hle i hget1
    rw [List.getD_eq_getElem _ _ hi2] at hget2
    exact ⟨l2[i], List.getElem_mem hi2, hget2⟩

private lemma evalWires_mono (gl : List Gate)
    (hmono : ∀ g ∈ gl, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hlen : x.length = y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (evalWires gl x).getD i false = true → (evalWires gl y).getD i false = true := by
  induction gl generalizing x y with
  | nil =>
    simpa [evalWires_nil] using hle
  | cons g rest ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hmono g (List.mem_cons_self ..)
    have hrest : ∀ g' ∈ rest, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')
    rw [evalWires_cons, evalWires_cons]
    apply ih hrest
    · simp [hlen]
    · intro i hi
      by_cases hix : i < x.length
      · have hiy : i < y.length := by omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hix] at hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hiy]
        exact hle i (by simpa [List.getD_eq_getElem?_getD] using hi)
      · by_cases hieq : i = x.length
        · subst hieq
          have hgetx : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD x.length false =
              g.op.eval (g.inputs.map fun i => x.getD i false) := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
              List.getElem?_cons_zero, Option.getD_some]
          have hgety : (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD x.length false =
              g.op.eval (g.inputs.map fun i => y.getD i false) := by
            simp only [List.getD_eq_getElem?_getD, hlen, List.getElem?_append_right (le_refl _), Nat.sub_self,
              List.getElem?_cons_zero, Option.getD_some]
          rw [hgetx] at hi
          rw [hgety]
          apply gateOp_eval_mono g.op hg (g.inputs.map fun i => x.getD i false)
            (g.inputs.map fun i => y.getD i false) (by simp)
          · intro j hj
            by_cases hjl : j < g.inputs.length
            · have hjl' : j < (g.inputs.map fun i => x.getD i false).length := by rw [List.length_map]; exact hjl
              have hjl'' : j < (g.inputs.map fun i => y.getD i false).length := by rw [List.length_map]; exact hjl
              rw [List.getD_eq_getElem _ _ hjl', List.getElem_map] at hj
              rw [List.getD_eq_getElem _ _ hjl'', List.getElem_map]
              exact hle g.inputs[j] hj
            · have hge : (g.inputs.map fun i => x.getD i false).length ≤ j := by rw [List.length_map]; omega
              rw [List.getD_eq_default _ _ hge] at hj
              cases hj
          · exact hi
        · have hgt : x.length + 1 ≤ i := by omega
          rw [List.getD_eq_default _ _ (by simp; omega)] at hi
          cases hi

private def shiftWire (k i : ℕ) : ℕ :=
  if i < k then i else i - 1

private def constGate (b : Bool) : Gate :=
  if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩

private def rewriteGate (k : ℕ) (c : Bool) (g : Gate) : Gate :=
  if k ∈ g.inputs then
    match g.op with
    | GateOp.and =>
      if c then ⟨GateOp.and, (g.inputs.filter fun i => decide (i ≠ k)).map (shiftWire k)⟩
      else constGate false
    | GateOp.or =>
      if c then constGate true
      else ⟨GateOp.or, (g.inputs.filter fun i => decide (i ≠ k)).map (shiftWire k)⟩
    | _ => g
  else
    ⟨g.op, g.inputs.map (shiftWire k)⟩

private lemma rewriteGate_mono (k : ℕ) (c : Bool) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((rewriteGate k c g).op = GateOp.and ∨ (rewriteGate k c g).op = GateOp.or) ∧
      (rewriteGate k c g).inputs.length ≤ 2 := by
  unfold rewriteGate
  by_cases hmem : k ∈ g.inputs
  · simp only [hmem, ↓reduceIte]
    rcases hg with ⟨hop, hlen⟩
    rcases hop with hop | hop <;> rw [hop]
    · by_cases hc : c
      · simp only [hc, ↓reduceIte, true_or, true_and, List.length_map]
        exact le_trans (List.length_filter_le _ _) hlen
      · simp [hc, constGate]
    · by_cases hc : c
      · simp [hc, constGate]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, or_true, true_and, List.length_map]
        exact le_trans (List.length_filter_le _ _) hlen
  · simp only [hmem, ↓reduceIte, List.length_map]
    exact hg

private lemma eval_rewriteGate (k : ℕ) (c : Bool) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool)
    (hk : w1.getD k false = c)
    (hagree : ∀ i, i ≠ k → w2.getD (shiftWire k i) false = w1.getD i false) :
    (rewriteGate k c g).op.eval ((rewriteGate k c g).inputs.map fun i => w2.getD i false) =
      g.op.eval (g.inputs.map fun i => w1.getD i false) := by
  unfold rewriteGate
  by_cases hmem : k ∈ g.inputs
  · simp only [hmem, ↓reduceIte]
    rcases hg with hop | hop <;> rw [hop]
    · by_cases hc : c
      · subst hc
        simp only [↓reduceIte, GateOp.eval, List.map_map, Function.comp_def]
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true, id_eq]
        constructor
        · intro h b hb
          rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
          by_cases hik : i = k
          · subst hik; exact hk
          · have hmemf : i ∈ g.inputs.filter (fun i => decide (i ≠ k)) :=
              List.mem_filter.mpr ⟨hi, by simp [hik]⟩
            have h1 := h (w2.getD (shiftWire k i) false) (List.mem_map.mpr ⟨i, hmemf, rfl⟩)
            rwa [hagree i hik] at h1
        · intro h b hb
          rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
          rcases List.mem_filter.mp hi with ⟨hi', hik⟩
          have hik' : i ≠ k := by simpa using hik
          rw [hagree i hik']
          exact h (w1.getD i false) (List.mem_map.mpr ⟨i, hi', rfl⟩)
      · have hcf : c = false := Bool.eq_false_iff.mpr hc
        subst hcf
        simp only [Bool.false_eq_true, ↓reduceIte, constGate, GateOp.eval, List.map_nil, List.any_nil]
        symm
        apply Bool.eq_false_iff.mpr
        intro hall
        simp only [List.all_eq_true, id_eq] at hall
        have hfalse := hall (w1.getD k false) (List.mem_map.mpr ⟨k, hmem, rfl⟩)
        rw [hk] at hfalse
        cases hfalse
    · by_cases hc : c
      · subst hc
        simp only [↓reduceIte, constGate, GateOp.eval, List.map_nil, List.all_nil]
        symm
        simp only [List.any_eq_true, id_eq]
        exact ⟨w1.getD k false, List.mem_map.mpr ⟨k, hmem, rfl⟩, hk⟩
      · have hcf : c = false := Bool.eq_false_iff.mpr hc
        subst hcf
        simp only [Bool.false_eq_true, ↓reduceIte, GateOp.eval, List.map_map, Function.comp_def]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, id_eq]
        constructor
        · rintro ⟨_, hb, htrue⟩
          rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
          rcases List.mem_filter.mp hi with ⟨hi', hik⟩
          have hik' : i ≠ k := by simpa using hik
          rw [hagree i hik'] at htrue
          exact ⟨w1.getD i false, List.mem_map.mpr ⟨i, hi', rfl⟩, htrue⟩
        · rintro ⟨_, hb, htrue⟩
          rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
          by_cases hik : i = k
          · subst hik; rw [hk] at htrue; cases htrue
          · have hmemf : i ∈ g.inputs.filter (fun i => decide (i ≠ k)) :=
              List.mem_filter.mpr ⟨hi, by simp [hik]⟩
            refine ⟨w2.getD (shiftWire k i) false, List.mem_map.mpr ⟨i, hmemf, rfl⟩, ?_⟩
            rwa [hagree i hik]
  · simp only [hmem, ↓reduceIte, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hik : i ≠ k := fun h => hmem (h ▸ hi)
    exact hagree i hik

private lemma evalWires_rewrite_post (k : ℕ) (c : Bool) (post : List Gate)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool)
    (hlen : w1.length = w2.length + 1)
    (hkle : k < w1.length)
    (hk : w1.getD k false = c)
    (hagree : ∀ i, i ≠ k → w2.getD (shiftWire k i) false = w1.getD i false) :
    ∀ i, i ≠ k →
      (evalWires (post.map (rewriteGate k c)) w2).getD (shiftWire k i) false =
        (evalWires post w1).getD i false := by
  induction post generalizing w1 w2 with
  | nil =>
    simpa [evalWires_nil] using hagree
  | cons g rest ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hpost g (List.mem_cons_self ..)
    have hrest : ∀ g' ∈ rest, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hpost g' (List.mem_cons_of_mem _ hg')
    simp only [List.map_cons, evalWires_cons]
    have hval : (rewriteGate k c g).op.eval ((rewriteGate k c g).inputs.map fun i => w2.getD i false) =
        g.op.eval (g.inputs.map fun i => w1.getD i false) :=
      eval_rewriteGate k c g hg w1 w2 hk hagree
    rw [hval]
    set v := g.op.eval (g.inputs.map fun i => w1.getD i false)
    apply ih hrest (w1 ++ [v]) (w2 ++ [v])
    · simp [hlen]
    · simp; omega
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hkle]
      simpa [List.getD_eq_getElem?_getD] using hk
    · intro i hik
      by_cases hi1 : i < w1.length
      · have hi2 : shiftWire k i < w2.length := by
          unfold shiftWire
          split_ifs <;> omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi1, List.getElem?_append_left hi2]
        simpa [List.getD_eq_getElem?_getD] using hagree i hik
      · by_cases hieq : i = w1.length
        · subst hieq
          have hsh : shiftWire k w1.length = w2.length := by
            unfold shiftWire
            rw [if_neg (by omega)]
            omega
          rw [hsh]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
            List.getElem?_cons_zero]
        · have hgt1 : w1.length + 1 ≤ i := by omega
          have hgt2 : w2.length + 1 ≤ shiftWire k i := by
            unfold shiftWire
            rw [if_neg (by omega)]
            omega
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma plane_hit_card_le {q : ℕ}
    (S : Fin (q^2 + q + 1) → Finset (Fin (q^2 + q + 1)))
    (hcard : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1)
    (T : Finset (Fin (q^2 + q + 1))) (hT : T.Nonempty) :
    (Finset.univ.filter (fun i : Fin (q^2 + q + 1) => ¬ Disjoint (S i) T)).card ≤ T.card * q + 1 := by
  let L : Fin (q^2 + q + 1) → Finset (Fin (q^2 + q + 1)) :=
    fun p => Finset.univ.filter (fun i => p ∈ S i)
  have hLcard : ∀ p, (L p).card = q + 1 := hdeg
  rcases hT with ⟨p0, hp0⟩
  have hcover : ∀ p, p ≠ p0 → ∃ i ∈ L p0, p ∈ S i := by
    let U : Finset (Fin (q^2 + q + 1)) := (L p0).biUnion (fun i => (S i).erase p0)
    have hdisj : Set.PairwiseDisjoint (L p0 : Set (Fin (q^2 + q + 1))) (fun i => (S i).erase p0) := by
      intro i hi j hj hij
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hxi hxj
      have hxp0 : x ≠ p0 := (Finset.mem_erase.mp hxi).1
      have hxsi : x ∈ S i := (Finset.mem_erase.mp hxi).2
      have hxsj : x ∈ S j := (Finset.mem_erase.mp hxj).2
      have hp0si : p0 ∈ S i := (Finset.mem_filter.mp hi).2
      have hp0sj : p0 ∈ S j := (Finset.mem_filter.mp hj).2
      have hsub : ({p0, x} : Finset _) ⊆ S i ∩ S j := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hp0si, hp0sj⟩
        · exact Finset.mem_inter.mpr ⟨hxsi, hxsj⟩
      have h2 : 2 ≤ (S i ∩ S j).card := by
        calc 2 = ({p0, x} : Finset _).card := (Finset.card_pair hxp0.symm).symm
          _ ≤ (S i ∩ S j).card := Finset.card_le_card hsub
      have h1 := hinter i j hij
      omega
    have hUcard : U.card = q^2 + q := by
      rw [Finset.card_biUnion hdisj]
      have hsum : ∑ i ∈ L p0, ((S i).erase p0).card = ∑ _i ∈ L p0, q := by
        apply Finset.sum_congr rfl
        intro i hi
        have hp0i : p0 ∈ S i := (Finset.mem_filter.mp hi).2
        rw [Finset.card_erase_of_mem hp0i, hcard i]
        omega
      rw [hsum, Finset.sum_const, smul_eq_mul, hLcard p0]
      ring
    have hUsub : U ⊆ Finset.univ.erase p0 := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨i, _, hxi⟩
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxi).1, Finset.mem_univ x⟩
    have hUeq : U = Finset.univ.erase p0 := by
      apply Finset.eq_of_subset_of_card_le hUsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ p0), Finset.card_univ, Fintype.card_fin, hUcard]
      omega
    intro p hpp0
    have hpU : p ∈ U := by
      rw [hUeq]
      exact Finset.mem_erase.mpr ⟨hpp0, Finset.mem_univ p⟩
    rcases Finset.mem_biUnion.mp hpU with ⟨i, hi, hpi⟩
    exact ⟨i, hi, (Finset.mem_erase.mp hpi).2⟩
  have hsub : Finset.univ.filter (fun i : Fin (q^2 + q + 1) => ¬ Disjoint (S i) T) ⊆
      L p0 ∪ (T.erase p0).biUnion (fun p => L p \ L p0) := by
    intro i hi
    have hnd : ¬ Disjoint (S i) T := (Finset.mem_filter.mp hi).2
    rw [Finset.not_disjoint_iff] at hnd
    rcases hnd with ⟨p, hpi, hpT⟩
    by_cases hi0 : i ∈ L p0
    · exact Finset.mem_union_left _ hi0
    · apply Finset.mem_union_right
      have hpp0 : p ≠ p0 := by
        rintro rfl
        exact hi0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi⟩)
      refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_erase.mpr ⟨hpp0, hpT⟩, ?_⟩
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi⟩, hi0⟩
  calc (Finset.univ.filter (fun i : Fin (q^2 + q + 1) => ¬ Disjoint (S i) T)).card
      ≤ (L p0 ∪ (T.erase p0).biUnion (fun p => L p \ L p0)).card := Finset.card_le_card hsub
    _ ≤ (L p0).card + ((T.erase p0).biUnion (fun p => L p \ L p0)).card := Finset.card_union_le _ _
    _ ≤ (L p0).card + ∑ p ∈ T.erase p0, (L p \ L p0).card := by
        gcongr
        exact Finset.card_biUnion_le
    _ ≤ (q + 1) + ∑ _p ∈ T.erase p0, q := by
        rw [hLcard p0]
        gcongr with p hp
        have hpp0 : p ≠ p0 := (Finset.mem_erase.mp hp).1
        rcases hcover p hpp0 with ⟨i, hi0, hpi⟩
        have himem : i ∈ L p ∩ L p0 :=
          Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi⟩, hi0⟩
        have hinter_pos : 1 ≤ (L p ∩ L p0).card := Finset.card_pos.mpr ⟨i, himem⟩
        have hsdiff := Finset.card_sdiff_add_card_inter (L p) (L p0)
        rw [hLcard p] at hsdiff
        omega
    _ = (q + 1) + (T.card - 1) * q := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hp0]
    _ = T.card * q + 1 := by
        have hTpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨p0, hp0⟩
        zify [hTpos]
        ring

private lemma arith_no_not {q L : ℕ} (hq : 2 ≤ q) (hL : (q^2 + q + 1) * q ≤ L) :
    ∃ w : ℕ, 1 ≤ w ∧ 1 + max ((q^2 + q + 1) * min (w - 1) q) (q * ((q^2 + q + 1) - (w * q + 1))) ≤ L := by
  refine ⟨q, by omega, ?_⟩
  have hmin : min (q - 1) q = q - 1 := Nat.min_eq_left (by omega)
  have hsub : q^2 + q + 1 - (q * q + 1) = q := by
    have : q^2 = q * q := sq q
    omega
  rw [hmin, hsub]
  have h1 : 1 + (q^2 + q + 1) * (q - 1) ≤ (q^2 + q + 1) * q := by
    have hmul : (q^2 + q + 1) * (q - 1) + (q^2 + q + 1) = (q^2 + q + 1) * q := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    omega
  have h2 : 1 + q * q ≤ (q^2 + q + 1) * q := by
    nlinarith
  have hmax : 1 + max ((q^2 + q + 1) * (q - 1)) (q * q) ≤ (q^2 + q + 1) * q := by
    rcases le_total ((q^2 + q + 1) * (q - 1)) (q * q) with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1
  exact le_trans hmax hL

end PEqualNP.Outside.L_meta_1373_aux

theorem PEqualNP.Outside.L_meta_1373 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (q : ℕ) (S : Fin (q^2+q+1) → Finset (Fin (q^2+q+1))) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q^2+q+1) → ℕ), 2 ≤ q → (∀ i, (S i).card = q + 1) → (∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ (w : Fin (q^2+q+1)) (x : Fin (q^2+q+1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → ∃ w : ℕ, 1 ≤ w ∧ 1 + max ((q^2+q+1) * min (w - 1) q) (q * ((q^2+q+1) - (w * q + 1))) ≤ gates.length := by
  intro h_lb h_simp q S gates out hq hcard hinter hdeg hgates hone_not heval
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1373_aux in
  let N := q^2 + q + 1
  have hSge2 : ∀ i : Fin N, 2 ≤ (S i).card := fun i => by rw [hcard i]; omega
  by_cases hnot : ∃ t : Fin gates.length, (gates.get t).op = GateOp.not
  · rcases hnot with ⟨t, ht⟩
    have hLpos : 1 ≤ gates.length := by have := t.isLt; omega
    let pre := gates.take t.val
    let notG := gates[t.val]
    let post := gates.drop (t.val + 1)
    have hsplit : gates = pre ++ [notG] ++ post := by
      have h1 := List.take_append_drop t.val gates
      have h2 : gates.drop t.val = notG :: post := List.drop_eq_getElem_cons t.isLt
      rw [h2] at h1
      simpa [List.append_assoc, pre, notG, post] using h1.symm
    have hpre_len : pre.length = t.val := by
      simp [pre, List.length_take]
    have hpost_len : post.length = gates.length - (t.val + 1) := by
      simp [post, List.length_drop]
    have hpre_mono : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      rcases List.mem_iff_getElem.mp hg with ⟨i, hi, rfl⟩
      have hi_lt : i < t.val := by rw [hpre_len] at hi; exact hi
      have hget : pre[i] = gates[i]'(Nat.lt_trans hi_lt t.isLt) := List.getElem_take
      rw [hget]
      have hmem : gates[i]'(Nat.lt_trans hi_lt t.isLt) ∈ gates := List.getElem_mem _
      rcases hgates _ hmem with ⟨hop, hlen⟩
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have heq := hone_not ⟨i, Nat.lt_trans hi_lt t.isLt⟩ t (by simpa using h) ht
        have : i = t.val := congrArg Fin.val heq
        omega
    have hpost_mono : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      rcases List.mem_iff_getElem.mp hg with ⟨i, hi, rfl⟩
      have hi_lt : t.val + 1 + i < gates.length := by rw [hpost_len] at hi; omega
      have hget : post[i] = gates[t.val + 1 + i]'hi_lt := List.getElem_drop
      rw [hget]
      have hmem : gates[t.val + 1 + i]'hi_lt ∈ gates := List.getElem_mem _
      rcases hgates _ hmem with ⟨hop, hlen⟩
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have heq := hone_not ⟨t.val + 1 + i, hi_lt⟩ t (by simpa using h) ht
        have : t.val + 1 + i = t.val := congrArg Fin.val heq
        omega
    let phi : (Fin N → Bool) → Bool :=
      fun x => !((evalWires gates (List.ofFn x)).getD (N + t.val) false)
    have hphi_eq : ∀ x : Fin N → Bool,
        phi x = (notG.inputs.map fun i => (evalWires pre (List.ofFn x)).getD i false).headD false := by
      intro x
      dsimp only [phi]
      have hgx := evalWires_gate_getD gates t.val t.isLt (List.ofFn x)
      rw [List.length_ofFn] at hgx
      rw [hgx]
      have hnotop : gates[t.val].op = GateOp.not := by simpa using ht
      rw [hnotop, GateOp.eval, Bool.not_not]
    have hphi_mono : ∀ x y : Fin N → Bool, (∀ p, x p = true → y p = true) → phi x = true → phi y = true := by
      intro x y hxy hx
      rw [hphi_eq] at hx ⊢
      cases hni : notG.inputs with
      | nil => simp [hni] at hx
      | cons a rest =>
        simp only [hni, List.map_cons, List.headD_cons] at hx ⊢
        apply evalWires_mono pre (fun g hg => (hpre_mono g hg).1) (List.ofFn x) (List.ofFn y) (by simp)
        · intro i hi
          by_cases hin : i < N
          · have hi1 : i < (List.ofFn x).length := by rw [List.length_ofFn]; exact hin
            have hi2 : i < (List.ofFn y).length := by rw [List.length_ofFn]; exact hin
            rw [List.getD_eq_getElem _ _ hi1, List.getElem_ofFn] at hi
            rw [List.getD_eq_getElem _ _ hi2, List.getElem_ofFn]
            exact hxy ⟨i, hin⟩ hi
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
            cases hi
        · exact hx
    have hout_ne : ∀ i : Fin N, out i ≠ N + t.val := by
      intro i heq
      have h0 := heval i (fun _ => false)
      have h1 := heval i (fun _ => true)
      have h0f : Circuit.eval ⟨gates, out i⟩ (List.ofFn (fun _ : Fin N => false)) = false := by
        simpa using h0
      have h1t : Circuit.eval ⟨gates, out i⟩ (List.ofFn (fun _ : Fin N => true)) = true := by
        have hne : (S i).Nonempty := Finset.card_pos.mp (by rw [hcard i]; omega)
        rcases hne with ⟨v, hv⟩
        rw [h1]
        exact decide_eq_true ⟨v, hv, rfl⟩
      have hphi0 : phi (fun _ => false) = true := by
        dsimp only [phi]
        rw [← heq]
        change !(Circuit.eval ⟨gates, out i⟩ (List.ofFn (fun _ : Fin N => false))) = true
        rw [h0f]
        rfl
      have hphi1 : phi (fun _ => true) = true := hphi_mono _ _ (fun _ _ => rfl) hphi0
      have h1f : Circuit.eval ⟨gates, out i⟩ (List.ofFn (fun _ : Fin N => true)) = false := by
        have hnot1 : (!(evalWires gates (List.ofFn (fun _ : Fin N => true))).getD (N + t.val) false) = true := hphi1
        have hfalse1 : (evalWires gates (List.ofFn (fun _ : Fin N => true))).getD (N + t.val) false = false := by
          simpa using hnot1
        change (evalWires gates (List.ofFn (fun _ : Fin N => true))).getD (out i) false = false
        rwa [heq]
      rw [h1t] at h1f
      cases h1f
    let delGates : Bool → List Gate := fun c => pre ++ post.map (rewriteGate (N + t.val) c)
    have hdel_len : ∀ c, (delGates c).length = gates.length - 1 := by
      intro c
      simp [delGates, hpre_len, hpost_len]
      omega
    have hdel_mono : ∀ c g, g ∈ delGates c → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro c g hg
      rcases List.mem_append.mp hg with h | h
      · exact hpre_mono g h
      · rcases List.mem_map.mp h with ⟨g0, hg0, rfl⟩
        exact rewriteGate_mono (N + t.val) c g0 (hpost_mono g0 hg0)
    have hdel_eval : ∀ (c : Bool) (x : Fin N → Bool),
        phi x = !c → ∀ i : Fin N,
          Circuit.eval ⟨delGates c, shiftWire (N + t.val) (out i)⟩ (List.ofFn x) =
            Circuit.eval ⟨gates, out i⟩ (List.ofFn x) := by
      intro c x hphix i
      change (evalWires (pre ++ post.map (rewriteGate (N + t.val) c)) (List.ofFn x)).getD
          (shiftWire (N + t.val) (out i)) false =
        (evalWires gates (List.ofFn x)).getD (out i) false
      conv_rhs => rw [hsplit]
      rw [evalWires_append, evalWires_append, evalWires_append]
      set w2 := evalWires pre (List.ofFn x)
      set w1 := evalWires [notG] w2
      have hw2_len : w2.length = N + t.val := by
        simp [w2, evalWires_length, hpre_len, N]
      have hw1_len : w1.length = w2.length + 1 := by
        simp [w1, evalWires_length]
      have hk_val : w1.getD (N + t.val) false = c := by
        have h1 : (evalWires gates (List.ofFn x)).getD (N + t.val) false = c := by
          have hnotx : (!((evalWires gates (List.ofFn x)).getD (N + t.val) false)) = !c := hphix
          exact Bool.not_inj hnotx
        rw [← h1]
        have hpref := evalWires_prefix_getD (pre ++ [notG]) post (List.ofFn x) (N + t.val) (by simp [hpre_len, N])
        rw [← hsplit] at hpref
        rw [hpref, evalWires_append]
      have hagree : ∀ j, j ≠ N + t.val → w2.getD (shiftWire (N + t.val) j) false = w1.getD j false := by
        intro j hjk
        by_cases hjlt : j < N + t.val
        · unfold shiftWire
          rw [if_pos hjlt]
          have hlt2 : j < w2.length := by omega
          simp only [w1, evalWires_cons, evalWires_nil, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
        · have hjgt : N + t.val < j := by omega
          have hge1 : w1.length ≤ j := by omega
          have hge2 : w2.length ≤ shiftWire (N + t.val) j := by
            unfold shiftWire
            rw [if_neg hjlt]
            omega
          rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
      exact evalWires_rewrite_post (N + t.val) c post (fun g hg => (hpost_mono g hg).1)
        w1 w2 hw1_len (by omega) hk_val hagree (out i) (hout_ne i)
    by_cases hconst : phi (fun _ => false) = true ∨ phi (fun _ => true) = false
    · have hconst_val : ∃ c : Bool, ∀ x : Fin N → Bool, phi x = !c := by
        rcases hconst with h0 | h1
        · refine ⟨false, fun x => ?_⟩
          simpa using hphi_mono (fun _ => false) x (fun _ h => by cases h) h0
        · refine ⟨true, fun x => ?_⟩
          apply Bool.eq_false_iff.mpr
          intro hx
          have := hphi_mono x (fun _ => true) (fun _ _ => rfl) hx
          rw [h1] at this
          cases this
      rcases hconst_val with ⟨c, hc⟩
      rcases h_simp N (delGates c) ∅ ∅ (hdel_mono c) with ⟨gates', r, hg'm, hg'len, hg'eval⟩
      have hCeval : ∀ (i : Fin N) (x : Fin N → Bool),
          Circuit.eval ⟨gates', r (shiftWire (N + t.val) (out i))⟩ (List.ofFn x) =
            decide (∃ v ∈ S i, x v = true) := by
        intro i x
        have hnc : ∃ x0 y0 : Fin N → Bool,
            Circuit.eval ⟨delGates c, shiftWire (N + t.val) (out i)⟩
              (List.ofFn (fun j => if j ∈ (∅ : Finset (Fin N)) then true else if j ∈ (∅ : Finset (Fin N)) then false else x0 j)) ≠
            Circuit.eval ⟨delGates c, shiftWire (N + t.val) (out i)⟩
              (List.ofFn (fun j => if j ∈ (∅ : Finset (Fin N)) then true else if j ∈ (∅ : Finset (Fin N)) then false else y0 j)) := by
          refine ⟨fun _ => false, fun _ => true, ?_⟩
          simp only [Finset.notMem_empty, ↓reduceIte]
          rw [hdel_eval c _ (hc _), hdel_eval c _ (hc _), heval, heval]
          have hne : (S i).Nonempty := Finset.card_pos.mp (by rw [hcard i]; omega)
          rcases hne with ⟨v, hv⟩
          simp
          exact ⟨v, hv⟩
        have h1 := hg'eval (shiftWire (N + t.val) (out i)) hnc x
        simp only [Finset.notMem_empty, ↓reduceIte] at h1
        rw [h1, hdel_eval c x (hc x), heval]
      have hlb := h_lb N N q S ⟨gates', 0⟩ (fun i => r (shiftWire (N + t.val) (out i))) (fun _ => q)
        hinter hSge2 hg'm
        (by
          intro i p
          have h := hCeval i (fun q0 => decide (q0 = p))
          change Circuit.eval ⟨gates', r (shiftWire (N + t.val) (out i))⟩
              (List.ofFn (fun q0 => decide (q0 = p))) = true ↔ p ∈ S i
          rw [h]
          simp)
        (by
          intro i x _ hx
          have h := hCeval i x
          change Circuit.eval ⟨gates', r (shiftWire (N + t.val) (out i))⟩ (List.ofFn x) = false
          rw [h]
          apply decide_eq_false
          rintro ⟨v, hv, hvx⟩
          rw [hx v hv] at hvx
          cases hvx)
        (fun _ => le_refl q)
        (fun i => by rw [hcard i])
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Circuit.size] at hlb
      have hNq : N * q ≤ gates.length := le_trans hlb (le_trans hg'len (by rw [hdel_len c]; omega))
      exact arith_no_not hq hNq
    · push_neg at hconst
      rcases hconst with ⟨hphi0_ne, hphi1_ne⟩
      have hphi0 : phi (fun _ => false) = false := Bool.eq_false_iff.mpr hphi0_ne
      have hphi1 : phi (fun _ => true) = true := Bool.eq_true_of_not_eq_false hphi1_ne
      let P : ℕ → Prop := fun k => ∃ y : Fin N → Bool, (Finset.univ.filter (fun p => y p = true)).card = k ∧ phi y = true
      have hPex : ∃ k, P k := ⟨N, fun _ => true, by simp, hphi1⟩
      classical
      let w := Nat.find hPex
      have hwP : P w := Nat.find_spec hPex
      rcases hwP with ⟨y0, hy0_card, hy0_phi⟩
      have hw_min : ∀ x : Fin N → Bool, (Finset.univ.filter (fun p => x p = true)).card < w → phi x = false := by
        intro x hlt
        apply Bool.eq_false_iff.mpr
        intro hx
        exact Nat.find_min hPex hlt ⟨x, rfl, hx⟩
      have hw_pos : 1 ≤ w := by
        by_contra h0
        have hw0 : w = 0 := by omega
        rw [hw0] at hy0_card
        have hy0f : y0 = fun _ => false := by
          funext p
          by_contra hp
          have hpt : y0 p = true := Bool.eq_true_of_not_eq_false hp
          have hmem : p ∈ Finset.univ.filter (fun p => y0 p = true) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpt⟩
          have hpos := Finset.card_pos.mpr ⟨p, hmem⟩
          omega
        rw [hy0f, hphi0] at hy0_phi
        cases hy0_phi
      -- Bound 1: light inputs (weight <= w - 1)
      have hbound1 : 1 + N * min (w - 1) q ≤ gates.length := by
        by_cases hw1 : w = 1
        · rw [hw1]
          simp only [Nat.sub_self, Nat.zero_min, Nat.mul_zero, Nat.add_zero]
          exact hLpos
        · have hw2 : 2 ≤ w := by omega
          rcases h_simp N (delGates true) ∅ ∅ (hdel_mono true) with ⟨gates1, r1, hg1m, hg1len, hg1eval⟩
          have hC1eval : ∀ (i : Fin N) (x : Fin N → Bool),
              (Finset.univ.filter (fun p => x p = true)).card ≤ w - 1 →
              Circuit.eval ⟨gates1, r1 (shiftWire (N + t.val) (out i))⟩ (List.ofFn x) =
                decide (∃ v ∈ S i, x v = true) := by
            intro i x hxw
            have hnc : ∃ x0 y0 : Fin N → Bool,
                Circuit.eval ⟨delGates true, shiftWire (N + t.val) (out i)⟩
                  (List.ofFn (fun j => if j ∈ (∅ : Finset (Fin N)) then true else if j ∈ (∅ : Finset (Fin N)) then false else x0 j)) ≠
                Circuit.eval ⟨delGates true, shiftWire (N + t.val) (out i)⟩
                  (List.ofFn (fun j => if j ∈ (∅ : Finset (Fin N)) then true else if j ∈ (∅ : Finset (Fin N)) then false else y0 j)) := by
              have hne : (S i).Nonempty := Finset.card_pos.mp (by rw [hcard i]; omega)
              rcases hne with ⟨v, hv⟩
              refine ⟨fun _ => false, fun p => decide (p = v), ?_⟩
              simp only [Finset.notMem_empty, ↓reduceIte]
              have hphiv : phi (fun p => decide (p = v)) = false := by
                apply hw_min
                have hfilt : (Finset.univ.filter (fun p : Fin N => decide (p = v) = true)) = {v} := by
                  ext p; simp
                rw [hfilt, Finset.card_singleton]
                omega
              rw [hdel_eval true _ (by simpa using hphi0), hdel_eval true _ (by simpa using hphiv), heval, heval]
              simp [hv]
            have h1 := hg1eval (shiftWire (N + t.val) (out i)) hnc x
            simp only [Finset.notMem_empty, ↓reduceIte] at h1
            have hphix : phi x = false := hw_min x (by omega)
            rw [h1, hdel_eval true x (by simpa using hphix), heval]
          have hlb1 := h_lb N N (w - 1) S ⟨gates1, 0⟩ (fun i => r1 (shiftWire (N + t.val) (out i)))
            (fun _ => min (w - 1) q)
            hinter hSge2 hg1m
            (by
              intro i p
              have hpw : (Finset.univ.filter (fun q0 : Fin N => decide (q0 = p) = true)).card ≤ w - 1 := by
                have hfilt : (Finset.univ.filter (fun q0 : Fin N => decide (q0 = p) = true)) = {p} := by
                  ext q0; simp
                rw [hfilt, Finset.card_singleton]
                omega
              have h := hC1eval i (fun q0 => decide (q0 = p)) hpw
              change Circuit.eval ⟨gates1, r1 (shiftWire (N + t.val) (out i))⟩
                  (List.ofFn (fun q0 => decide (q0 = p))) = true ↔ p ∈ S i
              rw [h]
              simp)
            (by
              intro i x hxw hx
              have h := hC1eval i x hxw
              change Circuit.eval ⟨gates1, r1 (shiftWire (N + t.val) (out i))⟩ (List.ofFn x) = false
              rw [h]
              apply decide_eq_false
              rintro ⟨v, hv, hvx⟩
              rw [hx v hv] at hvx
              cases hvx)
            (fun _ => Nat.min_le_left _ _)
            (fun i => by rw [hcard i]; have := Nat.min_le_right (w - 1) q; omega)
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Circuit.size] at hlb1
          have hle1 : N * min (w - 1) q ≤ gates.length - 1 :=
            le_trans hlb1 (le_trans hg1len (by rw [hdel_len true]))
          omega
      -- Bound 2: heavy inputs (T <= x)
      have hbound2 : 1 + q * (N - (w * q + 1)) ≤ gates.length := by
        let T : Finset (Fin N) := Finset.univ.filter (fun p => y0 p = true)
        have hTcard : T.card = w := hy0_card
        have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
        let M : Finset (Fin N) := Finset.univ.filter (fun i => Disjoint (S i) T)
        have hHit : (Finset.univ.filter (fun i : Fin N => ¬ Disjoint (S i) T)).card ≤ w * q + 1 := by
          rw [← hTcard]
          exact plane_hit_card_le S hcard hinter hdeg T hTne
        have hMcard : N - (w * q + 1) ≤ M.card := by
          have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
            (p := fun i => Disjoint (S i) T)
          simp only [Finset.card_univ, Fintype.card_fin] at hsum
          change M.card + (Finset.univ.filter (fun i : Fin N => ¬ Disjoint (S i) T)).card = N at hsum
          omega
        rcases h_simp N (delGates false) T ∅ (hdel_mono false) with ⟨gates2, r2, hg2m, hg2len, hg2eval⟩
        let e : Fin M.card ≃ M := M.equivFin.symm
        let SM : Fin M.card → Finset (Fin N) := fun j => S (e j).val
        have hC2eval : ∀ (j : Fin M.card) (x : Fin N → Bool),
            Circuit.eval ⟨gates2, r2 (shiftWire (N + t.val) (out (e j).val))⟩ (List.ofFn x) =
              decide (∃ v ∈ SM j, x v = true) := by
          intro j x
          have hdisj : Disjoint (SM j) T := (Finset.mem_filter.mp (e j).property).2
          have hphixT : ∀ z : Fin N → Bool, phi (fun p => if p ∈ T then true else z p) = true := by
            intro z
            apply hphi_mono y0 _ _ hy0_phi
            intro p hp
            have hpT : p ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
            simp [hpT]
          have hnc : ∃ x0 y0' : Fin N → Bool,
              Circuit.eval ⟨delGates false, shiftWire (N + t.val) (out (e j).val)⟩
                (List.ofFn (fun p => if p ∈ T then true else if p ∈ (∅ : Finset (Fin N)) then false else x0 p)) ≠
              Circuit.eval ⟨delGates false, shiftWire (N + t.val) (out (e j).val)⟩
                (List.ofFn (fun p => if p ∈ T then true else if p ∈ (∅ : Finset (Fin N)) then false else y0' p)) := by
            refine ⟨fun _ => false, fun _ => true, ?_⟩
            simp only [Finset.notMem_empty, ↓reduceIte]
            rw [hdel_eval false _ (by simpa using hphixT (fun _ => false)),
                hdel_eval false _ (by simpa using hphixT (fun _ => true)), heval, heval]
            have hne : (SM j).Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
            rcases hne with ⟨v, hv⟩
            have hfalse : decide (∃ u ∈ SM j, (if u ∈ T then true else false) = true) = false := by
              apply decide_eq_false
              rintro ⟨u, hu, huT⟩
              have : u ∈ T := by
                by_contra hnotT
                simp [hnotT] at huT
              exact Finset.disjoint_left.mp hdisj hu this
            have htrue : decide (∃ u ∈ SM j, (if u ∈ T then true else true) = true) = true :=
              decide_eq_true ⟨v, hv, by simp⟩
            change decide (∃ u ∈ SM j, (if u ∈ T then true else false) = true) ≠
              decide (∃ u ∈ SM j, (if u ∈ T then true else true) = true)
            rw [hfalse, htrue]
            decide
          have h1 := hg2eval (shiftWire (N + t.val) (out (e j).val)) hnc x
          simp only [Finset.notMem_empty, ↓reduceIte] at h1
          rw [h1, hdel_eval false _ (by simpa using hphixT x), heval]
          apply decide_eq_decide.mpr
          constructor
          · rintro ⟨v, hv, hvt⟩
            have hvnotT : v ∉ T := Finset.disjoint_left.mp hdisj hv
            simp only [hvnotT, ↓reduceIte] at hvt
            exact ⟨v, hv, hvt⟩
          · rintro ⟨v, hv, hvt⟩
            refine ⟨v, hv, ?_⟩
            have hvnotT : v ∉ T := Finset.disjoint_left.mp hdisj hv
            simp [hvnotT, hvt]
        have hlb2 := h_lb N M.card q SM ⟨gates2, 0⟩
          (fun j => r2 (shiftWire (N + t.val) (out (e j).val))) (fun _ => q)
          (by
            intro i j hij
            apply hinter
            intro heq
            exact hij (e.injective (Subtype.ext heq)))
          (fun j => hSge2 (e j).val)
          hg2m
          (by
            intro j p
            have h := hC2eval j (fun q0 => decide (q0 = p))
            change Circuit.eval ⟨gates2, r2 (shiftWire (N + t.val) (out (e j).val))⟩
                (List.ofFn (fun q0 => decide (q0 = p))) = true ↔ p ∈ SM j
            rw [h]
            simp)
          (by
            intro j x _ hx
            have h := hC2eval j x
            change Circuit.eval ⟨gates2, r2 (shiftWire (N + t.val) (out (e j).val))⟩ (List.ofFn x) = false
            rw [h]
            apply decide_eq_false
            rintro ⟨v, hv, hvx⟩
            rw [hx v hv] at hvx
            cases hvx)
          (fun _ => le_refl q)
          (fun j => by dsimp only [SM]; rw [hcard])
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Circuit.size] at hlb2
        have hle2 : q * (N - (w * q + 1)) ≤ gates.length - 1 := by
          calc q * (N - (w * q + 1)) ≤ q * M.card := Nat.mul_le_mul_left q hMcard
            _ = M.card * q := Nat.mul_comm _ _
            _ ≤ gates2.length := hlb2
            _ ≤ (delGates false).length := hg2len
            _ = gates.length - 1 := hdel_len false
        omega
      refine ⟨w, hw_pos, ?_⟩
      rcases le_total (N * min (w - 1) q) (q * (N - (w * q + 1))) with h | h
      · rw [max_eq_right h]; exact hbound2
      · rw [max_eq_left h]; exact hbound1
  · -- No NOT gate in gates
    have hgates_mono : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      rcases hgates g hg with ⟨hop, hlen⟩
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        rcases List.mem_iff_getElem.mp hg with ⟨i, hi, rfl⟩
        exact hnot ⟨⟨i, hi⟩, by simpa using h⟩
    rcases h_simp N gates ∅ ∅ hgates_mono with ⟨gates', r, hg'm, hg'len, hg'eval⟩
    have hCeval : ∀ (i : Fin N) (x : Fin N → Bool),
        Circuit.eval ⟨gates', r (out i)⟩ (List.ofFn x) = decide (∃ v ∈ S i, x v = true) := by
      intro i x
      have hnc : ∃ x0 y0 : Fin N → Bool,
          Circuit.eval ⟨gates, out i⟩
            (List.ofFn (fun j => if j ∈ (∅ : Finset (Fin N)) then true else if j ∈ (∅ : Finset (Fin N)) then false else x0 j)) ≠
          Circuit.eval ⟨gates, out i⟩
            (List.ofFn (fun j => if j ∈ (∅ : Finset (Fin N)) then true else if j ∈ (∅ : Finset (Fin N)) then false else y0 j)) := by
        refine ⟨fun _ => false, fun _ => true, ?_⟩
        simp only [Finset.notMem_empty, ↓reduceIte]
        rw [heval, heval]
        have hne : (S i).Nonempty := Finset.card_pos.mp (by rw [hcard i]; omega)
        rcases hne with ⟨v, hv⟩
        simp
        exact ⟨v, hv⟩
      have h1 := hg'eval (out i) hnc x
      simp only [Finset.notMem_empty, ↓reduceIte] at h1
      rw [h1, heval]
    have hlb := h_lb N N q S ⟨gates', 0⟩ (fun i => r (out i)) (fun _ => q)
      hinter hSge2 hg'm
      (by
        intro i p
        have h := hCeval i (fun q0 => decide (q0 = p))
        change Circuit.eval ⟨gates', r (out i)⟩ (List.ofFn (fun q0 => decide (q0 = p))) = true ↔ p ∈ S i
        rw [h]
        simp)
      (by
        intro i x _ hx
        have h := hCeval i x
        change Circuit.eval ⟨gates', r (out i)⟩ (List.ofFn x) = false
        rw [h]
        apply decide_eq_false
        rintro ⟨v, hv, hvx⟩
        rw [hx v hv] at hvx
        cases hvx)
      (fun _ => le_refl q)
      (fun i => by rw [hcard i])
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Circuit.size] at hlb
    exact arith_no_not hq (le_trans hlb hg'len)
