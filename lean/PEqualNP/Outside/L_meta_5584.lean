import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5584

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def targetA (u v : Fin 4) : Bool := (4815 : ℕ).testBit (4 * u.val + v.val)

def witC : Circuit :=
  { gates :=
      [ { op := GateOp.or,  inputs := [6, 7] }
      , { op := GateOp.and, inputs := [1, 8] }
      , { op := GateOp.and, inputs := [2, 5] }
      , { op := GateOp.and, inputs := [3, 4] }
      , { op := GateOp.or,  inputs := [0, 9] }
      , { op := GateOp.or,  inputs := [10, 11] }
      , { op := GateOp.or,  inputs := [12, 13] } ]
  , output := 14 }

lemma upper_proof : RepSizeAtMost targetA 7 := by
  refine ⟨witC, ?_, by decide, by decide⟩
  intro g hg
  simp only [witC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def wstep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

lemma wfold_len (gs : List Gate) (xs : List Bool) :
    (gs.foldl wstep xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons, ih, wstep, List.length_append, List.length_nil]
    omega

lemma wfold_prefix (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (gs.foldl wstep xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hlen : i < (wstep xs g).length := by simp [wstep]; omega
    rw [ih (wstep xs g) hlen, List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ hi]
    simp [wstep, List.getElem_append_left hi]

lemma wfold_gate (gs : List Gate) (xs : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl wstep xs).getD (xs.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => (gs.take j |>.foldl wstep xs).getD i false) := by
  induction gs generalizing xs j with
  | nil => simp at hj
  | cons g rest ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, Nat.add_zero, List.getElem_cons_zero, List.take_zero, List.foldl_nil]
      have hlt : xs.length < (wstep xs g).length := by simp [wstep]
      rw [wfold_prefix rest (wstep xs g) xs.length hlt, List.getD_eq_getElem _ _ hlt]
      simp [wstep]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ, List.take_succ_cons]
      have hlen : (wstep xs g).length = xs.length + 1 := by simp [wstep]
      have hj' : j' < rest.length := by simp at hj; omega
      have := ih (wstep xs g) j' hj'
      rw [hlen] at this
      simpa [Nat.add_assoc, Nat.add_comm 1 j'] using this

lemma eval_mono_op (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ (l1 l2 : List Bool), l1.length = l2.length →
      (∀ i < l1.length, l1[i]! = true → l2[i]! = true) →
      op.eval l1 = true → op.eval l2 = true := by
  intro l1 l2 hlen hle h1
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi1 : i < l1.length := by omega
    have h1i : l1[i]'hi1 = true := h1 _ (List.getElem_mem hi1)
    have h2i := hle i hi1 (by simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1] using h1i)
    simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h2i
  · simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    obtain ⟨x, hx, rfl⟩ := h1
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    have hi2 : i < l2.length := by omega
    have h2i := hle i hi (by simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hix)
    exact ⟨l2[i]'hi2, List.getElem_mem hi2, by simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi2] using h2i⟩

lemma wires_mono (gs : List Gate) (hM : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (hlen : xs.length = ys.length)
    (hle : ∀ i, xs.getD i false = true → ys.getD i false = true) :
    ∀ i, (gs.foldl wstep xs).getD i false = true → (gs.foldl wstep ys).getD i false = true := by
  induction gs generalizing xs ys with
  | nil => exact hle
  | cons g rest ih =>
    simp only [List.foldl_cons]
    refine ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (wstep xs g) (wstep ys g)
      (by simp [wstep, hlen]) ?_
    intro i hi
    by_cases hlt : i < xs.length
    · have h1 : (wstep xs g).getD i false = xs.getD i false := by
        rw [List.getD_eq_getElem _ _ (by simp [wstep]; omega), List.getD_eq_getElem _ _ hlt]
        simp [wstep, List.getElem_append_left hlt]
      have h2 : (wstep ys g).getD i false = ys.getD i false := by
        rw [List.getD_eq_getElem _ _ (by simp [wstep]; omega), List.getD_eq_getElem _ _ (by omega)]
        simp [wstep, List.getElem_append_left (by omega : i < ys.length)]
      rw [h1] at hi; rw [h2]; exact hle i hi
    · by_cases heq : i = xs.length
      · subst heq
        have h1 : (wstep xs g).getD xs.length false = g.op.eval (g.inputs.map fun k => xs.getD k false) := by
          rw [List.getD_eq_getElem _ _ (by simp [wstep])]; simp [wstep]
        have h2 : (wstep ys g).getD xs.length false = g.op.eval (g.inputs.map fun k => ys.getD k false) := by
          rw [hlen, List.getD_eq_getElem _ _ (by simp [wstep])]; simp [wstep]
        rw [h1] at hi; rw [h2]
        refine eval_mono_op g.op (hM g List.mem_cons_self) _ _ (by simp) ?_ hi
        intro k hk
        simp only [List.length_map] at hk
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; exact hk : k < (g.inputs.map _).length), List.getElem_map, Option.getD_some]
        exact hle _
      · have hge : (wstep xs g).length ≤ i := by simp [wstep]; omega
        rw [List.getD_eq_default _ _ hge] at hi; cases hi

def gateIns (gs : List Gate) (w : ℕ) : Finset ℕ :=
  if 8 ≤ w then
    match gs[w - 8]? with
    | some g => (g.inputs.filter fun i => decide (i < w)).toFinset
    | none => ∅
  else ∅

def stepReach (gs : List Gate) (S : Finset ℕ) : Finset ℕ :=
  S ∪ S.biUnion (gateIns gs)

def reachN (gs : List Gate) (out : ℕ) : ℕ → Finset ℕ
  | 0 => {out}
  | n + 1 => stepReach gs (reachN gs out n)

lemma reachN_sub (gs : List Gate) (out n : ℕ) : reachN gs out n ⊆ reachN gs out (n + 1) :=
  Finset.subset_union_left

lemma reachN_mono (gs : List Gate) (out : ℕ) {a b : ℕ} (h : a ≤ b) :
    reachN gs out a ⊆ reachN gs out b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha; exact Finset.Subset.refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · exact (ih hab).trans (reachN_sub gs out b)
    · have ha : a = b + 1 := by omega
      subst ha; exact Finset.Subset.refl _

lemma out_mem_reachN (gs : List Gate) (out n : ℕ) : out ∈ reachN gs out n :=
  reachN_mono gs out (Nat.zero_le n) (by simp [reachN])

lemma gateIns_lt (gs : List Gate) (w i : ℕ) (hi : i ∈ gateIns gs w) : i < w := by
  unfold gateIns at hi
  split_ifs at hi with h8
  · cases hg : gs[w - 8]? with
    | none => rw [hg] at hi; cases hi
    | some g =>
      rw [hg] at hi
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hi
      exact hi.2
  · cases hi

lemma gateIns_sub_gt (gs : List Gate) (w i : ℕ) (hi : i ∈ gateIns gs w) : 8 ≤ w ∧ w < 8 + gs.length := by
  unfold gateIns at hi
  split_ifs at hi with h8
  · cases hg : gs[w - 8]? with
    | none => rw [hg] at hi; cases hi
    | some g =>
      have hlt : w - 8 < gs.length := by
        by_contra hge
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hg; cases hg
      omega
  · cases hi

lemma reachN_le_out (gs : List Gate) (out n w : ℕ) (hw : w ∈ reachN gs out n) : w ≤ out := by
  induction n generalizing w with
  | zero => simp [reachN] at hw; omega
  | succ n ih =>
    simp only [reachN, stepReach, Finset.mem_union, Finset.mem_biUnion] at hw
    rcases hw with h | ⟨u, hu, hiu⟩
    · exact ih w h
    · exact le_trans (Nat.le_of_lt (gateIns_lt gs u w hiu)) (ih u hu)

lemma reachN_gate_dist (gs : List Gate) (out n w : ℕ) (hw : w ∈ reachN gs out n)
    (h8 : 8 ≤ w) (hlt : w < 8 + gs.length) :
    w ∈ reachN gs out ((8 + gs.length - 1) - w) := by
  induction n generalizing w with
  | zero =>
    simp only [reachN, Finset.mem_singleton] at hw; subst hw
    exact out_mem_reachN gs w _
  | succ n ih =>
    simp only [reachN, stepReach, Finset.mem_union, Finset.mem_biUnion] at hw
    rcases hw with h | ⟨u, hu, hiu⟩
    · exact ih w h h8 hlt
    · have ⟨hu8, hult⟩ := gateIns_sub_gt gs u w hiu
      have hwlt : w < u := gateIns_lt gs u w hiu
      have hu_in : u ∈ reachN gs out ((8 + gs.length - 1) - u) := ih u hu hu8 hult
      have hstep : w ∈ reachN gs out (((8 + gs.length - 1) - u) + 1) :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u, hu_in, hiu⟩)
      exact reachN_mono gs out (by omega) hstep

lemma reachN_closed (gs : List Gate) (out w i : ℕ)
    (hw : w ∈ reachN gs out (gs.length + 1)) (hi : i ∈ gateIns gs w) :
    i ∈ reachN gs out (gs.length + 1) := by
  have ⟨hw8, hwlt⟩ := gateIns_sub_gt gs w i hi
  have hw' : w ∈ reachN gs out ((8 + gs.length - 1) - w) := reachN_gate_dist gs out _ w hw hw8 hwlt
  have hstep : i ∈ reachN gs out (((8 + gs.length - 1) - w) + 1) :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hw', hi⟩)
  exact reachN_mono gs out (by omega) hstep

lemma reachN_erase_sub_biUnion (gs : List Gate) (out n : ℕ) :
    (reachN gs out n).erase out ⊆
      ((reachN gs out n).filter fun w => 8 ≤ w ∧ w < 8 + gs.length).biUnion (gateIns gs) := by
  intro i hi
  rw [Finset.mem_erase] at hi
  obtain ⟨hne, hmem⟩ := hi
  induction n with
  | zero => simp [reachN] at hmem; exact absurd hmem hne
  | succ n ih =>
    simp only [reachN, stepReach, Finset.mem_union, Finset.mem_biUnion] at hmem
    rcases hmem with h | ⟨u, hu, hiu⟩
    · have h1 := ih h
      rw [Finset.mem_biUnion] at h1 ⊢
      obtain ⟨u, hu, hiu⟩ := h1
      rw [Finset.mem_filter] at hu
      exact ⟨u, Finset.mem_filter.mpr ⟨reachN_sub gs out n hu.1, hu.2⟩, hiu⟩
    · have ⟨hu8, hult⟩ := gateIns_sub_gt gs u i hiu
      exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_filter.mpr ⟨reachN_sub gs out n hu, hu8, hult⟩, hiu⟩

lemma wires_agree_on_reach (C : Circuit) (xs ys : List Bool)
    (hxl : xs.length = 8) (hyl : ys.length = 8)
    (hagree : ∀ i < 8, i ∈ reachN C.gates C.output (C.gates.length + 1) →
      xs.getD i false = ys.getD i false) :
    ∀ w, w ∈ reachN C.gates C.output (C.gates.length + 1) →
      (C.wires xs).getD w false = (C.wires ys).getD w false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases h8 : w < 8
    · change (C.gates.foldl wstep xs).getD w false = (C.gates.foldl wstep ys).getD w false
      rw [wfold_prefix _ _ _ (by omega), wfold_prefix _ _ _ (by omega)]
      exact hagree w h8 hw
    · by_cases hlt : w < 8 + C.gates.length
      · have hj : w - 8 < C.gates.length := by omega
        change (C.gates.foldl wstep xs).getD w false = (C.gates.foldl wstep ys).getD w false
        have hwx : w = xs.length + (w - 8) := by omega
        have hwy : w = ys.length + (w - 8) := by omega
        have hx1 := wfold_gate C.gates xs (w - 8) hj
        have hy1 := wfold_gate C.gates ys (w - 8) hj
        rw [← hwx] at hx1; rw [← hwy] at hy1
        rw [hx1, hy1]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hlenx : ((C.gates.take (w - 8)).foldl wstep xs).length = w := by
          rw [wfold_len, hxl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
        have hleny : ((C.gates.take (w - 8)).foldl wstep ys).length = w := by
          rw [wfold_len, hyl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
        by_cases hiw : i < w
        · have hi_ins : i ∈ gateIns C.gates w := by
            unfold gateIns
            rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega : 8 ≤ w)), List.getElem?_eq_getElem hj]
            simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
            exact ⟨hi, hiw⟩
          have hi_reach := reachN_closed C.gates C.output w i hw hi_ins
          have heq := ih i hiw hi_reach
          have hsp : C.gates = C.gates.take (w - 8) ++ C.gates.drop (w - 8) := (List.take_append_drop _ _).symm
          change (C.gates.foldl wstep xs).getD i false = (C.gates.foldl wstep ys).getD i false at heq
          conv at heq => lhs; rw [hsp, List.foldl_append]
          conv at heq => rhs; rw [hsp, List.foldl_append]
          rw [wfold_prefix (C.gates.drop (w - 8)) _ _ (by omega),
              wfold_prefix (C.gates.drop (w - 8)) _ _ (by omega)] at heq
          exact heq
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · change (C.gates.foldl wstep xs).getD w false = (C.gates.foldl wstep ys).getD w false
        rw [List.getD_eq_default _ _ (by rw [wfold_len, hxl]; omega),
            List.getD_eq_default _ _ (by rw [wfold_len, hyl]; omega)]

lemma input_essential (C : Circuit) (hM : Monotone2 C) (hrep : Represents targetA C)
    (i : ℕ) (_hi : i < 8) (u v u' v' : Fin 4)
    (h1 : targetA u v = true) (h0 : targetA u' v' = false)
    (hdom : ∀ j < 8, j ≠ i → (oneEach u v).getD j false = true → (oneEach u' v').getD j false = true) :
    i ∈ reachN C.gates C.output (C.gates.length + 1) := by
  by_contra hni
  let xs := List.ofFn fun j : Fin 8 => if j.val = i then false else (oneEach u v).getD j.val false
  have hagree : ∀ j < 8, j ∈ reachN C.gates C.output (C.gates.length + 1) →
      (oneEach u v).getD j false = xs.getD j false := by
    intro j hj hjr
    have hne : j ≠ i := fun e => hni (e ▸ hjr)
    have hlen : j < xs.length := by simp [xs, hj]
    rw [List.getD_eq_getElem xs false hlen]
    change (oneEach u v).getD j false =
      (List.ofFn fun k : Fin 8 => if k.val = i then false else (oneEach u v).getD k.val false)[j]'(by simp [hj])
    rw [List.getElem_ofFn]
    simp [hne]
  have heq : C.eval (oneEach u v) = C.eval xs :=
    wires_agree_on_reach C (oneEach u v) xs (by simp [oneEach]) (by simp [xs]) hagree C.output
      (out_mem_reachN _ _ _)
  have hxt : C.eval xs = true := by rw [← heq, hrep u v, h1]
  have hle : ∀ j, xs.getD j false = true → (oneEach u' v').getD j false = true := by
    intro j hj
    by_cases hj8 : j < 8
    · have hlen : j < xs.length := by simp [xs, hj8]
      rw [List.getD_eq_getElem xs false hlen] at hj
      change (List.ofFn fun k : Fin 8 => if k.val = i then false else (oneEach u v).getD k.val false)[j]'(by simp [hj8]) = true at hj
      rw [List.getElem_ofFn] at hj
      by_cases hji : j = i
      · simp [hji] at hj
      · simp only [hji, ite_false] at hj
        exact hdom j hj8 hji hj
    · rw [List.getD_eq_default _ _ (by simp [xs]; omega)] at hj; cases hj
  have hyt : C.eval (oneEach u' v') = true :=
    wires_mono C.gates (fun g hg => (hM g hg).1) xs (oneEach u' v') (by simp [xs, oneEach]) hle C.output hxt
  rw [hrep u' v', h0] at hyt; cases hyt

lemma lower_proof : ¬ RepSizeAtMost targetA 6 := by
  rintro ⟨C, hM, hsz, hrep⟩
  let R := reachN C.gates C.output (C.gates.length + 1)
  let U := R.filter fun w => w < 8
  let G := R.filter fun w => 8 ≤ w ∧ w < 8 + C.gates.length
  have hall : Finset.range 8 ⊆ U := by
    intro i hi
    rw [Finset.mem_range] at hi
    refine Finset.mem_filter.mpr ⟨?_, hi⟩
    interval_cases i
    · exact input_essential C hM hrep 0 (by decide) 0 0 2 0 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 1 (by decide) 1 2 2 2 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 2 (by decide) 2 1 3 1 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 3 (by decide) 3 0 2 0 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 4 (by decide) 3 0 3 1 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 5 (by decide) 2 1 2 0 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 6 (by decide) 1 2 1 0 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 7 (by decide) 1 3 1 0 (by decide) (by decide) (by decide)
  have hU8 : 8 ≤ U.card := by simpa using Finset.card_le_card hall
  have hdisj : Disjoint U G := by
    rw [Finset.disjoint_left]
    intro w hwU hwG
    have h1 := (Finset.mem_filter.mp hwU).2
    have h2 := (Finset.mem_filter.mp hwG).2.1
    omega
  have hsubR : U ∪ G ⊆ R := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h <;> exact (Finset.mem_filter.mp h).1
  have hRcard : U.card + G.card ≤ R.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsubR
  have hGcard : G.card ≤ C.gates.length := by
    have hsub : G ⊆ (Finset.range C.gates.length).image (fun j => 8 + j) := by
      intro w hw
      obtain ⟨_, h8, hlt⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_image.mpr ⟨w - 8, Finset.mem_range.mpr (by omega), by omega⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  have herase : (R.erase C.output).card ≤ ∑ w ∈ G, (gateIns C.gates w).card :=
    (Finset.card_le_card (reachN_erase_sub_biUnion C.gates C.output (C.gates.length + 1))).trans
      Finset.card_biUnion_le
  have hsum2 : ∑ w ∈ G, (gateIns C.gates w).card ≤ ∑ _w ∈ G, 2 := by
    apply Finset.sum_le_sum
    intro w hw
    obtain ⟨_, h8, hlt⟩ := Finset.mem_filter.mp hw
    have hj : w - 8 < C.gates.length := by omega
    unfold gateIns
    rw [ite_eq_left_of_eq_true _ _ (eq_true h8), List.getElem?_eq_getElem hj]
    have hlen2 : (C.gates[w - 8]'hj).inputs.length ≤ 2 := (hM _ (List.getElem_mem hj)).2
    exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans hlen2)
  have hout : C.output ∈ R := out_mem_reachN _ _ _
  have hcardE : (R.erase C.output).card + 1 = R.card := Finset.card_erase_add_one hout
  simp only [Finset.sum_const, smul_eq_mul] at hsum2
  change C.gates.length ≤ 6 at hsz
  omega

end PEqualNP.Outside.L_meta_5584

theorem PEqualNP.Outside.L_meta_5584 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4815 : ℕ).testBit (4 * u.val + v.val)) 7 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4815 : ℕ).testBit (4 * u.val + v.val)) 6 :=
  ⟨PEqualNP.Outside.L_meta_5584.upper_proof, PEqualNP.Outside.L_meta_5584.lower_proof⟩
