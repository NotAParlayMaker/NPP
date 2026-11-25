import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6013

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def targetA (u v : Fin 4) : Bool := (4701 : ℕ).testBit (4 * u.val + v.val)

def witC : Circuit :=
  { gates :=
      [ { op := GateOp.or,  inputs := [0, 1] }
      , { op := GateOp.or,  inputs := [8, 3] }
      , { op := GateOp.and, inputs := [9, 4] }
      , { op := GateOp.and, inputs := [8, 6] }
      , { op := GateOp.and, inputs := [0, 7] }
      , { op := GateOp.and, inputs := [2, 5] }
      , { op := GateOp.or,  inputs := [10, 11] }
      , { op := GateOp.or,  inputs := [12, 13] }
      , { op := GateOp.or,  inputs := [14, 15] } ]
  , output := 16 }

lemma upper_proof : RepSizeAtMost targetA 9 := by
  refine ⟨witC, ?_, by decide, by decide⟩
  intro g hg
  simp only [witC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

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

lemma reachN_sub_of_mem (gs : List Gate) (out u : ℕ)
    (hu : u ∈ reachN gs out (gs.length + 1)) (m : ℕ) :
    reachN gs u m ⊆ reachN gs out (gs.length + 1) := by
  induction m with
  | zero =>
    intro x hx; simp [reachN] at hx; subst hx; exact hu
  | succ m ih =>
    intro x hx
    simp only [reachN, stepReach, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with h | ⟨y, hy, hxy⟩
    · exact ih h
    · exact reachN_closed gs out y x (ih hy) hxy

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

lemma wires_agree_on_reach (gs : List Gate) (out : ℕ) (xs ys : List Bool)
    (hxl : xs.length = 8) (hyl : ys.length = 8)
    (hagree : ∀ i < 8, i ∈ reachN gs out (gs.length + 1) →
      xs.getD i false = ys.getD i false) :
    ∀ w, w ∈ reachN gs out (gs.length + 1) →
      (gs.foldl wstep xs).getD w false = (gs.foldl wstep ys).getD w false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases h8 : w < 8
    · rw [wfold_prefix _ _ _ (by omega), wfold_prefix _ _ _ (by omega)]
      exact hagree w h8 hw
    · by_cases hlt : w < 8 + gs.length
      · have hj : w - 8 < gs.length := by omega
        have hwx : w = xs.length + (w - 8) := by omega
        have hwy : w = ys.length + (w - 8) := by omega
        have hx1 := wfold_gate gs xs (w - 8) hj
        have hy1 := wfold_gate gs ys (w - 8) hj
        rw [← hwx] at hx1; rw [← hwy] at hy1
        rw [hx1, hy1]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hlenx : ((gs.take (w - 8)).foldl wstep xs).length = w := by
          rw [wfold_len, hxl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
        have hleny : ((gs.take (w - 8)).foldl wstep ys).length = w := by
          rw [wfold_len, hyl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
        by_cases hiw : i < w
        · have hi_ins : i ∈ gateIns gs w := by
            unfold gateIns
            rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega : 8 ≤ w)), List.getElem?_eq_getElem hj]
            simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
            exact ⟨hi, hiw⟩
          have hi_reach := reachN_closed gs out w i hw hi_ins
          have heq := ih i hiw hi_reach
          have hsp : gs = gs.take (w - 8) ++ gs.drop (w - 8) := (List.take_append_drop _ _).symm
          conv at heq => lhs; rw [hsp, List.foldl_append]
          conv at heq => rhs; rw [hsp, List.foldl_append]
          rw [wfold_prefix (gs.drop (w - 8)) _ _ (by omega),
              wfold_prefix (gs.drop (w - 8)) _ _ (by omega)] at heq
          exact heq
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · rw [List.getD_eq_default _ _ (by rw [wfold_len, hxl]; omega),
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
    wires_agree_on_reach C.gates C.output (oneEach u v) xs (by simp [oneEach]) (by simp [xs]) hagree C.output
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

lemma sum_card_eq_biUnion_add_excess (G : Finset ℕ) (f : ℕ → Finset ℕ) :
    ∑ w ∈ G, (f w).card =
      (G.biUnion f).card + ∑ x ∈ G.biUnion f, ((G.filter fun w => x ∈ f w).card - 1) := by
  have h1 : ∑ w ∈ G, (f w).card = ∑ w ∈ G, ∑ x ∈ G.biUnion f, if x ∈ f w then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.sum_boole]
    have hsub : (G.biUnion f).filter (fun x => x ∈ f w) = f w := by
      ext x; simp only [Finset.mem_filter, Finset.mem_biUnion, and_iff_right_iff_imp]
      intro hx; exact ⟨w, hw, hx⟩
    simp [hsub]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ x ∈ G.biUnion f, (∑ w ∈ G, if x ∈ f w then 1 else 0) =
      1 + ((G.filter fun w => x ∈ f w).card - 1) := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.mp hx
    have hpos : 1 ≤ (G.filter fun w => x ∈ f w).card :=
      Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hxw⟩⟩
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    omega
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  simp

lemma biUnion_disjoint_of_card_eq {G : Finset ℕ} {f : ℕ → Finset ℕ}
    (heq : (G.biUnion f).card = ∑ w ∈ G, (f w).card) :
    ∀ w1 ∈ G, ∀ w2 ∈ G, w1 ≠ w2 → Disjoint (f w1) (f w2) := by
  intro w1 hw1 w2 hw2 hne
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have hex := sum_card_eq_biUnion_add_excess G f
  have hxbi : x ∈ G.biUnion f := Finset.mem_biUnion.mpr ⟨w1, hw1, hx1⟩
  have h2 : 2 ≤ (G.filter fun w => x ∈ f w).card := by
    have hsub : ({w1, w2} : Finset ℕ) ⊆ G.filter fun w => x ∈ f w := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hw1, hx1⟩
      · exact Finset.mem_filter.mpr ⟨hw2, hx2⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at hc; exact hc
  have hge1 : 1 ≤ ∑ y ∈ G.biUnion f, ((G.filter fun w => y ∈ f w).card - 1) := by
    have hle := Finset.single_le_sum (f := fun y => (G.filter fun w => y ∈ f w).card - 1)
      (fun _ _ => Nat.zero_le _) hxbi
    omega
  omega

lemma biUnion_at_most_one_overlap {G : Finset ℕ} {f : ℕ → Finset ℕ}
    (hle : ∑ w ∈ G, (f w).card ≤ (G.biUnion f).card + 1) :
    (∀ w1 ∈ G, ∀ w2 ∈ G, w1 ≠ w2 → Disjoint (f w1) (f w2)) ∨
    (∃ z ∈ G.biUnion f,
      (∃ w1 ∈ G, ∃ w2 ∈ G, w1 ≠ w2 ∧ z ∈ f w1 ∧ z ∈ f w2) ∧
      ∀ w1 ∈ G, ∀ w2 ∈ G, w1 ≠ w2 → ∀ x, x ∈ f w1 → x ∈ f w2 → x = z) := by
  by_cases hd : ∀ w1 ∈ G, ∀ w2 ∈ G, w1 ≠ w2 → Disjoint (f w1) (f w2)
  · exact Or.inl hd
  · right
    have hex : ∃ w1 ∈ G, ∃ w2 ∈ G, w1 ≠ w2 ∧ ∃ z, z ∈ f w1 ∧ z ∈ f w2 := by
      by_contra hnone
      apply hd
      intro w1 hw1 w2 hw2 hne
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      exact hnone ⟨w1, hw1, w2, hw2, hne, z, hz1, hz2⟩
    obtain ⟨w1, hw1, w2, hw2, hne, z, hz1, hz2⟩ := hex
    refine ⟨z, Finset.mem_biUnion.mpr ⟨w1, hw1, hz1⟩, ⟨w1, hw1, w2, hw2, hne, hz1, hz2⟩, ?_⟩
    intro u1 hu1 u2 hu2 hune x hx1 hx2
    by_contra hxz
    have hsum := sum_card_eq_biUnion_add_excess G f
    have hzbi : z ∈ G.biUnion f := Finset.mem_biUnion.mpr ⟨w1, hw1, hz1⟩
    have hxbi : x ∈ G.biUnion f := Finset.mem_biUnion.mpr ⟨u1, hu1, hx1⟩
    have hz2c : 2 ≤ (G.filter fun w => z ∈ f w).card := by
      have hsub : ({w1, w2} : Finset ℕ) ⊆ G.filter fun w => z ∈ f w := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hw1, hz1⟩
        · exact Finset.mem_filter.mpr ⟨hw2, hz2⟩
      have hc := Finset.card_le_card hsub; rw [Finset.card_pair hne] at hc; exact hc
    have hx2c : 2 ≤ (G.filter fun w => x ∈ f w).card := by
      have hsub : ({u1, u2} : Finset ℕ) ⊆ G.filter fun w => x ∈ f w := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hu1, hx1⟩
        · exact Finset.mem_filter.mpr ⟨hu2, hx2⟩
      have hc := Finset.card_le_card hsub; rw [Finset.card_pair hune] at hc; exact hc
    have hpair : ({x, z} : Finset ℕ) ⊆ G.biUnion f := by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> assumption
    have hge2 : ∑ y ∈ ({x, z} : Finset ℕ), ((G.filter fun w => y ∈ f w).card - 1) ≤
        ∑ y ∈ G.biUnion f, ((G.filter fun w => y ∈ f w).card - 1) :=
      Finset.sum_le_sum_of_subset hpair
    rw [Finset.sum_pair hxz] at hge2
    omega

lemma sum_eq_two_mul_imp {G : Finset ℕ} {f : ℕ → ℕ}
    (hle : ∀ w ∈ G, f w ≤ 2) (heq : ∑ w ∈ G, f w = 2 * G.card) :
    ∀ w ∈ G, f w = 2 := by
  intro w hw
  have hsum : ∑ u ∈ G, f u = f w + ∑ u ∈ G.erase w, f u := (Finset.add_sum_erase G f hw).symm
  have hrest : ∑ u ∈ G.erase w, f u ≤ ∑ _u ∈ G.erase w, 2 :=
    Finset.sum_le_sum fun u hu => hle u (Finset.mem_of_mem_erase hu)
  simp only [Finset.sum_const, smul_eq_mul] at hrest
  have hcard : (G.erase w).card + 1 = G.card := Finset.card_erase_add_one hw
  have hw2 := hle w hw
  omega

lemma sum_eq_two_mul_sub_one_imp {G : Finset ℕ} {f : ℕ → ℕ}
    (hle : ∀ w ∈ G, f w ≤ 2) (heq : ∑ w ∈ G, f w = 2 * G.card - 1) :
    ∀ w ∈ G, f w = 1 ∨ f w = 2 := by
  intro w hw
  have hsum : ∑ u ∈ G, f u = f w + ∑ u ∈ G.erase w, f u := (Finset.add_sum_erase G f hw).symm
  have hrest : ∑ u ∈ G.erase w, f u ≤ ∑ _u ∈ G.erase w, 2 :=
    Finset.sum_le_sum fun u hu => hle u (Finset.mem_of_mem_erase hu)
  simp only [Finset.sum_const, smul_eq_mul] at hrest
  have hcard : (G.erase w).card + 1 = G.card := Finset.card_erase_add_one hw
  have hw2 := hle w hw
  omega

lemma gateIns_card_two (C : Circuit) (hM : Monotone2 C) (w : ℕ)
    (h8 : 8 ≤ w) (hlt : w < 8 + C.gates.length) (hcard : (gateIns C.gates w).card = 2) :
    ∃ a b, (C.gates[w - 8]'(by omega)).inputs = [a, b] ∧ a < w ∧ b < w ∧ a ≠ b ∧
      gateIns C.gates w = {a, b} := by
  have hj : w - 8 < C.gates.length := by omega
  obtain ⟨_, hlen⟩ := hM _ (List.getElem_mem hj)
  unfold gateIns at hcard
  rw [ite_eq_left_of_eq_true _ _ (eq_true h8), List.getElem?_eq_getElem hj] at hcard
  dsimp only at hcard
  match hins : (C.gates[w - 8]'hj).inputs with
  | [] => rw [hins] at hcard; simp at hcard
  | [a] =>
    rw [hins] at hcard
    have := (List.toFinset_card_le ([a].filter fun i => decide (i < w))).trans (List.length_filter_le _ _)
    simp only [List.length_singleton] at this; omega
  | [a, b] =>
    rw [hins] at hcard
    have haw : a < w := by
      by_contra hna
      have h1 : ([a, b].filter fun i => decide (i < w)).length ≤ 1 := by
        rw [List.filter_cons_of_neg (by simp [hna])]
        exact List.length_filter_le _ [b]
      have := (List.toFinset_card_le ([a, b].filter fun i => decide (i < w))).trans h1; omega
    have hbw : b < w := by
      by_contra hnb
      have h1 : ([a, b].filter fun i => decide (i < w)).length ≤ 1 := by
        by_cases ha : a < w <;> simp [ha, hnb]
      have := (List.toFinset_card_le ([a, b].filter fun i => decide (i < w))).trans h1; omega
    have hne : a ≠ b := by
      intro hab; subst hab
      simp [haw] at hcard
    refine ⟨a, b, rfl, haw, hbw, hne, ?_⟩
    unfold gateIns
    rw [ite_eq_left_of_eq_true _ _ (eq_true h8), List.getElem?_eq_getElem hj]
    dsimp only
    rw [hins]
    ext x; simp [haw, hbw]
  | _ :: _ :: _ :: _ => rw [hins] at hlen; simp at hlen

lemma gateIns_card_one (C : Circuit) (hM : Monotone2 C) (w : ℕ)
    (h8 : 8 ≤ w) (hlt : w < 8 + C.gates.length) (hcard : (gateIns C.gates w).card = 1) :
    ∃ a, a < w ∧ gateIns C.gates w = {a} ∧
      ((∀ (xs : List Bool), xs.length = 8 →
        (C.gates.foldl wstep xs).getD w false = (C.gates.foldl wstep xs).getD a false) ∨
       (∀ (xs : List Bool), xs.length = 8 →
        (C.gates.foldl wstep xs).getD w false = false)) := by
  have hj : w - 8 < C.gates.length := by omega
  obtain ⟨hop, hlen⟩ := hM _ (List.getElem_mem hj)
  obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp hcard
  have ha_mem : a ∈ gateIns C.gates w := by rw [ha_eq]; simp
  have haw : a < w := gateIns_lt C.gates w a ha_mem
  refine ⟨a, haw, ha_eq, ?_⟩
  have hmem_a : ∀ i ∈ (C.gates[w - 8]'hj).inputs, i < w → i = a := by
    intro i hi hiw
    have : i ∈ gateIns C.gates w := by
      unfold gateIns
      rw [ite_eq_left_of_eq_true _ _ (eq_true h8), List.getElem?_eq_getElem hj]
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨hi, hiw⟩
    rw [ha_eq, Finset.mem_singleton] at this; exact this
  have hop2 : (C.gates[w - 8]'hj).op = GateOp.and ∨ (C.gates[w - 8]'hj).op = GateOp.or := by
    simpa using hop
  have hev_step : ∀ (xs : List Bool), xs.length = 8 →
      (C.gates.foldl wstep xs).getD w false =
        (C.gates[w - 8]'hj).op.eval ((C.gates[w - 8]'hj).inputs.map fun i =>
          if i < w then (C.gates.foldl wstep xs).getD i false else false) := by
    intro xs hxl
    have hwx : w = xs.length + (w - 8) := by omega
    have hw1 := wfold_gate C.gates xs (w - 8) hj
    rw [← hwx] at hw1; rw [hw1]; congr 1
    apply List.map_congr_left
    intro i _
    have hlenT : ((C.gates.take (w - 8)).foldl wstep xs).length = w := by
      rw [wfold_len, hxl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
    have hsp : C.gates = C.gates.take (w - 8) ++ C.gates.drop (w - 8) := (List.take_append_drop _ _).symm
    by_cases hiw : i < w
    · simp only [hiw, ite_true]
      conv_rhs => rw [hsp, List.foldl_append]
      exact (wfold_prefix (C.gates.drop (w - 8)) _ i (by omega)).symm
    · simp only [hiw, ite_false]
      exact List.getD_eq_default _ _ (by omega)
  match hins : (C.gates[w - 8]'hj).inputs with
  | [] =>
    unfold gateIns at ha_eq
    rw [ite_eq_left_of_eq_true _ _ (eq_true h8), List.getElem?_eq_getElem hj] at ha_eq
    dsimp only at ha_eq; rw [hins] at ha_eq; simp at ha_eq
  | [x] =>
    have hxw : x < w := by
      by_contra hnx
      unfold gateIns at ha_eq
      rw [ite_eq_left_of_eq_true _ _ (eq_true h8), List.getElem?_eq_getElem hj] at ha_eq
      dsimp only at ha_eq; rw [hins] at ha_eq; simp [hnx] at ha_eq
    have hxa : x = a := hmem_a x (by rw [hins]; simp) hxw
    subst hxa
    left; intro xs hxl; rw [hev_step xs hxl, hins]
    rcases hop2 with h | h <;> simp [h, GateOp.eval, hxw]
  | [x, y] =>
    by_cases hxw : x < w <;> by_cases hyw : y < w
    · have hxa : x = a := hmem_a x (by rw [hins]; simp) hxw
      have hya : y = a := hmem_a y (by rw [hins]; simp) hyw
      subst hxa; subst hya
      left; intro xs hxl; rw [hev_step xs hxl, hins]
      rcases hop2 with h | h <;> simp [h, GateOp.eval, hxw]
    · have hxa : x = a := hmem_a x (by rw [hins]; simp) hxw
      subst hxa
      rcases hop2 with h | h
      · right; intro xs hxl; rw [hev_step xs hxl, hins]; simp [h, GateOp.eval, hxw, hyw]
      · left; intro xs hxl; rw [hev_step xs hxl, hins]; simp [h, GateOp.eval, hxw, hyw]
    · have hya : y = a := hmem_a y (by rw [hins]; simp) hyw
      subst hya
      rcases hop2 with h | h
      · right; intro xs hxl; rw [hev_step xs hxl, hins]; simp [h, GateOp.eval, hxw, hyw]
      · left; intro xs hxl; rw [hev_step xs hxl, hins]; simp [h, GateOp.eval, hxw, hyw]
    · unfold gateIns at ha_eq
      rw [ite_eq_left_of_eq_true _ _ (eq_true h8), List.getElem?_eq_getElem hj] at ha_eq
      dsimp only at ha_eq; rw [hins] at ha_eq; simp [hxw, hyw] at ha_eq
  | _ :: _ :: _ :: _ => rw [hins] at hlen; simp at hlen

def vecOf (S : Finset ℕ) : List Bool :=
  List.ofFn fun j : Fin 8 => decide (j.val ∈ S)

lemma vecOf_len (S : Finset ℕ) : (vecOf S).length = 8 := by simp [vecOf]

lemma vecOf_getD (S : Finset ℕ) (i : ℕ) (hi : i < 8) :
    (vecOf S).getD i false = decide (i ∈ S) := by
  have hlen : i < (vecOf S).length := by simp [vecOf, hi]
  rw [List.getD_eq_getElem (vecOf S) false hlen]
  change (List.ofFn fun j : Fin 8 => decide (j.val ∈ S))[i]'(by simp [hi]) = _
  rw [List.getElem_ofFn]

lemma vecOf_pair_eq_oneEach (u v : Fin 4) : vecOf {u.val, 4 + v.val} = oneEach u v := by
  revert u v; decide

lemma eval_bin_gate (C : Circuit) (w a b : ℕ) (h8 : 8 ≤ w) (hlt : w < 8 + C.gates.length)
    (hins : (C.gates[w - 8]'(by omega)).inputs = [a, b]) (haw : a < w) (hbw : b < w)
    (xs : List Bool) (hxl : xs.length = 8) :
    (C.gates.foldl wstep xs).getD w false =
      (C.gates[w - 8]'(by omega)).op.eval [(C.gates.foldl wstep xs).getD a false,
        (C.gates.foldl wstep xs).getD b false] := by
  have hj : w - 8 < C.gates.length := by omega
  have hwx : w = xs.length + (w - 8) := by omega
  have hw1 := wfold_gate C.gates xs (w - 8) hj
  rw [← hwx] at hw1
  rw [hw1, hins]
  simp only [List.map]
  have hlen : ((C.gates.take (w - 8)).foldl wstep xs).length = w := by
    rw [wfold_len, hxl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
  have hsp : C.gates = C.gates.take (w - 8) ++ C.gates.drop (w - 8) := (List.take_append_drop _ _).symm
  have ha_eq : (C.gates.foldl wstep xs).getD a false = ((C.gates.take (w - 8)).foldl wstep xs).getD a false := by
    conv_lhs => rw [hsp, List.foldl_append]
    exact wfold_prefix (C.gates.drop (w - 8)) _ a (by omega)
  have hb_eq : (C.gates.foldl wstep xs).getD b false = ((C.gates.take (w - 8)).foldl wstep xs).getD b false := by
    conv_lhs => rw [hsp, List.foldl_append]
    exact wfold_prefix (C.gates.drop (w - 8)) _ b (by omega)
  rw [ha_eq, hb_eq]

lemma eval_empty_false (C : Circuit) (hM : Monotone2 C) (root : ℕ)
    (hRsub : reachN C.gates root (C.gates.length + 1) ⊆
      (reachN C.gates root (C.gates.length + 1)).filter (· < 8) ∪
      (reachN C.gates root (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length))
    (hcard12 : ∀ w ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length),
      (gateIns C.gates w).card = 1 ∨ (gateIns C.gates w).card = 2) :
    ∀ w ∈ reachN C.gates root (C.gates.length + 1),
      (C.gates.foldl wstep (vecOf ∅)).getD w false = false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    rcases Finset.mem_union.mp (hRsub hw) with hwU | hwG
    · have hw8 : w < 8 := (Finset.mem_filter.mp hwU).2
      rw [wfold_prefix _ _ _ (by rw [vecOf_len]; exact hw8), vecOf_getD ∅ w hw8]; simp
    · obtain ⟨_, hw8, hwlt⟩ := Finset.mem_filter.mp hwG
      rcases hcard12 w hwG with hc1 | hc2
      · obtain ⟨a, haw, hgi, hev⟩ := gateIns_card_one C hM w hw8 hwlt hc1
        have haR : a ∈ reachN C.gates root (C.gates.length + 1) :=
          reachN_closed C.gates root w a hw (by rw [hgi]; simp)
        rcases hev with h | h
        · rw [h (vecOf ∅) (vecOf_len ∅)]; exact ih a haw haR
        · exact h (vecOf ∅) (vecOf_len ∅)
      · obtain ⟨a, b, hins, haw, hbw, _, hgi⟩ := gateIns_card_two C hM w hw8 hwlt hc2
        have haR : a ∈ reachN C.gates root (C.gates.length + 1) :=
          reachN_closed C.gates root w a hw (by rw [hgi]; simp)
        have hbR : b ∈ reachN C.gates root (C.gates.length + 1) :=
          reachN_closed C.gates root w b hw (by rw [hgi]; simp)
        rw [eval_bin_gate C w a b hw8 hwlt hins haw hbw (vecOf ∅) (vecOf_len ∅),
            ih a haw haR, ih b hbw hbR]
        rcases (by simpa using (hM _ (List.getElem_mem (by omega : w - 8 < C.gates.length))).1 :
            (C.gates[w - 8]'(by omega)).op = GateOp.and ∨ (C.gates[w - 8]'(by omega)).op = GateOp.or) with hop | hop <;>
          simp [hop, GateOp.eval]

lemma reachN_inter_sub_z (C : Circuit) (root z : ℕ)
    (hunique : ∀ w1 ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length),
      ∀ w2 ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length),
      w1 ≠ w2 → ∀ x, x ∈ gateIns C.gates w1 → x ∈ gateIns C.gates w2 → x = z)
    (w a b : ℕ)
    (hw : w ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length))
    (ha : a ∈ gateIns C.gates w) (hb : b ∈ gateIns C.gates w) (hne : a ≠ b) :
    reachN C.gates a (C.gates.length + 1) ∩ reachN C.gates b (C.gates.length + 1) ⊆
      reachN C.gates z (C.gates.length + 1) := by
  let N := C.gates.length + 1
  let R := reachN C.gates root N
  let G := R.filter fun u => 8 ≤ u ∧ u < 8 + C.gates.length
  have haR : a ∈ R := reachN_closed C.gates root w a (Finset.mem_filter.mp hw).1 ha
  have hbR : b ∈ R := reachN_closed C.gates root w b (Finset.mem_filter.mp hw).1 hb
  have hsubA : reachN C.gates a N ⊆ R := reachN_sub_of_mem C.gates root a haR N
  have hsubB : reachN C.gates b N ⊆ R := reachN_sub_of_mem C.gates root b hbR N
  intro x hx
  by_contra hxz
  let S := (reachN C.gates a N ∩ reachN C.gates b N) \ reachN C.gates z N
  have hS : S.Nonempty := ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxz⟩⟩
  let m := S.max' hS
  have hmS : m ∈ S := Finset.max'_mem S hS
  have ⟨hmAB, hmz⟩ := Finset.mem_sdiff.mp hmS
  have ⟨hma, hmb⟩ := Finset.mem_inter.mp hmAB
  have hm_ne_z : m ≠ z := fun h => hmz (h ▸ out_mem_reachN _ _ _)
  have hma_ne : m ≠ a := by
    intro hmeq
    rw [hmeq] at hmb
    have hab_er : a ∈ (reachN C.gates b N).erase b := Finset.mem_erase.mpr ⟨hne, hmb⟩
    have hbi := reachN_erase_sub_biUnion C.gates b N hab_er
    obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp hbi
    obtain ⟨huB, hu8, hult⟩ := Finset.mem_filter.mp hu
    have huG : u ∈ G := Finset.mem_filter.mpr ⟨hsubB huB, hu8, hult⟩
    have hule : u ≤ b := reachN_le_out C.gates b N u huB
    have hblt : b < w := gateIns_lt C.gates w b hb
    have haz : a = z := hunique w hw u huG (by omega) a ha hau
    exact hm_ne_z (hmeq.trans haz)
  have hmb_ne : m ≠ b := by
    intro hmeq
    rw [hmeq] at hma
    have hba_er : b ∈ (reachN C.gates a N).erase a := Finset.mem_erase.mpr ⟨hne.symm, hma⟩
    have hbi := reachN_erase_sub_biUnion C.gates a N hba_er
    obtain ⟨u, hu, hbu⟩ := Finset.mem_biUnion.mp hbi
    obtain ⟨huA, hu8, hult⟩ := Finset.mem_filter.mp hu
    have huG : u ∈ G := Finset.mem_filter.mpr ⟨hsubA huA, hu8, hult⟩
    have hule : u ≤ a := reachN_le_out C.gates a N u huA
    have halt : a < w := gateIns_lt C.gates w a ha
    have hbz : b = z := hunique w hw u huG (by omega) b hb hbu
    exact hm_ne_z (hmeq.trans hbz)
  have h1 := reachN_erase_sub_biUnion C.gates a N (Finset.mem_erase.mpr ⟨hma_ne, hma⟩)
  have h2 := reachN_erase_sub_biUnion C.gates b N (Finset.mem_erase.mpr ⟨hmb_ne, hmb⟩)
  obtain ⟨u1, hu1, hmu1⟩ := Finset.mem_biUnion.mp h1
  obtain ⟨u2, hu2, hmu2⟩ := Finset.mem_biUnion.mp h2
  obtain ⟨hu1A, hu18, hu1lt⟩ := Finset.mem_filter.mp hu1
  obtain ⟨hu2B, hu28, hu2lt⟩ := Finset.mem_filter.mp hu2
  have hu1G : u1 ∈ G := Finset.mem_filter.mpr ⟨hsubA hu1A, hu18, hu1lt⟩
  have hu2G : u2 ∈ G := Finset.mem_filter.mpr ⟨hsubB hu2B, hu28, hu2lt⟩
  have hu_eq : u1 = u2 := by
    by_contra hune
    exact hm_ne_z (hunique u1 hu1G u2 hu2G hune m hmu1 hmu2)
  subst hu_eq
  have hu1_nz : u1 ∉ reachN C.gates z N := fun huz =>
    hmz (reachN_closed C.gates z u1 m huz hmu1)
  have hu1S : u1 ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hu1A, hu2B⟩, hu1_nz⟩
  have hle : u1 ≤ m := Finset.le_max' S u1 hu1S
  have hlt : m < u1 := gateIns_lt C.gates u1 m hmu1
  omega

lemma dominator_z (C : Circuit) (z : ℕ)
    (hzR : z ∈ reachN C.gates C.output (C.gates.length + 1))
    (hunique : ∀ w1 ∈ (reachN C.gates C.output (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length),
      ∀ w2 ∈ (reachN C.gates C.output (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length),
      w1 ≠ w2 → ∀ x, x ∈ gateIns C.gates w1 → x ∈ gateIns C.gates w2 → x = z)
    (xs ys : List Bool) (hxl : xs.length = 8) (hyl : ys.length = 8)
    (hagree : ∀ i < 8, i ∉ reachN C.gates z (C.gates.length + 1) → xs.getD i false = ys.getD i false)
    (hz_eq : (C.gates.foldl wstep xs).getD z false = (C.gates.foldl wstep ys).getD z false) :
    ∀ w ∈ reachN C.gates C.output (C.gates.length + 1),
      w ∉ (reachN C.gates z (C.gates.length + 1)).erase z →
      (C.gates.foldl wstep xs).getD w false = (C.gates.foldl wstep ys).getD w false := by
  let N := C.gates.length + 1
  let R := reachN C.gates C.output N
  let G := R.filter fun u => 8 ≤ u ∧ u < 8 + C.gates.length
  have hsubZ : reachN C.gates z N ⊆ R := reachN_sub_of_mem C.gates C.output z hzR N
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hw_ne_er
    by_cases hwz : w = z
    · subst hwz; exact hz_eq
    · have hw_nz : w ∉ reachN C.gates z N := fun hz =>
        hw_ne_er (Finset.mem_erase.mpr ⟨hwz, hz⟩)
      by_cases h8 : w < 8
      · rw [wfold_prefix _ _ _ (by omega), wfold_prefix _ _ _ (by omega)]
        exact hagree w h8 hw_nz
      · by_cases hlt : w < 8 + C.gates.length
        · have hj : w - 8 < C.gates.length := by omega
          have hwG : w ∈ G := Finset.mem_filter.mpr ⟨hw, by omega, hlt⟩
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
            have hiR : i ∈ R := reachN_closed C.gates C.output w i hw hi_ins
            have hi_ner : i ∉ (reachN C.gates z N).erase z := by
              intro hier
              have ⟨hiz, _⟩ := Finset.mem_erase.mp hier
              have hbi := reachN_erase_sub_biUnion C.gates z N hier
              obtain ⟨u, hu, hiu⟩ := Finset.mem_biUnion.mp hbi
              obtain ⟨huZ, hu8, hult⟩ := Finset.mem_filter.mp hu
              have huG : u ∈ G := Finset.mem_filter.mpr ⟨hsubZ huZ, hu8, hult⟩
              have hne : w ≠ u := fun e => hw_nz (e ▸ huZ)
              exact hiz (hunique w hwG u huG hne i hi_ins hiu)
            have heq := ih i hiw hiR hi_ner
            have hsp : C.gates = C.gates.take (w - 8) ++ C.gates.drop (w - 8) := (List.take_append_drop _ _).symm
            conv at heq => lhs; rw [hsp, List.foldl_append]
            conv at heq => rhs; rw [hsp, List.foldl_append]
            rw [wfold_prefix (C.gates.drop (w - 8)) _ _ (by omega),
                wfold_prefix (C.gates.drop (w - 8)) _ _ (by omega)] at heq
            exact heq
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by rw [wfold_len, hxl]; omega),
              List.getD_eq_default _ _ (by rw [wfold_len, hyl]; omega)]

lemma no_P4_gen (C : Circuit) (hM : Monotone2 C) (root : ℕ)
    (hRsub : reachN C.gates root (C.gates.length + 1) ⊆
      (reachN C.gates root (C.gates.length + 1)).filter (· < 8) ∪
      (reachN C.gates root (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length))
    (hcard12 : ∀ w ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length),
      (gateIns C.gates w).card = 1 ∨ (gateIns C.gates w).card = 2)
    (p q r t : ℕ)
    (hdisj4 : ∀ w ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length),
      ∀ a b, a ∈ gateIns C.gates w → b ∈ gateIns C.gates w → a ≠ b →
      ∀ x ∈ ({p, q, r, t} : Finset ℕ),
        ¬ (x ∈ reachN C.gates a (C.gates.length + 1) ∧ x ∈ reachN C.gates b (C.gates.length + 1))) :
    ∀ w ∈ reachN C.gates root (C.gates.length + 1),
      (C.gates.foldl wstep (vecOf {p, r})).getD w false = true →
      (C.gates.foldl wstep (vecOf {p, t})).getD w false = true →
      (C.gates.foldl wstep (vecOf {q, r})).getD w false = true →
      (C.gates.foldl wstep (vecOf {q, t})).getD w false = false →
      (C.gates.foldl wstep (vecOf {p})).getD w false = false →
      (C.gates.foldl wstep (vecOf {r})).getD w false = false →
      False := by
  let N := C.gates.length + 1
  have hmonoS : ∀ (S T : Finset ℕ), S ⊆ T → ∀ u,
      (C.gates.foldl wstep (vecOf S)).getD u false = true →
      (C.gates.foldl wstep (vecOf T)).getD u false = true := by
    intro S T hST u hu
    refine wires_mono C.gates (fun g hg => (hM g hg).1) (vecOf S) (vecOf T) (by simp [vecOf_len]) ?_ u hu
    intro i hi
    by_cases hi8 : i < 8
    · rw [vecOf_getD S i hi8] at hi
      rw [vecOf_getD T i hi8]
      simp only [decide_eq_true_eq] at hi ⊢
      exact hST hi
    · rw [List.getD_eq_default _ _ (by rw [vecOf_len]; omega)] at hi; cases hi
  have hagreeW : ∀ u (S T : Finset ℕ),
      (∀ i < 8, i ∈ reachN C.gates u N → (i ∈ S ↔ i ∈ T)) →
      (C.gates.foldl wstep (vecOf S)).getD u false = (C.gates.foldl wstep (vecOf T)).getD u false := by
    intro u S T hST
    refine wires_agree_on_reach C.gates u (vecOf S) (vecOf T) (vecOf_len S) (vecOf_len T) ?_ u (out_mem_reachN _ _ _)
    intro i hi hir
    rw [vecOf_getD S i hi, vecOf_getD T i hi, decide_eq_decide]
    exact hST i hi hir
  have hpair_in : ∀ u x y,
      (C.gates.foldl wstep (vecOf {x, y})).getD u false = true →
      (C.gates.foldl wstep (vecOf {x})).getD u false = false →
      (C.gates.foldl wstep (vecOf {y})).getD u false = false →
      x ∈ reachN C.gates u N ∧ y ∈ reachN C.gates u N := by
    intro u x y hxy hx hy
    constructor
    · by_contra hnx
      have heq := hagreeW u {x, y} {y} fun i _ hir => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl); exact absurd hir hnx; rfl
        · intro h; exact Or.inr h
      rw [heq, hy] at hxy; cases hxy
    · by_contra hny
      have heq := hagreeW u {x, y} {x} fun i _ hir => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl); rfl; exact absurd hir hny
        · intro h; exact Or.inl h
      rw [heq, hx] at hxy; cases hxy
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hpr hpt hqr hqt hp hr
    have hq : (C.gates.foldl wstep (vecOf {q})).getD w false = false := by
      cases hv : (C.gates.foldl wstep (vecOf {q})).getD w false
      · rfl
      · have := hmonoS {q} {q, t} (by simp) w hv; rw [hqt] at this; cases this
    have ht : (C.gates.foldl wstep (vecOf {t})).getD w false = false := by
      cases hv : (C.gates.foldl wstep (vecOf {t})).getD w false
      · rfl
      · have := hmonoS {t} {q, t} (by simp) w hv; rw [hqt] at this; cases this
    rcases Finset.mem_union.mp (hRsub hw) with hwU | hwG
    · have hw8 : w < 8 := (Finset.mem_filter.mp hwU).2
      rw [wfold_prefix _ _ _ (by rw [vecOf_len]; exact hw8), vecOf_getD _ w hw8] at hpr hp hr
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, Finset.mem_insert, Finset.mem_singleton] at hpr hp hr
      rcases hpr with rfl | rfl
      · exact hp rfl
      · exact hr rfl
    · obtain ⟨_, hw8, hwlt⟩ := Finset.mem_filter.mp hwG
      rcases hcard12 w hwG with hc1 | hc2
      · obtain ⟨a, haw, hgi, hev⟩ := gateIns_card_one C hM w hw8 hwlt hc1
        have haR : a ∈ reachN C.gates root N := reachN_closed C.gates root w a hw (by rw [hgi]; simp)
        rcases hev with h | h
        · rw [h (vecOf {p, r}) (vecOf_len _)] at hpr
          rw [h (vecOf {p, t}) (vecOf_len _)] at hpt
          rw [h (vecOf {q, r}) (vecOf_len _)] at hqr
          rw [h (vecOf {q, t}) (vecOf_len _)] at hqt
          rw [h (vecOf {p}) (vecOf_len _)] at hp
          rw [h (vecOf {r}) (vecOf_len _)] at hr
          exact ih a haw haR hpr hpt hqr hqt hp hr
        · rw [h (vecOf {p, r}) (vecOf_len _)] at hpr; cases hpr
      · obtain ⟨a, b, hins, haw, hbw, hab, hgi⟩ := gateIns_card_two C hM w hw8 hwlt hc2
        have ha_ins : a ∈ gateIns C.gates w := by rw [hgi]; simp
        have hb_ins : b ∈ gateIns C.gates w := by rw [hgi]; simp
        have haR : a ∈ reachN C.gates root N := reachN_closed C.gates root w a hw ha_ins
        have hbR : b ∈ reachN C.gates root N := reachN_closed C.gates root w b hw hb_ins
        have hnd : ∀ x ∈ ({p, q, r, t} : Finset ℕ),
            ¬ (x ∈ reachN C.gates a N ∧ x ∈ reachN C.gates b N) :=
          hdisj4 w hwG a b ha_ins hb_ins hab
        have hev := fun S => eval_bin_gate C w a b hw8 hwlt hins haw hbw (vecOf S) (vecOf_len S)
        rcases (by simpa using (hM _ (List.getElem_mem (by omega : w - 8 < C.gates.length))).1 :
            (C.gates[w - 8]'(by omega)).op = GateOp.and ∨ (C.gates[w - 8]'(by omega)).op = GateOp.or) with hop | hop
        · have hand : ∀ S, (C.gates.foldl wstep (vecOf S)).getD w false =
              ((C.gates.foldl wstep (vecOf S)).getD a false && (C.gates.foldl wstep (vecOf S)).getD b false) := by
            intro S; rw [hev S, hop]; simp [GateOp.eval]
          rw [hand] at hpr hpt hqr hqt
          simp only [Bool.and_eq_true] at hpr hpt hqr
          have ha0 := eval_empty_false C hM root hRsub hcard12 a haR
          have hb0 := eval_empty_false C hM root hRsub hcard12 b hbR
          have hit : ∀ u x y, (C.gates.foldl wstep (vecOf ∅)).getD u false = false →
              (C.gates.foldl wstep (vecOf {x, y})).getD u false = true →
              x ∈ reachN C.gates u N ∨ y ∈ reachN C.gates u N := by
            intro u x y hu0 hxy
            by_contra hneither
            have ⟨hnx, hny⟩ := not_or.mp hneither
            have heq := hagreeW u {x, y} ∅ fun i _ hir => by
              simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
              rintro (rfl | rfl)
              · exact hnx hir
              · exact hny hir
            rw [heq, hu0] at hxy; cases hxy
          have h1a := hit a p r ha0 hpr.1
          have h1b := hit b p r hb0 hpr.2
          have h2a := hit a p t ha0 hpt.1
          have h2b := hit b p t hb0 hpt.2
          have h3a := hit a q r ha0 hqr.1
          have h3b := hit b q r hb0 hqr.2
          rcases h1a with hpa | hra
          · have hpb : p ∉ reachN C.gates b N := fun h => hnd p (by simp) ⟨hpa, h⟩
            have hrb : r ∈ reachN C.gates b N := h1b.resolve_left hpb
            have hra' : r ∉ reachN C.gates a N := fun h => hnd r (by simp) ⟨h, hrb⟩
            have htb : t ∈ reachN C.gates b N := h2b.resolve_left hpb
            have hta' : t ∉ reachN C.gates a N := fun h => hnd t (by simp) ⟨h, htb⟩
            have hqa : q ∈ reachN C.gates a N := h3a.resolve_right hra'
            have hqb : q ∉ reachN C.gates b N := fun h => hnd q (by simp) ⟨hqa, h⟩
            have hqta : (C.gates.foldl wstep (vecOf {q, t})).getD a false = true := by
              rw [hagreeW a {q, t} {q, r} fun i _ hir => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (rfl | rfl); exact Or.inl rfl; exact absurd hir hta'
                · rintro (rfl | rfl); exact Or.inl rfl; exact absurd hir hra']
              exact hqr.1
            have hqtb : (C.gates.foldl wstep (vecOf {q, t})).getD b false = true := by
              rw [hagreeW b {q, t} {p, t} fun i _ hir => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (rfl | rfl); exact absurd hir hqb; exact Or.inr rfl
                · rintro (rfl | rfl); exact absurd hir hpb; exact Or.inr rfl]
              exact hpt.2
            rw [hqta, hqtb] at hqt; cases hqt
          · have hrb : r ∉ reachN C.gates b N := fun h => hnd r (by simp) ⟨hra, h⟩
            have hpb : p ∈ reachN C.gates b N := h1b.resolve_right hrb
            have hpa' : p ∉ reachN C.gates a N := fun h => hnd p (by simp) ⟨h, hpb⟩
            have hta : t ∈ reachN C.gates a N := h2a.resolve_left hpa'
            have htb' : t ∉ reachN C.gates b N := fun h => hnd t (by simp) ⟨hta, h⟩
            have hqb : q ∈ reachN C.gates b N := h3b.resolve_right hrb
            have hqa' : q ∉ reachN C.gates a N := fun h => hnd q (by simp) ⟨h, hqb⟩
            have hqta : (C.gates.foldl wstep (vecOf {q, t})).getD a false = true := by
              rw [hagreeW a {q, t} {p, t} fun i _ hir => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (rfl | rfl); exact absurd hir hqa'; exact Or.inr rfl
                · rintro (rfl | rfl); exact absurd hir hpa'; exact Or.inr rfl]
              exact hpt.1
            have hqtb : (C.gates.foldl wstep (vecOf {q, t})).getD b false = true := by
              rw [hagreeW b {q, t} {q, r} fun i _ hir => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (rfl | rfl); exact Or.inl rfl; exact absurd hir htb'
                · rintro (rfl | rfl); exact Or.inl rfl; exact absurd hir hrb]
              exact hqr.2
            rw [hqta, hqtb] at hqt; cases hqt
        · have hor : ∀ S, (C.gates.foldl wstep (vecOf S)).getD w false =
              ((C.gates.foldl wstep (vecOf S)).getD a false || (C.gates.foldl wstep (vecOf S)).getD b false) := by
            intro S; rw [hev S, hop]; simp [GateOp.eval]
          rw [hor] at hpr hpt hqr hqt hp hq hr ht
          simp only [Bool.or_eq_false_iff] at hqt hp hq hr ht
          simp only [Bool.or_eq_true] at hpr hpt hqr
          rcases hpr with hpra | hprb
          · have ⟨hpa, hra⟩ := hpair_in a p r hpra hp.1 hr.1
            have hpb : p ∉ reachN C.gates b N := fun h => hnd p (by simp) ⟨hpa, h⟩
            have hrb : r ∉ reachN C.gates b N := fun h => hnd r (by simp) ⟨hra, h⟩
            have hpta : (C.gates.foldl wstep (vecOf {p, t})).getD a false = true :=
              hpt.resolve_right fun hptb => hpb (hpair_in b p t hptb hp.2 ht.2).1
            have hqra : (C.gates.foldl wstep (vecOf {q, r})).getD a false = true :=
              hqr.resolve_right fun hqrb => hrb (hpair_in b q r hqrb hq.2 hr.2).2
            exact ih a haw haR hpra hpta hqra hqt.1 hp.1 hr.1
          · have ⟨hpb, hrb⟩ := hpair_in b p r hprb hp.2 hr.2
            have hpa : p ∉ reachN C.gates a N := fun h => hnd p (by simp) ⟨h, hpb⟩
            have hra : r ∉ reachN C.gates a N := fun h => hnd r (by simp) ⟨h, hrb⟩
            have hptb : (C.gates.foldl wstep (vecOf {p, t})).getD b false = true :=
              hpt.resolve_left fun hpta => hpa (hpair_in a p t hpta hp.1 ht.1).1
            have hqrb : (C.gates.foldl wstep (vecOf {q, r})).getD b false = true :=
              hqr.resolve_left fun hqra => hra (hpair_in a q r hqra hq.1 hr.1).2
            exact ih b hbw hbR hprb hptb hqrb hqt.2 hp.2 hr.2

lemma no_K22_with_Z (C : Circuit) (hM : Monotone2 C) (Z : Finset ℕ)
    (hRsub : reachN C.gates C.output (C.gates.length + 1) ⊆
      (reachN C.gates C.output (C.gates.length + 1)).filter (· < 8) ∪
      (reachN C.gates C.output (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length))
    (hcard2 : ∀ w ∈ (reachN C.gates C.output (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length),
      (gateIns C.gates w).card = 2)
    (hdisj4 : ∀ w ∈ (reachN C.gates C.output (C.gates.length + 1)).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length),
      ∀ a b, a ∈ gateIns C.gates w → b ∈ gateIns C.gates w → a ≠ b →
      ∀ x ∈ ({0, 1, 4, 6} : Finset ℕ),
        ¬ (x ∈ reachN C.gates a (C.gates.length + 1) ∧ x ∈ reachN C.gates b (C.gates.length + 1))) :
    ∀ w ∈ reachN C.gates C.output (C.gates.length + 1),
      (C.gates.foldl wstep (vecOf {0, 6})).getD w false = true →
      (C.gates.foldl wstep (vecOf {1, 6})).getD w false = true →
      (C.gates.foldl wstep (vecOf {1, 4})).getD w false = true →
      (C.gates.foldl wstep (vecOf (insert 0 Z))).getD w false = true →
      (C.gates.foldl wstep (vecOf (insert 4 Z))).getD w false = true →
      (C.gates.foldl wstep (vecOf Z)).getD w false = false →
      (C.gates.foldl wstep (vecOf {0})).getD w false = false →
      (C.gates.foldl wstep (vecOf {1})).getD w false = false →
      (C.gates.foldl wstep (vecOf {4})).getD w false = false →
      (C.gates.foldl wstep (vecOf {6})).getD w false = false →
      False := by
  let N := C.gates.length + 1
  have hcard12 : ∀ w ∈ (reachN C.gates C.output N).filter (fun w => 8 ≤ w ∧ w < 8 + C.gates.length),
      (gateIns C.gates w).card = 1 ∨ (gateIns C.gates w).card = 2 :=
    fun w hw => Or.inr (hcard2 w hw)
  have hagreeW : ∀ u (S T : Finset ℕ),
      (∀ i < 8, i ∈ reachN C.gates u N → (i ∈ S ↔ i ∈ T)) →
      (C.gates.foldl wstep (vecOf S)).getD u false = (C.gates.foldl wstep (vecOf T)).getD u false := by
    intro u S T hST
    refine wires_agree_on_reach C.gates u (vecOf S) (vecOf T) (vecOf_len S) (vecOf_len T) ?_ u (out_mem_reachN _ _ _)
    intro i hi hir
    rw [vecOf_getD S i hi, vecOf_getD T i hi, decide_eq_decide]
    exact hST i hi hir
  have hpair_in : ∀ u x y,
      (C.gates.foldl wstep (vecOf {x, y})).getD u false = true →
      (C.gates.foldl wstep (vecOf {x})).getD u false = false →
      (C.gates.foldl wstep (vecOf {y})).getD u false = false →
      x ∈ reachN C.gates u N ∧ y ∈ reachN C.gates u N := by
    intro u x y hxy hx hy
    constructor
    · by_contra hnx
      have heq := hagreeW u {x, y} {y} fun i _ hir => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl); exact absurd hir hnx; rfl
        · intro h; exact Or.inr h
      rw [heq, hy] at hxy; cases hxy
    · by_contra hny
      have heq := hagreeW u {x, y} {x} fun i _ hir => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl); rfl; exact absurd hir hny
        · intro h; exact Or.inl h
      rw [heq, hx] at hxy; cases hxy
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw h06 h16 h14 h0Z h4Z hZ h0 h1 h4 h6
    rcases Finset.mem_union.mp (hRsub hw) with hwU | hwG
    · have hw8 : w < 8 := (Finset.mem_filter.mp hwU).2
      rw [wfold_prefix _ _ _ (by rw [vecOf_len]; exact hw8), vecOf_getD _ w hw8] at h16 h1 h6
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, Finset.mem_insert, Finset.mem_singleton] at h16 h1 h6
      rcases h16 with rfl | rfl
      · exact h1 rfl
      · exact h6 rfl
    · obtain ⟨_, hw8, hwlt⟩ := Finset.mem_filter.mp hwG
      obtain ⟨a, b, hins, haw, hbw, hab, hgi⟩ := gateIns_card_two C hM w hw8 hwlt (hcard2 w hwG)
      have ha_ins : a ∈ gateIns C.gates w := by rw [hgi]; simp
      have hb_ins : b ∈ gateIns C.gates w := by rw [hgi]; simp
      have haR : a ∈ reachN C.gates C.output N := reachN_closed C.gates C.output w a hw ha_ins
      have hbR : b ∈ reachN C.gates C.output N := reachN_closed C.gates C.output w b hw hb_ins
      have hnd := hdisj4 w hwG a b ha_ins hb_ins hab
      have hev := fun S => eval_bin_gate C w a b hw8 hwlt hins haw hbw (vecOf S) (vecOf_len S)
      rcases (by simpa using (hM _ (List.getElem_mem (by omega : w - 8 < C.gates.length))).1 :
          (C.gates[w - 8]'(by omega)).op = GateOp.and ∨ (C.gates[w - 8]'(by omega)).op = GateOp.or) with hop | hop
      · have hand : ∀ S, (C.gates.foldl wstep (vecOf S)).getD w false =
            ((C.gates.foldl wstep (vecOf S)).getD a false && (C.gates.foldl wstep (vecOf S)).getD b false) := by
          intro S; rw [hev S, hop]; simp [GateOp.eval]
        rw [hand] at h06 h16 h14 h0Z h4Z hZ
        simp only [Bool.and_eq_true] at h06 h16 h14 h0Z h4Z
        have ha0 := eval_empty_false C hM C.output hRsub hcard12 a haR
        have hb0 := eval_empty_false C hM C.output hRsub hcard12 b hbR
        have hit : ∀ u x y, (C.gates.foldl wstep (vecOf ∅)).getD u false = false →
            (C.gates.foldl wstep (vecOf {x, y})).getD u false = true →
            x ∈ reachN C.gates u N ∨ y ∈ reachN C.gates u N := by
          intro u x y hu0 hxy
          by_contra hneither
          have ⟨hnx, hny⟩ := not_or.mp hneither
          have heq := hagreeW u {x, y} ∅ fun i _ hir => by
            simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
            rintro (rfl | rfl)
            · exact hnx hir
            · exact hny hir
          rw [heq, hu0] at hxy; cases hxy
        have h06a := hit a 0 6 ha0 h06.1
        have h06b := hit b 0 6 hb0 h06.2
        have h16a := hit a 1 6 ha0 h16.1
        have h16b := hit b 1 6 hb0 h16.2
        have h14a := hit a 1 4 ha0 h14.1
        have h14b := hit b 1 4 hb0 h14.2
        rcases h06a with h0a | h6a
        · have h0b : 0 ∉ reachN C.gates b N := fun h => hnd 0 (by simp) ⟨h0a, h⟩
          have h6b : 6 ∈ reachN C.gates b N := h06b.resolve_left h0b
          have h6a' : 6 ∉ reachN C.gates a N := fun h => hnd 6 (by simp) ⟨h, h6b⟩
          have h1a : 1 ∈ reachN C.gates a N := h16a.resolve_right h6a'
          have h1b : 1 ∉ reachN C.gates b N := fun h => hnd 1 (by simp) ⟨h1a, h⟩
          have h4b : 4 ∈ reachN C.gates b N := h14b.resolve_left h1b
          have h4a' : 4 ∉ reachN C.gates a N := fun h => hnd 4 (by simp) ⟨h, h4b⟩
          have hZa : (C.gates.foldl wstep (vecOf Z)).getD a false = true := by
            rw [hagreeW a Z (insert 4 Z) fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨Or.inr, fun h => h.elim (fun e => absurd (e ▸ hir) h4a') id⟩]
            exact h4Z.1
          have hZb : (C.gates.foldl wstep (vecOf Z)).getD b false = true := by
            rw [hagreeW b Z (insert 0 Z) fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨Or.inr, fun h => h.elim (fun e => absurd (e ▸ hir) h0b) id⟩]
            exact h0Z.2
          rw [hZa, hZb] at hZ; cases hZ
        · have h6b : 6 ∉ reachN C.gates b N := fun h => hnd 6 (by simp) ⟨h6a, h⟩
          have h0b : 0 ∈ reachN C.gates b N := h06b.resolve_right h6b
          have h0a' : 0 ∉ reachN C.gates a N := fun h => hnd 0 (by simp) ⟨h, h0b⟩
          have h1b : 1 ∈ reachN C.gates b N := h16b.resolve_right h6b
          have h1a' : 1 ∉ reachN C.gates a N := fun h => hnd 1 (by simp) ⟨h, h1b⟩
          have h4a : 4 ∈ reachN C.gates a N := h14a.resolve_left h1a'
          have h4b' : 4 ∉ reachN C.gates b N := fun h => hnd 4 (by simp) ⟨h4a, h⟩
          have hZa : (C.gates.foldl wstep (vecOf Z)).getD a false = true := by
            rw [hagreeW a Z (insert 0 Z) fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨Or.inr, fun h => h.elim (fun e => absurd (e ▸ hir) h0a') id⟩]
            exact h0Z.1
          have hZb : (C.gates.foldl wstep (vecOf Z)).getD b false = true := by
            rw [hagreeW b Z (insert 4 Z) fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨Or.inr, fun h => h.elim (fun e => absurd (e ▸ hir) h4b') id⟩]
            exact h4Z.2
          rw [hZa, hZb] at hZ; cases hZ
      · have hor : ∀ S, (C.gates.foldl wstep (vecOf S)).getD w false =
            ((C.gates.foldl wstep (vecOf S)).getD a false || (C.gates.foldl wstep (vecOf S)).getD b false) := by
          intro S; rw [hev S, hop]; simp [GateOp.eval]
        rw [hor] at h06 h16 h14 h0Z h4Z hZ h0 h1 h4 h6
        simp only [Bool.or_eq_false_iff] at hZ h0 h1 h4 h6
        simp only [Bool.or_eq_true] at h06 h16 h14 h0Z h4Z
        rcases h16 with h16a | h16b
        · have ⟨h1a, h6a⟩ := hpair_in a 1 6 h16a h1.1 h6.1
          have h1b : 1 ∉ reachN C.gates b N := fun h => hnd 1 (by simp) ⟨h1a, h⟩
          have h6b : 6 ∉ reachN C.gates b N := fun h => hnd 6 (by simp) ⟨h6a, h⟩
          have h06a : (C.gates.foldl wstep (vecOf {0, 6})).getD a false = true :=
            h06.resolve_right fun h06b => h6b (hpair_in b 0 6 h06b h0.2 h6.2).2
          have h14a : (C.gates.foldl wstep (vecOf {1, 4})).getD a false = true :=
            h14.resolve_right fun h14b => h1b (hpair_in b 1 4 h14b h1.2 h4.2).1
          have h0a : 0 ∈ reachN C.gates a N := (hpair_in a 0 6 h06a h0.1 h6.1).1
          have h4a : 4 ∈ reachN C.gates a N := (hpair_in a 1 4 h14a h1.1 h4.1).2
          have h0b : 0 ∉ reachN C.gates b N := fun h => hnd 0 (by simp) ⟨h0a, h⟩
          have h4b : 4 ∉ reachN C.gates b N := fun h => hnd 4 (by simp) ⟨h4a, h⟩
          have h0Zb : (C.gates.foldl wstep (vecOf (insert 0 Z))).getD b false = false := by
            rw [hagreeW b (insert 0 Z) Z fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ hir) h0b) id, Or.inr⟩]
            exact hZ.2
          have h4Zb : (C.gates.foldl wstep (vecOf (insert 4 Z))).getD b false = false := by
            rw [hagreeW b (insert 4 Z) Z fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ hir) h4b) id, Or.inr⟩]
            exact hZ.2
          have h0Za : (C.gates.foldl wstep (vecOf (insert 0 Z))).getD a false = true :=
            h0Z.resolve_right (by rw [h0Zb]; decide)
          have h4Za : (C.gates.foldl wstep (vecOf (insert 4 Z))).getD a false = true :=
            h4Z.resolve_right (by rw [h4Zb]; decide)
          exact ih a haw haR h06a h16a h14a h0Za h4Za hZ.1 h0.1 h1.1 h4.1 h6.1
        · have ⟨h1b, h6b⟩ := hpair_in b 1 6 h16b h1.2 h6.2
          have h1a : 1 ∉ reachN C.gates a N := fun h => hnd 1 (by simp) ⟨h, h1b⟩
          have h6a : 6 ∉ reachN C.gates a N := fun h => hnd 6 (by simp) ⟨h, h6b⟩
          have h06b : (C.gates.foldl wstep (vecOf {0, 6})).getD b false = true :=
            h06.resolve_left fun h06a => h6a (hpair_in a 0 6 h06a h0.1 h6.1).2
          have h14b : (C.gates.foldl wstep (vecOf {1, 4})).getD b false = true :=
            h14.resolve_left fun h14a => h1a (hpair_in a 1 4 h14a h1.1 h4.1).1
          have h0b : 0 ∈ reachN C.gates b N := (hpair_in b 0 6 h06b h0.2 h6.2).1
          have h4b : 4 ∈ reachN C.gates b N := (hpair_in b 1 4 h14b h1.2 h4.2).2
          have h0a : 0 ∉ reachN C.gates a N := fun h => hnd 0 (by simp) ⟨h, h0b⟩
          have h4a : 4 ∉ reachN C.gates a N := fun h => hnd 4 (by simp) ⟨h, h4b⟩
          have h0Za : (C.gates.foldl wstep (vecOf (insert 0 Z))).getD a false = false := by
            rw [hagreeW a (insert 0 Z) Z fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ hir) h0a) id, Or.inr⟩]
            exact hZ.1
          have h4Za : (C.gates.foldl wstep (vecOf (insert 4 Z))).getD a false = false := by
            rw [hagreeW a (insert 4 Z) Z fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ hir) h4a) id, Or.inr⟩]
            exact hZ.1
          have h0Zb : (C.gates.foldl wstep (vecOf (insert 0 Z))).getD b false = true :=
            h0Z.resolve_left (by rw [h0Za]; decide)
          have h4Zb : (C.gates.foldl wstep (vecOf (insert 4 Z))).getD b false = true :=
            h4Z.resolve_left (by rw [h4Za]; decide)
          exact ih b hbw hbR h06b h16b h14b h0Zb h4Zb hZ.2 h0.2 h1.2 h4.2 h6.2

lemma lower_proof : ¬ RepSizeAtMost targetA 8 := by
  rintro ⟨C, hM, hsz, hrep⟩
  let N := C.gates.length + 1
  let R := reachN C.gates C.output N
  let U := R.filter fun w => w < 8
  let G := R.filter fun w => 8 ≤ w ∧ w < 8 + C.gates.length
  have hall : Finset.range 8 ⊆ U := by
    intro i hi
    rw [Finset.mem_range] at hi
    refine Finset.mem_filter.mpr ⟨?_, hi⟩
    interval_cases i
    · exact input_essential C hM hrep 0 (by decide) 0 3 1 3 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 1 (by decide) 1 2 3 2 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 2 (by decide) 2 1 3 1 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 3 (by decide) 3 0 2 0 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 4 (by decide) 3 0 3 1 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 5 (by decide) 2 1 2 0 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 6 (by decide) 1 2 1 1 (by decide) (by decide) (by decide)
    · exact input_essential C hM hrep 7 (by decide) 0 3 0 1 (by decide) (by decide) (by decide)
  have hU8 : 8 ≤ U.card := by simpa using Finset.card_le_card hall
  have hU_le8 : U.card ≤ 8 := by
    have hsub : U ⊆ Finset.range 8 := fun w hw => Finset.mem_range.mpr (Finset.mem_filter.mp hw).2
    simpa using Finset.card_le_card hsub
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
  have herase_bi : (R.erase C.output).card ≤ (G.biUnion (gateIns C.gates)).card :=
    Finset.card_le_card (reachN_erase_sub_biUnion C.gates C.output N)
  have hbi_sum : (G.biUnion (gateIns C.gates)).card ≤ ∑ w ∈ G, (gateIns C.gates w).card :=
    Finset.card_biUnion_le
  have hgate_le2 : ∀ w ∈ G, (gateIns C.gates w).card ≤ 2 := by
    intro w hw
    obtain ⟨_, h8, hlt⟩ := Finset.mem_filter.mp hw
    have hj : w - 8 < C.gates.length := by omega
    unfold gateIns
    rw [ite_eq_left_of_eq_true _ _ (eq_true h8), List.getElem?_eq_getElem hj]
    have hlen2 : (C.gates[w - 8]'hj).inputs.length ≤ 2 := (hM _ (List.getElem_mem hj)).2
    exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans hlen2)
  have hsum2 : ∑ w ∈ G, (gateIns C.gates w).card ≤ 2 * G.card := by
    have h := Finset.sum_le_sum hgate_le2
    simp only [Finset.sum_const, smul_eq_mul] at h
    omega
  have hout : C.output ∈ R := out_mem_reachN _ _ _
  have hcardE : (R.erase C.output).card + 1 = R.card := Finset.card_erase_add_one hout
  change C.gates.length ≤ 8 at hsz
  have hmono_out : ∀ (S T : Finset ℕ), S ⊆ T →
      (C.gates.foldl wstep (vecOf S)).getD C.output false = true →
      (C.gates.foldl wstep (vecOf T)).getD C.output false = true := by
    intro S T hST hu
    refine wires_mono C.gates (fun g hg => (hM g hg).1) (vecOf S) (vecOf T) (by simp [vecOf_len]) ?_ C.output hu
    intro i hi
    by_cases hi8 : i < 8
    · rw [vecOf_getD S i hi8] at hi
      rw [vecOf_getD T i hi8]
      simp only [decide_eq_true_eq] at hi ⊢
      exact hST hi
    · rw [List.getD_eq_default _ _ (by rw [vecOf_len]; omega)] at hi; cases hi
  have hev_pair : ∀ (u v : Fin 4),
      (C.gates.foldl wstep (vecOf {u.val, 4 + v.val})).getD C.output false = targetA u v := by
    intro u v
    rw [vecOf_pair_eq_oneEach u v]
    exact hrep u v
  have hsing_false : ∀ i < 8, (C.gates.foldl wstep (vecOf {i})).getD C.output false = false := by
    intro i hi
    cases hv : (C.gates.foldl wstep (vecOf {i})).getD C.output false
    · rfl
    · exfalso
      have hbad : ∀ (u v : Fin 4), i ∈ ({u.val, 4 + v.val} : Finset ℕ) → targetA u v = false → False := by
        intro u v him h0
        have h1 := hmono_out {i} {u.val, 4 + v.val} (by intro x hx; simp at hx; subst hx; exact him) hv
        rw [hev_pair u v, h0] at h1; cases h1
      interval_cases i
      · exact hbad 0 1 (by decide) (by decide)
      · exact hbad 1 1 (by decide) (by decide)
      · exact hbad 2 0 (by decide) (by decide)
      · exact hbad 3 1 (by decide) (by decide)
      · exact hbad 2 0 (by decide) (by decide)
      · exact hbad 0 1 (by decide) (by decide)
      · exact hbad 2 2 (by decide) (by decide)
      · exact hbad 1 3 (by decide) (by decide)
  have hkill_disj : R ⊆ U ∪ G →
      (∀ w ∈ G, (gateIns C.gates w).card = 1 ∨ (gateIns C.gates w).card = 2) →
      (∀ w1 ∈ G, ∀ w2 ∈ G, w1 ≠ w2 → Disjoint (gateIns C.gates w1) (gateIns C.gates w2)) → False := by
    intro hRsub hcard12 hdisj_ins
    have hdisj4 : ∀ w ∈ G, ∀ a b, a ∈ gateIns C.gates w → b ∈ gateIns C.gates w → a ≠ b →
        ∀ x ∈ ({0, 1, 6, 7} : Finset ℕ),
          ¬ (x ∈ reachN C.gates a N ∧ x ∈ reachN C.gates b N) := by
      intro w hw a b ha hb hab x hx ⟨hxa, hxb⟩
      have hsub := reachN_inter_sub_z C C.output 99 (fun w1 hw1 w2 hw2 hne y hy1 hy2 =>
        absurd hy2 (Finset.disjoint_left.mp (hdisj_ins w1 hw1 w2 hw2 hne) hy1)) w a b hw ha hb hab
      have hx99 : x ∈ reachN C.gates 99 N := hsub (Finset.mem_inter.mpr ⟨hxa, hxb⟩)
      have hx_le : x < 8 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> omega
      -- wait: 99 might reach nothing, so reachN 99 N = {99}!
      have h99 : reachN C.gates 99 N = {99} := by
        have hstep : ∀ m, reachN C.gates 99 m = {99} := by
          intro m; induction m with
          | zero => rfl
          | succ m ih =>
            simp only [reachN, stepReach, ih]
            have hem : gateIns C.gates 99 = ∅ := by
              unfold gateIns; simp [List.getElem?_eq_none (by omega : C.gates.length ≤ 99 - 8)]
            simp [hem]
        exact hstep N
      rw [h99, Finset.mem_singleton] at hx99; omega
    exact no_P4_gen C hM C.output hRsub hcard12 0 1 6 7 hdisj4 C.output hout
      ((hev_pair 0 2).trans (by decide))
      ((hev_pair 0 3).trans (by decide))
      ((hev_pair 1 2).trans (by decide))
      ((hev_pair 1 3).trans (by decide))
      (hsing_false 0 (by decide))
      (hsing_false 6 (by decide))
  by_cases hG7 : G.card ≤ 7
  · have hReq : R = U ∪ G := by
      apply (Finset.eq_of_subset_of_card_le hsubR ?_).symm
      rw [Finset.card_union_of_disjoint hdisj]; omega
    have hcard2 := sum_eq_two_mul_imp hgate_le2 (by omega)
    have hbi_eq : (G.biUnion (gateIns C.gates)).card = ∑ w ∈ G, (gateIns C.gates w).card := by omega
    have hdisj_ins := biUnion_disjoint_of_card_eq hbi_eq
    exact hkill_disj hReq.subset (fun w hw => Or.inr (hcard2 w hw)) hdisj_ins
  · have hG8 : G.card = 8 := by omega
    by_cases hbi16 : (G.biUnion (gateIns C.gates)).card = ∑ w ∈ G, (gateIns C.gates w).card
    · -- Pairwise disjoint! Could R have 1 extra wire? Wait: (R.erase C.output).card ≤ 16 and R.card ≥ 16,
      -- Wait: if R.card = 17, then C.output ∉ U ∪ G? No, if w ∈ R and w ∉ U ∪ G then w ≥ 8 + C.gates.length so gateIns w = ∅,
      -- so w CANNOT be in G.biUnion? Wait: C.output COULD be ≥ 8 + C.gates.length? No! If C.output ≥ 8 + len, reachN = {C.output}, U = ∅!
      -- Wait: every w ∈ R.erase C.output is in G.biUnion (gateIns) ⊆ {i < 8 + len} = U ∪ G!
      have hRsub : R ⊆ U ∪ G := by
        intro w hw
        by_cases hwout : w = C.output
        · subst hwout
          have hne_U : U.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨u0, hu0⟩ := hne_U
          have hu0R : u0 ∈ R := (Finset.mem_filter.mp hu0).1
          have hu08 : u0 < 8 := (Finset.mem_filter.mp hu0).2
          by_cases hlt : C.output < 8 + C.gates.length
          · by_cases h8 : C.output < 8
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h8⟩)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, by omega, hlt⟩)
          · exfalso
            have hstep : ∀ m, reachN C.gates C.output m = {C.output} := by
              intro m; induction m with
              | zero => rfl
              | succ m ih =>
                simp only [reachN, stepReach, ih]
                have hem : gateIns C.gates C.output = ∅ := by
                  unfold gateIns
                  by_cases h8 : 8 ≤ C.output
                  · rw [ite_eq_left_of_eq_true _ _ (eq_true h8), List.getElem?_eq_none (by omega)]
                  · rw [ite_eq_right_of_eq_false _ _ (eq_false h8)]
                simp [hem]
            rw [show R = {C.output} from hstep N, Finset.mem_singleton] at hu0R
            omega
        · have hbi := reachN_erase_sub_biUnion C.gates C.output N (Finset.mem_erase.mpr ⟨hwout, hw⟩)
          obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.mp hbi
          have ⟨_, hult⟩ := gateIns_sub_gt C.gates u w hwu
          have hwlt : w < u := gateIns_lt C.gates u w hwu
          by_cases h8 : w < 8
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h8⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, by omega, by omega⟩)
      have hR16 : R.card = 16 := by
        have h1 := Finset.card_le_card hRsub
        rw [Finset.card_union_of_disjoint hdisj] at h1
        omega
      have hdisj_ins := biUnion_disjoint_of_card_eq hbi16
      have hcard12 : ∀ w ∈ G, (gateIns C.gates w).card = 1 ∨ (gateIns C.gates w).card = 2 := by
        by_cases hs16 : ∑ w ∈ G, (gateIns C.gates w).card = 16
        · intro w hw; exact Or.inr (sum_eq_two_mul_imp hgate_le2 (by omega) w hw)
        · exact sum_eq_two_mul_sub_one_imp hgate_le2 (by omega)
      exact hkill_disj hRsub hcard12 hdisj_ins
    · -- Exactly 1 excess overlap: sum = 16, biUnion.card = 15!
      have hRsub : R ⊆ U ∪ G := by
        intro w hw
        by_cases hwout : w = C.output
        · subst hwout
          have hne_U : U.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨u0, hu0⟩ := hne_U
          have hu0R : u0 ∈ R := (Finset.mem_filter.mp hu0).1
          have hu08 : u0 < 8 := (Finset.mem_filter.mp hu0).2
          by_cases hlt : C.output < 8 + C.gates.length
          · by_cases h8 : C.output < 8
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h8⟩)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, by omega, hlt⟩)
          · exfalso
            have hstep : ∀ m, reachN C.gates C.output m = {C.output} := by
              intro m; induction m with
              | zero => rfl
              | succ m ih =>
                simp only [reachN, stepReach, ih]
                have hem : gateIns C.gates C.output = ∅ := by
                  unfold gateIns
                  by_cases h8 : 8 ≤ C.output
                  · rw [ite_eq_left_of_eq_true _ _ (eq_true h8), List.getElem?_eq_none (by omega)]
                  · rw [ite_eq_right_of_eq_false _ _ (eq_false h8)]
                simp [hem]
            rw [show R = {C.output} from hstep N, Finset.mem_singleton] at hu0R
            omega
        · have hbi := reachN_erase_sub_biUnion C.gates C.output N (Finset.mem_erase.mpr ⟨hwout, hw⟩)
          obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.mp hbi
          have ⟨_, hult⟩ := gateIns_sub_gt C.gates u w hwu
          have hwlt : w < u := gateIns_lt C.gates u w hwu
          by_cases h8 : w < 8
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h8⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, by omega, by omega⟩)
      have hR16 : R.card = 16 := by
        have h1 := Finset.card_le_card hRsub
        rw [Finset.card_union_of_disjoint hdisj] at h1
        omega
      have hcard2 : ∀ w ∈ G, (gateIns C.gates w).card = 2 :=
        sum_eq_two_mul_imp hgate_le2 (by omega)
      rcases biUnion_at_most_one_overlap (by omega : ∑ w ∈ G, (gateIns C.gates w).card ≤ (G.biUnion (gateIns C.gates)).card + 1) with hdisj_ins | ⟨z, _, ⟨w1, hw1, w2, hw2, hw12, hzw1, hzw2⟩, hunique⟩
      · exact hkill_disj hRsub (fun w hw => Or.inr (hcard2 w hw)) hdisj_ins
      · have hzR : z ∈ R := reachN_closed C.gates C.output w1 z (Finset.mem_filter.mp hw1).1 hzw1
        have hout_ner : C.output ∉ (reachN C.gates z N).erase z := by
          intro hmem
          have ⟨hne, hin⟩ := Finset.mem_erase.mp hmem
          have hle1 : C.output ≤ z := reachN_le_out C.gates z N C.output hin
          have hlt1 : z < w1 := gateIns_lt C.gates w1 z hzw1
          have hle2 : w1 ≤ C.output := reachN_le_out C.gates C.output N w1 (Finset.mem_filter.mp hw1).1
          omega
        let L := (reachN C.gates z N).filter (· < 8)
        have hkill_P4 : ∀ (p q r t : Fin 4),
            p.val ∉ L → q.val ∉ L → (4 + r.val) ∉ L → (4 + t.val) ∉ L →
            targetA p r = true → targetA p t = true → targetA q r = true → targetA q t = false → False := by
          intro p q r t hpL hqL hrL htL hpr hpt hqr hqt
          have hdisj4 : ∀ w ∈ G, ∀ a b, a ∈ gateIns C.gates w → b ∈ gateIns C.gates w → a ≠ b →
              ∀ x ∈ ({p.val, q.val, 4 + r.val, 4 + t.val} : Finset ℕ),
                ¬ (x ∈ reachN C.gates a N ∧ x ∈ reachN C.gates b N) := by
            intro w hw a b ha hb hab x hx ⟨hxa, hxb⟩
            have hxz : x ∈ reachN C.gates z N :=
              reachN_inter_sub_z C C.output z hunique w a b hw ha hb hab (Finset.mem_inter.mpr ⟨hxa, hxb⟩)
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl
            · exact hpL (Finset.mem_filter.mpr ⟨hxz, by omega⟩)
            · exact hqL (Finset.mem_filter.mpr ⟨hxz, by omega⟩)
            · exact hrL (Finset.mem_filter.mpr ⟨hxz, by omega⟩)
            · exact htL (Finset.mem_filter.mpr ⟨hxz, by omega⟩)
          exact no_P4_gen C hM C.output hRsub (fun w hw => Or.inr (hcard2 w hw)) p.val q.val (4 + r.val) (4 + t.val)
            hdisj4 C.output hout
            ((hev_pair p r).trans hpr) ((hev_pair p t).trans hpt)
            ((hev_pair q r).trans hqr) ((hev_pair q t).trans hqt)
            (hsing_false p.val (by omega)) (hsing_false (4 + r.val) (by omega))
        have hdom : ∀ (S T : Finset ℕ),
            (∀ i < 8, i ∉ L → (i ∈ S ↔ i ∈ T)) →
            (C.gates.foldl wstep (vecOf S)).getD z false = (C.gates.foldl wstep (vecOf T)).getD z false →
            (C.gates.foldl wstep (vecOf S)).getD C.output false = (C.gates.foldl wstep (vecOf T)).getD C.output false := by
          intro S T hST hz_eq
          refine dominator_z C z hzR hunique (vecOf S) (vecOf T) (vecOf_len S) (vecOf_len T) ?_ hz_eq C.output hout hout_ner
          intro i hi hiz
          rw [vecOf_getD S i hi, vecOf_getD T i hi, decide_eq_decide]
          exact hST i hi (fun h => hiz (Finset.mem_filter.mp h).1)
        have hagreeZ : ∀ (S T : Finset ℕ),
            (∀ i < 8, i ∈ L → (i ∈ S ↔ i ∈ T)) →
            (C.gates.foldl wstep (vecOf S)).getD z false = (C.gates.foldl wstep (vecOf T)).getD z false := by
          intro S T hST
          refine wires_agree_on_reach C.gates z (vecOf S) (vecOf T) (vecOf_len S) (vecOf_len T) ?_ z (out_mem_reachN _ _ _)
          intro i hi hiz
          rw [vecOf_getD S i hi, vecOf_getD T i hi, decide_eq_decide]
          exact hST i hi (Finset.mem_filter.mpr ⟨hiz, hi⟩)
        have hz_empty : (C.gates.foldl wstep (vecOf ∅)).getD z false = false :=
          eval_empty_false C hM C.output hRsub (fun w hw => Or.inr (hcard2 w hw)) z hzR
        have hout_empty : (C.gates.foldl wstep (vecOf ∅)).getD C.output false = false :=
          eval_empty_false C hM C.output hRsub (fun w hw => Or.inr (hcard2 w hw)) C.output hout
        by_cases hT : ∃ i0 ∈ L, (C.gates.foldl wstep (vecOf {i0})).getD z false = true
        · -- Case T ≠ ∅
          obtain ⟨i0, hi0L, hi0t⟩ := hT
          have hi08 : i0 < 8 := (Finset.mem_filter.mp hi0L).2
          have hsubL_false : ∀ (S : Finset ℕ), S ⊆ L → (C.gates.foldl wstep (vecOf S)).getD C.output false = false := by
            intro S hSL
            cases hv : (C.gates.foldl wstep (vecOf S)).getD z false
            · rw [hdom S ∅ (fun i _ hiL => by simp; intro h; exact absurd (hSL h) hiL) (hv.trans hz_empty.symm)]
              exact hout_empty
            · rw [hdom S {i0} (fun i _ hiL => by
                simp only [Finset.mem_singleton]
                exact ⟨fun h => absurd (hSL h) hiL, fun e => absurd (e ▸ hi0L) hiL⟩) (hv.trans hi0t.symm)]
              exact hsing_false i0 hi08
          have hno_edge_L : ∀ (u v : Fin 4), targetA u v = true → ¬ (u.val ∈ L ∧ 4 + v.val ∈ L) := by
            rintro u v h1 ⟨huL, hvL⟩
            have h0 := hsubL_false {u.val, 4 + v.val} (by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption)
            rw [hev_pair u v, h1] at h0; cases h0
          have hall_T : ∀ i ∈ L, (C.gates.foldl wstep (vecOf {i})).getD z false = true := by
            intro i hiL
            cases hv : (C.gates.foldl wstep (vecOf {i})).getD z false
            · exfalso
              have hi8 : i < 8 := (Finset.mem_filter.mp hiL).2
              have hzero : ∀ (u v : Fin 4), i ∈ ({u.val, 4 + v.val} : Finset ℕ) → targetA u v = true → False := by
                intro u v him h1
                have hother : ∃ k, {u.val, 4 + v.val} = ({i, k} : Finset ℕ) ∧ k < 8 := by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at him
                  rcases him with rfl | rfl
                  · exact ⟨4 + v.val, rfl, by omega⟩
                  · exact ⟨u.val, Finset.pair_comm _ _, by omega⟩
                obtain ⟨k, heq, hk8⟩ := hother
                by_cases hkL : k ∈ L
                · have h0 := hsubL_false {u.val, 4 + v.val} (by
                    rw [heq]; intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl <;> assumption)
                  rw [hev_pair u v, h1] at h0; cases h0
                · have hzk : (C.gates.foldl wstep (vecOf {i, k})).getD z false =
                      (C.gates.foldl wstep (vecOf {k})).getD z false := by
                    have h1' : (C.gates.foldl wstep (vecOf {i, k})).getD z false =
                        (C.gates.foldl wstep (vecOf {i})).getD z false :=
                      hagreeZ {i, k} {i} fun x _ hxL => by
                        simp only [Finset.mem_insert, Finset.mem_singleton]
                        exact ⟨fun h => h.elim id (fun e => absurd (e ▸ hxL) hkL), Or.inl⟩
                    have h2' : (C.gates.foldl wstep (vecOf {k})).getD z false =
                        (C.gates.foldl wstep (vecOf ∅)).getD z false :=
                      hagreeZ {k} ∅ fun x _ hxL => by
                        simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
                        intro e; exact hkL (e ▸ hxL)
                    rw [h1', hv, h2', hz_empty]
                  have h0 := hdom {i, k} {k} (fun x _ hxL => by
                    simp only [Finset.mem_insert, Finset.mem_singleton]
                    exact ⟨fun h => h.elim (fun e => absurd (e ▸ hiL) hxL) id, Or.inr⟩) hzk
                  rw [← heq, hev_pair u v, h1, hsing_false k hk8] at h0; cases h0
              interval_cases i
              · exact hzero 0 0 (by decide) (by decide)
              · exact hzero 1 0 (by decide) (by decide)
              · exact hzero 2 1 (by decide) (by decide)
              · exact hzero 3 0 (by decide) (by decide)
              · exact hzero 0 0 (by decide) (by decide)
              · exact hzero 2 1 (by decide) (by decide)
              · exact hzero 0 2 (by decide) (by decide)
              · exact hzero 0 3 (by decide) (by decide)
            · rfl
          have hno_pair_L : ∀ (u1 u2 v : Fin 4), targetA u1 v = true → targetA u2 v = false →
              ¬ (u1.val ∈ L ∧ u2.val ∈ L) := by
            rintro u1 u2 v h1 h0 ⟨hu1L, hu2L⟩
            have hvL : 4 + v.val ∉ L := fun hv => hno_edge_L u1 v h1 ⟨hu1L, hv⟩
            have hz1 : (C.gates.foldl wstep (vecOf {u1.val, 4 + v.val})).getD z false = true := by
              rw [hagreeZ {u1.val, 4 + v.val} {u1.val} fun x _ hxL => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                exact ⟨fun h => h.elim id (fun e => absurd (e ▸ hxL) hvL), Or.inl⟩]
              exact hall_T u1.val hu1L
            have hz2 : (C.gates.foldl wstep (vecOf {u2.val, 4 + v.val})).getD z false = true := by
              rw [hagreeZ {u2.val, 4 + v.val} {u2.val} fun x _ hxL => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                exact ⟨fun h => h.elim id (fun e => absurd (e ▸ hxL) hvL), Or.inl⟩]
              exact hall_T u2.val hu2L
            have heq := hdom {u1.val, 4 + v.val} {u2.val, 4 + v.val} (fun x _ hxL => by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ hu1L) hxL) Or.inr,
                     fun h => h.elim (fun e => absurd (e ▸ hu2L) hxL) Or.inr⟩) (hz1.trans hz2.symm)
            rw [hev_pair u1 v, hev_pair u2 v, h1, h0] at heq; cases heq
          have hno_pair_R : ∀ (u v1 v2 : Fin 4), targetA u v1 = true → targetA u v2 = false →
              ¬ (4 + v1.val ∈ L ∧ 4 + v2.val ∈ L) := by
            rintro u v1 v2 h1 h0 ⟨hv1L, hv2L⟩
            have huL : u.val ∉ L := fun hu => hno_edge_L u v1 h1 ⟨hu, hv1L⟩
            have hz1 : (C.gates.foldl wstep (vecOf {u.val, 4 + v1.val})).getD z false = true := by
              rw [hagreeZ {u.val, 4 + v1.val} {4 + v1.val} fun x _ hxL => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                exact ⟨fun h => h.elim (fun e => absurd (e ▸ hxL) huL) id, Or.inr⟩]
              exact hall_T (4 + v1.val) hv1L
            have hz2 : (C.gates.foldl wstep (vecOf {u.val, 4 + v2.val})).getD z false = true := by
              rw [hagreeZ {u.val, 4 + v2.val} {4 + v2.val} fun x _ hxL => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                exact ⟨fun h => h.elim (fun e => absurd (e ▸ hxL) huL) id, Or.inr⟩]
              exact hall_T (4 + v2.val) hv2L
            have heq := hdom {u.val, 4 + v1.val} {u.val, 4 + v2.val} (fun x _ hxL => by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact ⟨fun h => h.elim Or.inl (fun e => absurd (e ▸ hv1L) hxL),
                     fun h => h.elim Or.inl (fun e => absurd (e ▸ hv2L) hxL)⟩) (hz1.trans hz2.symm)
            rw [hev_pair u v1, hev_pair u v2, h1, h0] at heq; cases heq
          have hp1 : ¬ (0 ∉ L ∧ 1 ∉ L ∧ 6 ∉ L ∧ 7 ∉ L) := fun ⟨a, b, c, d⟩ =>
            hkill_P4 0 1 2 3 a b c d (by decide) (by decide) (by decide) (by decide)
          have hp2 : ¬ (0 ∉ L ∧ 1 ∉ L ∧ 4 ∉ L ∧ 7 ∉ L) := fun ⟨a, b, c, d⟩ =>
            hkill_P4 0 1 0 3 a b c d (by decide) (by decide) (by decide) (by decide)
          have hp3 : ¬ (1 ∉ L ∧ 3 ∉ L ∧ 4 ∉ L ∧ 6 ∉ L) := fun ⟨a, b, c, d⟩ =>
            hkill_P4 1 3 0 2 a b c d (by decide) (by decide) (by decide) (by decide)
          have hp4 : ¬ (0 ∉ L ∧ 3 ∉ L ∧ 4 ∉ L ∧ 6 ∉ L) := fun ⟨a, b, c, d⟩ =>
            hkill_P4 0 3 0 2 a b c d (by decide) (by decide) (by decide) (by decide)
          have hp5 : ¬ (0 ∉ L ∧ 3 ∉ L ∧ 4 ∉ L ∧ 7 ∉ L) := fun ⟨a, b, c, d⟩ =>
            hkill_P4 0 3 0 3 a b c d (by decide) (by decide) (by decide) (by decide)
          have hl01 : ¬ (0 ∈ L ∧ 1 ∈ L) := by simpa using hno_pair_L 0 1 3 (by decide) (by decide)
          have hl03 : ¬ (0 ∈ L ∧ 3 ∈ L) := by simpa using hno_pair_L 0 3 2 (by decide) (by decide)
          have hl13 : ¬ (1 ∈ L ∧ 3 ∈ L) := by simpa using hno_pair_L 1 3 2 (by decide) (by decide)
          have hr46 : ¬ (4 ∈ L ∧ 6 ∈ L) := by simpa using hno_pair_R 3 0 2 (by decide) (by decide)
          have hr47 : ¬ (4 ∈ L ∧ 7 ∈ L) := by simpa using hno_pair_R 1 0 3 (by decide) (by decide)
          have hr67 : ¬ (6 ∈ L ∧ 7 ∈ L) := by simpa using hno_pair_R 1 2 3 (by decide) (by decide)
          have he04 : ¬ (0 ∈ L ∧ 4 ∈ L) := by simpa using hno_edge_L 0 0 (by decide)
          have he06 : ¬ (0 ∈ L ∧ 6 ∈ L) := by simpa using hno_edge_L 0 2 (by decide)
          have he07 : ¬ (0 ∈ L ∧ 7 ∈ L) := by simpa using hno_edge_L 0 3 (by decide)
          have he14 : ¬ (1 ∈ L ∧ 4 ∈ L) := by simpa using hno_edge_L 1 0 (by decide)
          have he16 : ¬ (1 ∈ L ∧ 6 ∈ L) := by simpa using hno_edge_L 1 2 (by decide)
          have he34 : ¬ (3 ∈ L ∧ 4 ∈ L) := by simpa using hno_edge_L 3 0 (by decide)
          have h0146 : 0 ∉ L ∧ 1 ∉ L ∧ 4 ∉ L ∧ 6 ∉ L := by
            have h0n : 0 ∉ L := fun h0 =>
              hp3 ⟨fun h => hl01 ⟨h0, h⟩, fun h => hl03 ⟨h0, h⟩, fun h => he04 ⟨h0, h⟩, fun h => he06 ⟨h0, h⟩⟩
            have h1n : 1 ∉ L := fun h1 =>
              hp4 ⟨h0n, fun h => hl13 ⟨h1, h⟩, fun h => he14 ⟨h1, h⟩, fun h => he16 ⟨h1, h⟩⟩
            have h4n : 4 ∉ L := fun h4 =>
              hp1 ⟨h0n, h1n, fun h => hr46 ⟨h4, h⟩, fun h => hr47 ⟨h4, h⟩⟩
            have h6n : 6 ∉ L := fun h6 =>
              hp2 ⟨h0n, h1n, h4n, fun h => hr67 ⟨h6, h⟩⟩
            exact ⟨h0n, h1n, h4n, h6n⟩
          have hdisj4 : ∀ w ∈ G, ∀ a b, a ∈ gateIns C.gates w → b ∈ gateIns C.gates w → a ≠ b →
              ∀ x ∈ ({0, 1, 4, 6} : Finset ℕ),
                ¬ (x ∈ reachN C.gates a N ∧ x ∈ reachN C.gates b N) := by
            intro w hw a b ha hb hab x hx ⟨hxa, hxb⟩
            have hxz : x ∈ reachN C.gates z N :=
              reachN_inter_sub_z C C.output z hunique w a b hw ha hb hab (Finset.mem_inter.mpr ⟨hxa, hxb⟩)
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl
            · exact h0146.1 (Finset.mem_filter.mpr ⟨hxz, by decide⟩)
            · exact h0146.2.1 (Finset.mem_filter.mpr ⟨hxz, by decide⟩)
            · exact h0146.2.2.1 (Finset.mem_filter.mpr ⟨hxz, by decide⟩)
            · exact h0146.2.2.2 (Finset.mem_filter.mpr ⟨hxz, by decide⟩)
          have h0Z : (C.gates.foldl wstep (vecOf (insert 0 ({3, 7} : Finset ℕ)))).getD C.output false = true :=
            hmono_out {0, 7} (insert 0 {3, 7}) (by decide) ((hev_pair 0 3).trans (by decide))
          have h4Z : (C.gates.foldl wstep (vecOf (insert 4 ({3, 7} : Finset ℕ)))).getD C.output false = true :=
            hmono_out {3, 4} (insert 4 {3, 7}) (by decide) ((hev_pair 3 0).trans (by decide))
          exact no_K22_with_Z C hM {3, 7} hRsub hcard2 hdisj4 C.output hout
            ((hev_pair 0 2).trans (by decide))
            ((hev_pair 1 2).trans (by decide))
            ((hev_pair 1 0).trans (by decide))
            h0Z h4Z
            ((hev_pair 3 3).trans (by decide))
            (hsing_false 0 (by decide)) (hsing_false 1 (by decide))
            (hsing_false 4 (by decide)) (hsing_false 6 (by decide))
        · -- Case T = ∅: ∀ i ∈ L, eval z {i} = false
          have hall_F : ∀ i ∈ L, (C.gates.foldl wstep (vecOf {i})).getD z false = false := by
            intro i hiL
            cases hv : (C.gates.foldl wstep (vecOf {i})).getD z false
            · rfl
            · exact absurd ⟨i, hiL, hv⟩ hT
          have hcomp : ∀ (u v : Fin 4), targetA u v = true → (u.val ∈ L ↔ 4 + v.val ∈ L) := by
            intro u v h1
            constructor
            · intro huL
              by_contra hvL
              have hzeq : (C.gates.foldl wstep (vecOf {u.val, 4 + v.val})).getD z false =
                  (C.gates.foldl wstep (vecOf {4 + v.val})).getD z false := by
                have h1' : (C.gates.foldl wstep (vecOf {u.val, 4 + v.val})).getD z false =
                    (C.gates.foldl wstep (vecOf {u.val})).getD z false :=
                  hagreeZ _ _ fun x _ hxL => by
                    simp only [Finset.mem_insert, Finset.mem_singleton]
                    exact ⟨fun h => h.elim id (fun e => absurd (e ▸ hxL) hvL), Or.inl⟩
                have h2' : (C.gates.foldl wstep (vecOf {4 + v.val})).getD z false =
                    (C.gates.foldl wstep (vecOf ∅)).getD z false :=
                  hagreeZ _ _ fun x _ hxL => by
                    simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
                    intro e; exact hvL (e ▸ hxL)
                rw [h1', hall_F u.val huL, h2', hz_empty]
              have h0 := hdom {u.val, 4 + v.val} {4 + v.val} (fun x _ hxL => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                exact ⟨fun h => h.elim (fun e => absurd (e ▸ huL) hxL) id, Or.inr⟩) hzeq
              rw [hev_pair u v, h1, hsing_false (4 + v.val) (by omega)] at h0; cases h0
            · intro hvL
              by_contra huL
              have hzeq : (C.gates.foldl wstep (vecOf {u.val, 4 + v.val})).getD z false =
                  (C.gates.foldl wstep (vecOf {u.val})).getD z false := by
                have h1' : (C.gates.foldl wstep (vecOf {u.val, 4 + v.val})).getD z false =
                    (C.gates.foldl wstep (vecOf {4 + v.val})).getD z false :=
                  hagreeZ _ _ fun x _ hxL => by
                    simp only [Finset.mem_insert, Finset.mem_singleton]
                    exact ⟨fun h => h.elim (fun e => absurd (e ▸ hxL) huL) id, Or.inr⟩
                have h2' : (C.gates.foldl wstep (vecOf {u.val})).getD z false =
                    (C.gates.foldl wstep (vecOf ∅)).getD z false :=
                  hagreeZ _ _ fun x _ hxL => by
                    simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
                    intro e; exact huL (e ▸ hxL)
                rw [h1', hall_F (4 + v.val) hvL, h2', hz_empty]
              have h0 := hdom {u.val, 4 + v.val} {u.val} (fun x _ hxL => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                exact ⟨fun h => h.elim id (fun e => absurd (e ▸ hvL) hxL), Or.inl⟩) hzeq
              rw [hev_pair u v, h1, hsing_false u.val (by omega)] at h0; cases h0
          have hc04 : 0 ∈ L ↔ 4 ∈ L := by simpa using hcomp 0 0 (by decide)
          have hc06 : 0 ∈ L ↔ 6 ∈ L := by simpa using hcomp 0 2 (by decide)
          have hc07 : 0 ∈ L ↔ 7 ∈ L := by simpa using hcomp 0 3 (by decide)
          have hc14 : 1 ∈ L ↔ 4 ∈ L := by simpa using hcomp 1 0 (by decide)
          have hc34 : 3 ∈ L ↔ 4 ∈ L := by simpa using hcomp 3 0 (by decide)
          have hc25 : 2 ∈ L ↔ 5 ∈ L := by simpa using hcomp 2 1 (by decide)
          by_cases h0L : 0 ∈ L
          · have h4L : 4 ∈ L := hc04.mp h0L
            have h6L : 6 ∈ L := hc06.mp h0L
            have h7L : 7 ∈ L := hc07.mp h0L
            have h1L : 1 ∈ L := hc14.mpr h4L
            have h3L : 3 ∈ L := hc34.mpr h4L
            by_cases h2L : 2 ∈ L
            · have h5L : 5 ∈ L := hc25.mp h2L
              -- All 8 inputs in L => |Gz| >= 7, plus w1 != w2 outside Rz => |G| >= 9 > 8!
              let Rz := reachN C.gates z N
              let Gz := Rz.filter fun w => 8 ≤ w ∧ w < 8 + C.gates.length
              have hL8 : 8 ≤ L.card := by
                have hsub : Finset.range 8 ⊆ L := by
                  intro i hi; rw [Finset.mem_range] at hi; interval_cases i <;> assumption
                simpa using Finset.card_le_card hsub
              have hdisjZ : Disjoint L Gz := by
                rw [Finset.disjoint_left]; intro w hw1 hw2
                have a := (Finset.mem_filter.mp hw1).2; have b := (Finset.mem_filter.mp hw2).2.1; omega
              have hsubRz : L ∪ Gz ⊆ Rz := fun w hw =>
                (Finset.mem_union.mp hw).elim (fun h => (Finset.mem_filter.mp h).1) (fun h => (Finset.mem_filter.mp h).1)
              have hRzcard : L.card + Gz.card ≤ Rz.card := by
                rw [← Finset.card_union_of_disjoint hdisjZ]; exact Finset.card_le_card hsubRz
              have herZ : (Rz.erase z).card ≤ ∑ w ∈ Gz, (gateIns C.gates w).card :=
                (Finset.card_le_card (reachN_erase_sub_biUnion C.gates z N)).trans Finset.card_biUnion_le
              have hsumZ : ∑ w ∈ Gz, (gateIns C.gates w).card ≤ 2 * Gz.card := by
                have hle : ∀ w ∈ Gz, (gateIns C.gates w).card ≤ 2 := fun w hw =>
                  hgate_le2 w (Finset.mem_filter.mpr ⟨reachN_sub_of_mem C.gates C.output z hzR N (Finset.mem_filter.mp hw).1,
                    (Finset.mem_filter.mp hw).2⟩)
                have h := Finset.sum_le_sum hle; simp only [Finset.sum_const, smul_eq_mul] at h; omega
              have hcardEZ : (Rz.erase z).card + 1 = Rz.card := Finset.card_erase_add_one (out_mem_reachN _ _ _)
              have hGz7 : 7 ≤ Gz.card := by omega
              have hw1_not : w1 ∉ Gz := fun h => by
                have := reachN_le_out C.gates z N w1 (Finset.mem_filter.mp h).1
                have := gateIns_lt C.gates w1 z hzw1; omega
              have hw2_not : w2 ∉ Gz := fun h => by
                have := reachN_le_out C.gates z N w2 (Finset.mem_filter.mp h).1
                have := gateIns_lt C.gates w2 z hzw2; omega
              have hGz_sub : Gz ∪ {w1, w2} ⊆ G := by
                intro w hw; rcases Finset.mem_union.mp hw with h | h
                · exact Finset.mem_filter.mpr ⟨reachN_sub_of_mem C.gates C.output z hzR N (Finset.mem_filter.mp h).1,
                    (Finset.mem_filter.mp h).2⟩
                · simp only [Finset.mem_insert, Finset.mem_singleton] at h; rcases h with rfl | rfl <;> assumption
              have hdisj12 : Disjoint Gz {w1, w2} := by
                rw [Finset.disjoint_right]; intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                rcases hw with rfl | rfl <;> assumption
              have hcard9 := Finset.card_le_card hGz_sub
              rw [Finset.card_union_of_disjoint hdisj12, Finset.card_pair hw12] at hcard9
              omega
            · -- z itself is a read-once tree computing T3 on {0,1,3,4,6,7} -> P4 on (0,1,4,7)!
              let Rz := reachN C.gates z N
              let Gz := Rz.filter fun w => 8 ≤ w ∧ w < 8 + C.gates.length
              have hsubRzR : Rz ⊆ R := reachN_sub_of_mem C.gates C.output z hzR N
              have hRzsub : Rz ⊆ Rz.filter (· < 8) ∪ Gz := by
                intro w hw
                rcases Finset.mem_union.mp (hRsub (hsubRzR hw)) with hwU | hwG
                · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, (Finset.mem_filter.mp hwU).2⟩)
                · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, (Finset.mem_filter.mp hwG).2⟩)
              have hcardZ : ∀ w ∈ Gz, (gateIns C.gates w).card = 1 ∨ (gateIns C.gates w).card = 2 :=
                fun w hw => Or.inr (hcard2 w (Finset.mem_filter.mpr ⟨hsubRzR (Finset.mem_filter.mp hw).1,
                  (Finset.mem_filter.mp hw).2⟩))
              have hdisjZ : ∀ w ∈ Gz, ∀ a b, a ∈ gateIns C.gates w → b ∈ gateIns C.gates w → a ≠ b →
                  ∀ x ∈ ({0, 1, 4, 7} : Finset ℕ),
                    ¬ (x ∈ reachN C.gates a N ∧ x ∈ reachN C.gates b N) := by
                intro w hw a b ha hb hab x _ ⟨hxa, hxb⟩
                have huniqZ : ∀ u1 ∈ Gz, ∀ u2 ∈ Gz, u1 ≠ u2 → ∀ y, y ∈ gateIns C.gates u1 → y ∈ gateIns C.gates u2 → False := by
                  intro u1 hu1 u2 hu2 hune y hy1 hy2
                  have hyz := hunique u1 (Finset.mem_filter.mpr ⟨hsubRzR (Finset.mem_filter.mp hu1).1, (Finset.mem_filter.mp hu1).2⟩)
                    u2 (Finset.mem_filter.mpr ⟨hsubRzR (Finset.mem_filter.mp hu2).1, (Finset.mem_filter.mp hu2).2⟩) hune y hy1 hy2
                  have hlt := gateIns_lt C.gates u1 y hy1
                  have hle := reachN_le_out C.gates z N u1 (Finset.mem_filter.mp hu1).1
                  omega
                have hsub := reachN_inter_sub_z C z 99 (fun u1 hu1 u2 hu2 hune y hy1 hy2 =>
                  absurd hy2 (fun h => huniqZ u1 hu1 u2 hu2 hune y hy1 h)) w a b hw ha hb hab
                have hx99 := hsub (Finset.mem_inter.mpr ⟨hxa, hxb⟩)
                have h99 : reachN C.gates 99 N = {99} := by
                  have hstep : ∀ m, reachN C.gates 99 m = {99} := by
                    intro m; induction m with
                    | zero => rfl
                    | succ m ih =>
                      simp only [reachN, stepReach, ih]
                      have hem : gateIns C.gates 99 = ∅ := by
                        unfold gateIns; simp [List.getElem?_eq_none (by omega : C.gates.length ≤ 99 - 8)]
                      simp [hem]
                  exact hstep N
                rw [h99, Finset.mem_singleton] at hx99
                have hle := reachN_le_out C.gates C.output N x (hsubRzR (reachN_sub_of_mem C.gates z a
                  (reachN_closed C.gates z w a (Finset.mem_filter.mp hw).1 ha) N hxa))
                have hle2 := (Finset.mem_filter.mp hw).2.2
                have hle3 := reachN_le_out C.gates a N x hxa
                have hlt4 := gateIns_lt C.gates w a ha
                omega
              have hz_of_one : ∀ (u v : Fin 4), u.val ∈ L → 4 + v.val ∈ L → targetA u v = true →
                  (C.gates.foldl wstep (vecOf {u.val, 4 + v.val})).getD z false = true := by
                intro u v huL hvL h1
                cases hv : (C.gates.foldl wstep (vecOf {u.val, 4 + v.val})).getD z false
                · exfalso
                  have h0 := hdom {u.val, 4 + v.val} ∅ (fun i _ hiL => by
                    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
                    rintro (rfl | rfl)
                    · exact hiL huL
                    · exact hiL hvL) (hv.trans hz_empty.symm)
                  rw [hev_pair u v, h1, hout_empty] at h0; cases h0
                · rfl
              have hz04 := hz_of_one 0 0 h0L h4L (by decide)
              have hz07 := hz_of_one 0 3 h0L h7L (by decide)
              have hz14 := hz_of_one 1 0 h1L h4L (by decide)
              have hz17 : (C.gates.foldl wstep (vecOf {1, 7})).getD z false = false := by
                cases hv : (C.gates.foldl wstep (vecOf {1, 7})).getD z false
                · rfl
                · exfalso
                  have heq := hdom {1, 7} {0, 7} (fun i _ hiL => by
                    simp only [Finset.mem_insert, Finset.mem_singleton]
                    exact ⟨fun h => h.elim (fun e => absurd (e ▸ h1L) hiL) (fun e => absurd (e ▸ h7L) hiL),
                           fun h => h.elim (fun e => absurd (e ▸ h0L) hiL) (fun e => absurd (e ▸ h7L) hiL)⟩)
                    (hv.trans hz07.symm)
                  have h13 : (C.gates.foldl wstep (vecOf {1, 7})).getD C.output false = false :=
                    (hev_pair 1 3).trans (by decide)
                  have h03 : (C.gates.foldl wstep (vecOf {0, 7})).getD C.output false = true :=
                    (hev_pair 0 3).trans (by decide)
                  rw [h13, h03] at heq; cases heq
              exact no_P4_gen C hM z hRzsub hcardZ 0 1 4 7 hdisjZ z (out_mem_reachN _ _ _)
                hz04 hz07 hz14 hz17 (hall_F 0 h0L) (hall_F 4 h4L)
          · -- 0 ∉ L => 0, 1, 6, 7 ∉ L => P4 on (0, 1, 6, 7)!
            have h4n : 4 ∉ L := fun h => h0L (hc04.mpr h)
            have h6n : 6 ∉ L := fun h => h0L (hc06.mpr h)
            have h7n : 7 ∉ L := fun h => h0L (hc07.mpr h)
            have h1n : 1 ∉ L := fun h => h4n (hc14.mp h)
            exact hkill_P4 0 1 2 3 h0L h1n h6n h7n (by decide) (by decide) (by decide) (by decide)

end PEqualNP.Outside.L_meta_6013

theorem PEqualNP.Outside.L_meta_6013 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4701 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4701 : ℕ).testBit (4 * u.val + v.val)) 8 :=
  ⟨PEqualNP.Outside.L_meta_6013.upper_proof, PEqualNP.Outside.L_meta_6013.lower_proof⟩

