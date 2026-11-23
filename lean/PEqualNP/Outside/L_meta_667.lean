import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_667

open PEqualNP.CircuitLowerBounds

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def runWires (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl stepWire init

private lemma runWires_length (gs : List Gate) (init : List Bool) :
    (runWires gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [runWires]
  | cons g gs ih =>
    change (runWires gs (stepWire init g)).length = init.length + (gs.length + 1)
    rw [ih, stepWire, List.length_append, List.length_singleton]
    omega

private lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < w.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1]
    by_cases h2 : i = w.length
    · subst h2
      rw [if_pos rfl, List.getElem?_append_right (le_refl _)]
      simp
    · rw [if_neg h2, List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

private lemma getD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private lemma runWires_getD_prefix (gs : List Gate) (init : List Bool) (i : ℕ)
    (hi : i < init.length) :
    (runWires gs init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    change (runWires gs (stepWire init g)).getD i false = init.getD i false
    have hlt : i < (stepWire init g).length := by
      simp only [stepWire, List.length_append, List.length_singleton]
      omega
    rw [ih (stepWire init g) hlt, stepWire, getD_append_singleton, if_pos hi]

private lemma runWires_getD_gate (gs : List Gate) (init : List Bool) (j : ℕ)
    (hj : j < gs.length) :
    (runWires gs init).getD (init.length + j) false =
      (gs[j]).op.eval
        ((gs[j]).inputs.map fun i =>
          if i < init.length + j then (runWires gs init).getD i false else false) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      change (runWires gs (stepWire init g)).getD (init.length + 0) false =
        g.op.eval (g.inputs.map fun i =>
          if i < init.length + 0 then (runWires gs (stepWire init g)).getD i false else false)
      have hlen : init.length < (stepWire init g).length := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      rw [Nat.add_zero, runWires_getD_prefix gs (stepWire init g) init.length hlen]
      have hhead : (stepWire init g).getD init.length false =
          g.op.eval (g.inputs.map fun i => init.getD i false) := by
        rw [stepWire, getD_append_singleton, if_neg (lt_irrefl _), if_pos rfl]
      rw [hhead]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length
      · rw [if_pos hi]
        have hi' : i < (stepWire init g).length := by
          simp only [stepWire, List.length_append, List.length_singleton]
          omega
        rw [runWires_getD_prefix gs (stepWire init g) i hi', stepWire,
          getD_append_singleton, if_pos hi]
      · rw [if_neg hi, getD_of_ge init i (not_lt.mp hi)]
    | succ k =>
      have hk : k < gs.length := by simpa using hj
      have hidx : init.length + (k + 1) = (stepWire init g).length + k := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      change (runWires gs (stepWire init g)).getD (init.length + (k + 1)) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < init.length + (k + 1) then (runWires gs (stepWire init g)).getD i false else false)
      rw [hidx]
      exact ih (stepWire init g) k hk

private lemma gateOp_eval_map_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (inputs : List ℕ) (f1 f2 : ℕ → Bool) (hf : ∀ i, f1 i = true → f2 i = true) :
    op.eval (inputs.map f1) = true → op.eval (inputs.map f2) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro h1 i hi
    exact hf i (h1 i hi)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨f2 i, ⟨i, hi, rfl⟩, hf i hb⟩

private lemma runWires_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hlen : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (runWires gs x).getD i false = true → (runWires gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hmono g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hmono g' (by simp [hg'])
    have hlen' : (stepWire x g).length = (stepWire y g).length := by
      simp [stepWire, hlen]
    apply ih hgs (stepWire x g) (stepWire y g) hlen'
    intro i hi
    rw [stepWire, getD_append_singleton] at hi ⊢
    rw [hlen] at hi
    by_cases h1 : i < y.length
    · rw [if_pos h1] at hi ⊢
      exact hxy i hi
    · rw [if_neg h1] at hi ⊢
      by_cases h2 : i = y.length
      · rw [if_pos h2] at hi ⊢
        exact gateOp_eval_map_mono g.op hg g.inputs _ _ hxy hi
      · rw [if_neg h2] at hi
        cases hi

private def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

private lemma line_card : ∀ w : Fin 13, (line w).card = 4 := by
  decide

private lemma line_inter_card : ∀ w1 w2 : Fin 13, w1 ≠ w2 → (line w1 ∩ line w2).card = 1 := by
  decide

private lemma line_union_card (w1 w2 : Fin 13) (h : w1 ≠ w2) : (line w1 ∪ line w2).card = 7 := by
  have h1 := line_card w1
  have h2 := line_card w2
  have hi := line_inter_card w1 w2 h
  have hu := Finset.card_union_add_card_inter (line w1) (line w2)
  omega

private lemma line_union3_card (w1 w2 w3 : Fin 13)
    (h12 : w1 ≠ w2) (h13 : w1 ≠ w3) (h23 : w2 ≠ w3) :
    9 ≤ (line w1 ∪ line w2 ∪ line w3).card := by
  have hu12 := line_union_card w1 w2 h12
  have h3 := line_card w3
  have hi13 := line_inter_card w1 w3 h13
  have hi23 := line_inter_card w2 w3 h23
  have hinter : ((line w1 ∪ line w2) ∩ line w3).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    have hle := Finset.card_union_le (line w1 ∩ line w3) (line w2 ∩ line w3)
    omega
  have hu := Finset.card_union_add_card_inter (line w1 ∪ line w2) (line w3)
  omega

private lemma eq_of_subset_lines {T : Finset (Fin 13)} {w1 w2 : Fin 13}
    (hcard : 2 ≤ T.card) (h1 : T ⊆ line w1) (h2 : T ⊆ line w2) : w1 = w2 := by
  by_contra hne
  have hsub : T ⊆ line w1 ∩ line w2 := Finset.subset_inter h1 h2
  have hle : T.card ≤ (line w1 ∩ line w2).card := Finset.card_le_card hsub
  have hi := line_inter_card w1 w2 hne
  omega

private lemma lines_subset_card_le_one {T : Finset (Fin 13)} (hT : T.card ≤ 6) :
    (Finset.univ.filter fun l : Fin 13 => line l ⊆ T).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro l1 hl1 l2 hl2
  by_contra hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl1 hl2
  have hsub : line l1 ∪ line l2 ⊆ T := Finset.union_subset hl1 hl2
  have hle : (line l1 ∪ line l2).card ≤ T.card := Finset.card_le_card hsub
  have hu := line_union_card l1 l2 hne
  omega

private lemma lines_subset_card_le_two {T : Finset (Fin 13)} (hT : T.card ≤ 8) :
    (Finset.univ.filter fun l : Fin 13 => line l ⊆ T).card ≤ 2 := by
  by_contra hgt
  let F := Finset.univ.filter fun l : Fin 13 => line l ⊆ T
  have hF3 : 3 ≤ F.card := Nat.lt_of_not_ge hgt
  have hne1 : F.Nonempty := Finset.card_pos.mp (by omega)
  rcases hne1 with ⟨l1, hl1⟩
  have hcard1 : (F.erase l1).card = F.card - 1 := Finset.card_erase_of_mem hl1
  have hne2 : (F.erase l1).Nonempty := Finset.card_pos.mp (by omega)
  rcases hne2 with ⟨l2, hl2⟩
  have h21 : l2 ≠ l1 := (Finset.mem_erase.mp hl2).1
  have hl2F : l2 ∈ F := (Finset.mem_erase.mp hl2).2
  have hcard2 : ((F.erase l1).erase l2).card = (F.erase l1).card - 1 :=
    Finset.card_erase_of_mem hl2
  have hne3 : ((F.erase l1).erase l2).Nonempty := Finset.card_pos.mp (by omega)
  rcases hne3 with ⟨l3, hl3⟩
  have h32 : l3 ≠ l2 := (Finset.mem_erase.mp hl3).1
  have hl3' : l3 ∈ F.erase l1 := (Finset.mem_erase.mp hl3).2
  have h31 : l3 ≠ l1 := (Finset.mem_erase.mp hl3').1
  have hl3F : l3 ∈ F := (Finset.mem_erase.mp hl3').2
  have hsub1 : line l1 ⊆ T := (Finset.mem_filter.mp hl1).2
  have hsub2 : line l2 ⊆ T := (Finset.mem_filter.mp hl2F).2
  have hsub3 : line l3 ⊆ T := (Finset.mem_filter.mp hl3F).2
  have hsub : line l1 ∪ line l2 ∪ line l3 ⊆ T :=
    Finset.union_subset (Finset.union_subset hsub1 hsub2) hsub3
  have hle : (line l1 ∪ line l2 ∪ line l3).card ≤ T.card := Finset.card_le_card hsub
  have hu := line_union3_card l1 l2 l3 h21.symm h31.symm h32.symm
  omega

private def pt1 (v : Fin 13) : Fin 13 → Bool :=
  fun i => decide (i = v)

private def pt2 (u v : Fin 13) : Fin 13 → Bool :=
  fun i => decide (i = u ∨ i = v)

private lemma pt1_le_pt2_left (u v : Fin 13) :
    ∀ i : Fin 13, pt1 u i = true → pt2 u v i = true := by
  intro i hi
  simp only [pt1, pt2, decide_eq_true_eq] at hi ⊢
  exact Or.inl hi

private lemma pt1_le_pt2_right (u v : Fin 13) :
    ∀ i : Fin 13, pt1 v i = true → pt2 u v i = true := by
  intro i hi
  simp only [pt1, pt2, decide_eq_true_eq] at hi ⊢
  exact Or.inr hi

private lemma pt1_wt2 (v : Fin 13) :
    ∀ i j k : Fin 13, pt1 v i = true → pt1 v j = true → pt1 v k = true →
      i = j ∨ j = k ∨ i = k := by
  intro i j k hi hj _
  simp only [pt1, decide_eq_true_eq] at hi hj
  exact Or.inl (hi.trans hj.symm)

private lemma pt2_wt2 (u v : Fin 13) :
    ∀ i j k : Fin 13, pt2 u v i = true → pt2 u v j = true → pt2 u v k = true →
      i = j ∨ j = k ∨ i = k := by
  intro i j k hi hj hk
  simp only [pt2, decide_eq_true_eq] at hi hj hk
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;> simp

private def wval (gates : List Gate) (w : ℕ) (x : Fin 13 → Bool) : Bool :=
  (runWires gates (List.ofFn x)).getD w false

private def cval (gates : List Gate) (j i : ℕ) (x : Fin 13 → Bool) : Bool :=
  if i < 13 + j then wval gates i x else false

private def S (gates : List Gate) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun v => wval gates w (pt1 v) = true)

private def Sc (gates : List Gate) (j i : ℕ) : Finset (Fin 13) :=
  if i < 13 + j then S gates i else ∅

private def Safe (gates : List Gate) (w : ℕ) (l : Fin 13) : Prop :=
  S gates w ⊆ line l ∧ ∀ u v : Fin 13, u ∉ line l → v ∉ line l → wval gates w (pt2 u v) = false

private lemma mem_S_iff (gates : List Gate) (w : ℕ) (v : Fin 13) :
    v ∈ S gates w ↔ wval gates w (pt1 v) = true := by
  simp [S]

private lemma mem_Sc_iff (gates : List Gate) (j i : ℕ) (v : Fin 13) :
    v ∈ Sc gates j i ↔ cval gates j i (pt1 v) = true := by
  unfold Sc cval
  by_cases h : i < 13 + j
  · simp [h, mem_S_iff]
  · simp [h]

private lemma wval_mono (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin 13 → Bool) (hxy : ∀ i : Fin 13, x i = true → y i = true)
    (w : ℕ) (hx : wval gates w x = true) : wval gates w y = true := by
  apply runWires_mono gates hmono (List.ofFn x) (List.ofFn y) (by simp)
  · intro i hi
    rw [List.getD_eq_getElem?_getD] at hi ⊢
    by_cases hlt : i < 13
    · rw [List.getElem?_ofFn] at hi ⊢
      simp only [hlt, dite_true, Option.getD_some] at hi ⊢
      exact hxy ⟨i, hlt⟩ hi
    · rw [List.getElem?_eq_none (by simpa using not_lt.mp hlt)] at hi
      simp at hi
  · exact hx

private lemma wval_input (gates : List Gate) (w : ℕ) (hw : w < 13) (x : Fin 13 → Bool) :
    wval gates w x = x ⟨w, hw⟩ := by
  unfold wval
  have hlen : w < (List.ofFn x).length := by simpa using hw
  rw [runWires_getD_prefix gates (List.ofFn x) w hlen, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]
  simp [hw]

private lemma S_input_card (gates : List Gate) (w : ℕ) (hw : w < 13) :
    (S gates w).card = 1 := by
  have heq : S gates w = {⟨w, hw⟩} := by
    ext v
    simp only [mem_S_iff, wval_input gates w hw, pt1, decide_eq_true_eq, Finset.mem_singleton]
    exact eq_comm
  rw [heq, Finset.card_singleton]

private lemma wval_beyond (gates : List Gate) (w : ℕ) (hw : 13 + gates.length ≤ w)
    (x : Fin 13 → Bool) : wval gates w x = false := by
  unfold wval
  apply getD_of_ge
  rw [runWires_length, List.length_ofFn]
  exact hw

private lemma S_beyond (gates : List Gate) (w : ℕ) (hw : 13 + gates.length ≤ w) :
    S gates w = ∅ := by
  ext v
  simp [mem_S_iff, wval_beyond gates w hw]

private lemma S_ge_two_bounds (gates : List Gate) (w : ℕ) (hcard : 2 ≤ (S gates w).card) :
    13 ≤ w ∧ w < 13 + gates.length := by
  constructor
  · by_contra hlt
    have h1 := S_input_card gates w (not_le.mp hlt)
    omega
  · by_contra hge
    have h0 := S_beyond gates w (not_lt.mp hge)
    rw [h0, Finset.card_empty] at hcard
    omega

private lemma wval_gate (gates : List Gate) (j : ℕ) (hj : j < gates.length) (x : Fin 13 → Bool) :
    wval gates (13 + j) x =
      (gates[j]).op.eval ((gates[j]).inputs.map fun i => cval gates j i x) := by
  unfold wval cval
  have h := runWires_getD_gate gates (List.ofFn x) j hj
  rwa [List.length_ofFn] at h

private lemma Sc_eq_S_of_card_pos (gates : List Gate) (j i : ℕ) (h : 0 < (Sc gates j i).card) :
    i < 13 + j ∧ Sc gates j i = S gates i := by
  unfold Sc at h ⊢
  by_cases hi : i < 13 + j
  · simp [hi]
  · simp [hi] at h

private lemma and_safe_subset (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w a b : ℕ) (l : Fin 13)
    (heq : ∀ x : Fin 13 → Bool, wval gates w x = (wval gates a x && wval gates b x))
    (hsafe : Safe gates w l) :
    S gates a ⊆ line l ∨ S gates b ⊆ line l := by
  by_contra hnot
  push_neg at hnot
  rcases Finset.not_subset.mp hnot.1 with ⟨u, huS, huL⟩
  rcases Finset.not_subset.mp hnot.2 with ⟨v, hvS, hvL⟩
  have hua : wval gates a (pt2 u v) = true :=
    wval_mono gates hmono (pt1 u) (pt2 u v) (pt1_le_pt2_left u v) a
      ((mem_S_iff gates a u).mp huS)
  have hvb : wval gates b (pt2 u v) = true :=
    wval_mono gates hmono (pt1 v) (pt2 u v) (pt1_le_pt2_right u v) b
      ((mem_S_iff gates b v).mp hvS)
  have htrue : wval gates w (pt2 u v) = true := by
    rw [heq, hua, hvb]
    rfl
  have hfalse : wval gates w (pt2 u v) = false := hsafe.2 u v huL hvL
  rw [htrue] at hfalse
  cases hfalse

private lemma disjoint_diff_of_triple (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (f1 f2 f3 : ℕ) (l : Fin 13)
    (h3 : (S gates f3 \ line l).Nonempty)
    (hforbid : ∀ u v : Fin 13, u ∉ line l → v ∉ line l →
      ¬ (wval gates f1 (pt2 u v) = true ∧ wval gates f2 (pt2 u v) = true ∧
         wval gates f3 (pt2 u v) = true)) :
    Disjoint (S gates f1 \ line l) (S gates f2 \ line l) := by
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  rcases h3 with ⟨y, hy⟩
  rw [Finset.mem_sdiff] at hz1 hz2 hy
  have hf1 : wval gates f1 (pt2 z y) = true :=
    wval_mono gates hmono (pt1 z) (pt2 z y) (pt1_le_pt2_left z y) f1
      ((mem_S_iff gates f1 z).mp hz1.1)
  have hf2 : wval gates f2 (pt2 z y) = true :=
    wval_mono gates hmono (pt1 z) (pt2 z y) (pt1_le_pt2_left z y) f2
      ((mem_S_iff gates f2 z).mp hz2.1)
  have hf3 : wval gates f3 (pt2 z y) = true :=
    wval_mono gates hmono (pt1 y) (pt2 z y) (pt1_le_pt2_right z y) f3
      ((mem_S_iff gates f3 y).mp hy.1)
  exact hforbid z y hz1.2 hy.2 ⟨hf1, hf2, hf3⟩

private def Own (gates : List Gate) (l : Fin 13) : Finset ℕ :=
  (Finset.range gates.length).filter
    (fun j => 2 ≤ (S gates (13 + j)).card ∧ S gates (13 + j) ⊆ line l)

private def Outside (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter
    (fun j => ∀ l : Fin 13, ¬ (2 ≤ (S gates (13 + j)).card ∧ S gates (13 + j) ⊆ line l))

private lemma mem_Own_iff (gates : List Gate) (l : Fin 13) (j : ℕ) :
    j ∈ Own gates l ↔ j < gates.length ∧ 2 ≤ (S gates (13 + j)).card ∧ S gates (13 + j) ⊆ line l := by
  simp [Own, and_assoc]

private lemma mem_Outside_iff (gates : List Gate) (j : ℕ) :
    j ∈ Outside gates ↔
      j < gates.length ∧ ∀ l : Fin 13, ¬ (2 ≤ (S gates (13 + j)).card ∧ S gates (13 + j) ⊆ line l) := by
  simp [Outside]

private lemma own_add_outside_le (gates : List Gate) :
    (∑ l : Fin 13, (Own gates l).card) + (Outside gates).card ≤ gates.length := by
  have hdisj_own : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint (Own gates) := by
    intro l1 _ l2 _ hne
    change Disjoint (Own gates l1) (Own gates l2)
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    rw [mem_Own_iff] at hj1 hj2
    exact hne (eq_of_subset_lines hj1.2.1 hj1.2.2 hj2.2.2)
  have hdisj_out : Disjoint (Finset.univ.biUnion (Own gates)) (Outside gates) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    rcases Finset.mem_biUnion.mp hj1 with ⟨l, _, hjl⟩
    rw [mem_Own_iff] at hjl
    rw [mem_Outside_iff] at hj2
    exact hj2.2 l ⟨hjl.2.1, hjl.2.2⟩
  have hsub : Finset.univ.biUnion (Own gates) ∪ Outside gates ⊆ Finset.range gates.length := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj1 | hj2
    · rcases Finset.mem_biUnion.mp hj1 with ⟨l, _, hjl⟩
      exact Finset.mem_range.mpr ((mem_Own_iff gates l j).mp hjl).1
    · exact Finset.mem_range.mpr ((mem_Outside_iff gates j).mp hj2).1
  calc
    (∑ l : Fin 13, (Own gates l).card) + (Outside gates).card
      = (Finset.univ.biUnion (Own gates)).card + (Outside gates).card := by
          rw [Finset.card_biUnion hdisj_own]
    _ = (Finset.univ.biUnion (Own gates) ∪ Outside gates).card := by
          rw [Finset.card_union_of_disjoint hdisj_out]
    _ ≤ (Finset.range gates.length).card := Finset.card_le_card hsub
    _ = gates.length := Finset.card_range _

private lemma outside_of_strict_superset (gates : List Gate) (l : Fin 13) (w : ℕ)
    (hw : w < 13 + gates.length) (hsub : line l ⊆ S gates w) (hnot : ¬ S gates w ⊆ line l) :
    13 ≤ w ∧ (w - 13) ∈ Outside gates ∧ 5 ≤ (S gates w).card ∧ (S gates w \ line l).Nonempty := by
  have hcard4 : 4 ≤ (S gates w).card := by
    have hle := Finset.card_le_card hsub
    rw [line_card l] at hle
    exact hle
  have h13 : 13 ≤ w := (S_ge_two_bounds gates w (by omega)).1
  have hlt : w - 13 < gates.length := by omega
  have hadd : 13 + (w - 13) = w := by omega
  have hout : (w - 13) ∈ Outside gates := by
    rw [mem_Outside_iff]
    refine ⟨hlt, ?_⟩
    intro l' ⟨_, hsub'⟩
    rw [hadd] at hsub'
    have hll' : line l ⊆ line l' := hsub.trans hsub'
    have heq : l = l' := eq_of_subset_lines (by rw [line_card]; omega) (Finset.Subset.refl _) hll'
    subst heq
    exact hnot hsub'
  rcases Finset.not_subset.mp hnot with ⟨z, hzS, hzL⟩
  have hne : (S gates w \ line l).Nonempty := ⟨z, Finset.mem_sdiff.mpr ⟨hzS, hzL⟩⟩
  have hcard5 : 5 ≤ (S gates w).card := by
    have hsd := Finset.card_sdiff_add_card_eq_card hsub
    have hpos : 1 ≤ (S gates w \ line l).card := Finset.card_pos.mpr hne
    rw [line_card l] at hsd
    omega
  exact ⟨h13, hout, hcard5, hne⟩

private lemma safe_has_pred (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (l : Fin 13) (j : ℕ) (hj : j < gates.length)
    (hcard : 3 ≤ (S gates (13 + j)).card) (hsafe : Safe gates (13 + j) l) :
    ∃ j' < j, j' ∈ Own gates l := by
  have hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hgates g hg).1
  have hgj := hgates (gates[j]) (List.getElem_mem hj)
  rcases hgj with ⟨hop, hlen⟩
  match hin : (gates[j]).inputs with
  | [] =>
    rcases hop with hand | hor
    · have hall : S gates (13 + j) = Finset.univ := by
        ext v
        simp [mem_S_iff, wval_gate gates j hj, hin, hand, GateOp.eval]
      have hle : (S gates (13 + j)).card ≤ (line l).card := Finset.card_le_card hsafe.1
      rw [hall, Finset.card_univ, Fintype.card_fin, line_card l] at hle
      omega
    · have hemp : S gates (13 + j) = ∅ := by
        ext v
        simp [mem_S_iff, wval_gate gates j hj, hin, hor, GateOp.eval]
      rw [hemp, Finset.card_empty] at hcard
      omega
  | [a] =>
    have hSeq : S gates (13 + j) = Sc gates j a := by
      ext v
      rw [mem_S_iff, mem_Sc_iff, wval_gate gates j hj, hin]
      rcases hop with h | h <;> simp [h, GateOp.eval]
    rw [hSeq] at hcard
    obtain ⟨ha, hSc⟩ := Sc_eq_S_of_card_pos gates j a (by omega)
    rw [hSc] at hcard hSeq
    have h13 : 13 ≤ a := (S_ge_two_bounds gates a (by omega)).1
    refine ⟨a - 13, by omega, ?_⟩
    rw [mem_Own_iff]
    have hadd : 13 + (a - 13) = a := by omega
    rw [hadd]
    exact ⟨by omega, by omega, hSeq ▸ hsafe.1⟩
  | [a, b] =>
    rcases hop with hand | hor
    · have hSeq : S gates (13 + j) = Sc gates j a ∩ Sc gates j b := by
        ext v
        simp [mem_S_iff, mem_Sc_iff, wval_gate gates j hj, hin, hand, GateOp.eval]
      have hsubA : S gates (13 + j) ⊆ Sc gates j a := hSeq ▸ Finset.inter_subset_left
      have hsubB : S gates (13 + j) ⊆ Sc gates j b := hSeq ▸ Finset.inter_subset_right
      have hcA : 3 ≤ (Sc gates j a).card := le_trans hcard (Finset.card_le_card hsubA)
      have hcB : 3 ≤ (Sc gates j b).card := le_trans hcard (Finset.card_le_card hsubB)
      obtain ⟨ha, hScA⟩ := Sc_eq_S_of_card_pos gates j a (by omega)
      obtain ⟨hb, hScB⟩ := Sc_eq_S_of_card_pos gates j b (by omega)
      rw [hScA] at hcA
      rw [hScB] at hcB
      have hval : ∀ x : Fin 13 → Bool,
          wval gates (13 + j) x = (wval gates a x && wval gates b x) := by
        intro x
        simp [wval_gate gates j hj, hin, hand, GateOp.eval, cval, ha, hb]
      rcases and_safe_subset gates hmono (13 + j) a b l hval hsafe with hSa | hSb
      · have h13 : 13 ≤ a := (S_ge_two_bounds gates a (by omega)).1
        refine ⟨a - 13, by omega, ?_⟩
        rw [mem_Own_iff]
        have hadd : 13 + (a - 13) = a := by omega
        rw [hadd]
        exact ⟨by omega, by omega, hSa⟩
      · have h13 : 13 ≤ b := (S_ge_two_bounds gates b (by omega)).1
        refine ⟨b - 13, by omega, ?_⟩
        rw [mem_Own_iff]
        have hadd : 13 + (b - 13) = b := by omega
        rw [hadd]
        exact ⟨by omega, by omega, hSb⟩
    · have hSeq : S gates (13 + j) = Sc gates j a ∪ Sc gates j b := by
        ext v
        simp [mem_S_iff, mem_Sc_iff, wval_gate gates j hj, hin, hor, GateOp.eval]
      have hle := Finset.card_union_le (Sc gates j a) (Sc gates j b)
      rw [← hSeq] at hle
      by_cases hcA : 2 ≤ (Sc gates j a).card
      · obtain ⟨ha, hScA⟩ := Sc_eq_S_of_card_pos gates j a (by omega)
        rw [hScA] at hcA
        have h13 : 13 ≤ a := (S_ge_two_bounds gates a hcA).1
        have hsub : S gates a ⊆ line l := by
          have hs : Sc gates j a ⊆ S gates (13 + j) := hSeq ▸ Finset.subset_union_left
          rw [hScA] at hs
          exact hs.trans hsafe.1
        refine ⟨a - 13, by omega, ?_⟩
        rw [mem_Own_iff]
        have hadd : 13 + (a - 13) = a := by omega
        rw [hadd]
        exact ⟨by omega, hcA, hsub⟩
      · have hcB : 2 ≤ (Sc gates j b).card := by omega
        obtain ⟨hb, hScB⟩ := Sc_eq_S_of_card_pos gates j b (by omega)
        rw [hScB] at hcB
        have h13 : 13 ≤ b := (S_ge_two_bounds gates b hcB).1
        have hsub : S gates b ⊆ line l := by
          have hs : Sc gates j b ⊆ S gates (13 + j) := hSeq ▸ Finset.subset_union_right
          rw [hScB] at hs
          exact hs.trans hsafe.1
        refine ⟨b - 13, by omega, ?_⟩
        rw [mem_Own_iff]
        have hadd : 13 + (b - 13) = b := by omega
        rw [hadd]
        exact ⟨by omega, hcB, hsub⟩
  | _ :: _ :: _ :: _ =>
    rw [hin] at hlen
    simp at hlen

private lemma output_info (gates : List Gate) (out : Fin 13 → ℕ)
    (heval : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ line w, x v = true))
    (l : Fin 13) :
    ∃ j_l < gates.length, 13 + j_l = out l ∧ S gates (13 + j_l) = line l ∧
      Safe gates (13 + j_l) l ∧ j_l ∈ Own gates l := by
  have hS : S gates (out l) = line l := by
    ext v
    rw [mem_S_iff]
    change Circuit.eval ⟨gates, out l⟩ (List.ofFn (pt1 v)) = true ↔ v ∈ line l
    rw [heval l (pt1 v) (pt1_wt2 v)]
    simp [pt1]
  have hsafe : Safe gates (out l) l := by
    refine ⟨hS ▸ Finset.Subset.refl _, ?_⟩
    intro u v hu hv
    change Circuit.eval ⟨gates, out l⟩ (List.ofFn (pt2 u v)) = false
    rw [heval l (pt2 u v) (pt2_wt2 u v)]
    rw [decide_eq_false_iff_not]
    rintro ⟨z, hzL, hz⟩
    simp only [pt2, decide_eq_true_eq] at hz
    rcases hz with rfl | rfl
    · exact hu hzL
    · exact hv hzL
  have hbounds := S_ge_two_bounds gates (out l) (by rw [hS, line_card l]; omega)
  refine ⟨out l - 13, by omega, by omega, ?_, ?_, ?_⟩
  · have hadd : 13 + (out l - 13) = out l := by omega
    rw [hadd]
    exact hS
  · have hadd : 13 + (out l - 13) = out l := by omega
    rw [hadd]
    exact hsafe
  · rw [mem_Own_iff]
    have hadd : 13 + (out l - 13) = out l := by omega
    rw [hadd, hS, line_card l]
    exact ⟨by omega, by omega, Finset.Subset.refl _⟩

private lemma own_card_ge_two (gates : List Gate) (out : Fin 13 → ℕ)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ line w, x v = true))
    (l : Fin 13) : 2 ≤ (Own gates l).card := by
  obtain ⟨j_l, hj_l, _, hS, hsafe, hmem⟩ := output_info gates out heval l
  have hcard4 : 3 ≤ (S gates (13 + j_l)).card := by rw [hS, line_card l]; omega
  obtain ⟨j', hj'lt, hj'mem⟩ := safe_has_pred gates hgates l j_l hj_l hcard4 hsafe
  have hsub : ({j', j_l} : Finset ℕ) ⊆ Own gates l := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> assumption
  have hpair : ({j', j_l} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
  have hle := Finset.card_le_card hsub
  omega

private lemma own_card_eq_two_triple (gates : List Gate) (out : Fin 13 → ℕ)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ line w, x v = true))
    (l : Fin 13) (hcard2 : (Own gates l).card = 2) :
    ∃ b d c : ℕ,
      b ∈ Outside gates ∧ d ∈ Outside gates ∧ c ∈ Outside gates ∧
      b ≠ d ∧ b ≠ c ∧ d ≠ c ∧
      line l ⊆ S gates (13 + b) ∧ line l ⊆ S gates (13 + d) ∧ line l ⊆ S gates (13 + c) ∧
      5 ≤ (S gates (13 + b)).card ∧ 5 ≤ (S gates (13 + d)).card ∧ 5 ≤ (S gates (13 + c)).card ∧
      (S gates (13 + b)).card + (S gates (13 + d)).card + (S gates (13 + c)).card ≤ 21 := by
  have hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hgates g hg).1
  obtain ⟨j_l, hj_l, _, hSl, hsafe_l, hmem_l⟩ := output_info gates out heval l
  have hcard_l : 3 ≤ (S gates (13 + j_l)).card := by rw [hSl, line_card l]; omega
  obtain ⟨j', hj'lt, hj'mem⟩ := safe_has_pred gates hgates l j_l hj_l hcard_l hsafe_l
  have hj'_lt_len : j' < gates.length := by omega
  have hOwn_eq : Own gates l = {j', j_l} := by
    have hsub : ({j', j_l} : Finset ℕ) ⊆ Own gates l := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption
    have hpair : ({j', j_l} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hlt_jl_eq : ∀ k ∈ Own gates l, k < j_l → k = j' := by
    intro k hk hlt
    rw [hOwn_eq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · rfl
    · omega
  have hno_lt_j' : ∀ k < j', k ∉ Own gates l := by
    intro k hlt hk
    rw [hOwn_eq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> omega
  have hstep1 : ∃ c : ℕ, c ∈ Outside gates ∧ line l ⊆ S gates (13 + c) ∧
      5 ≤ (S gates (13 + c)).card ∧ (S gates (13 + c) \ line l).Nonempty ∧
      S gates (13 + j') = line l ∧
      ∀ x : Fin 13 → Bool,
        wval gates (13 + j_l) x = (wval gates (13 + j') x && wval gates (13 + c) x) := by
    rcases hgates (gates[j_l]) (List.getElem_mem hj_l) with ⟨hop, hlen⟩
    match hin : (gates[j_l]).inputs with
    | [] =>
      rcases hop with hand | hor
      · have hall : S gates (13 + j_l) = Finset.univ := by
          ext v
          simp [mem_S_iff, wval_gate gates j_l hj_l, hin, hand, GateOp.eval]
        have hc : (S gates (13 + j_l)).card = 13 := by simp [hall]
        rw [hSl, line_card l] at hc
        omega
      · have hemp : S gates (13 + j_l) = ∅ := by
          ext v
          simp [mem_S_iff, wval_gate gates j_l hj_l, hin, hor, GateOp.eval]
        have hc : (S gates (13 + j_l)).card = 0 := by simp [hemp]
        rw [hSl, line_card l] at hc
        omega
    | [a] =>
      have hval : ∀ x : Fin 13 → Bool, wval gates (13 + j_l) x = cval gates j_l a x := by
        intro x
        rw [wval_gate gates j_l hj_l, hin]
        rcases hop with h | h <;> simp [h, GateOp.eval]
      have hSeq : S gates (13 + j_l) = Sc gates j_l a := by
        ext v
        rw [mem_S_iff, mem_Sc_iff, hval]
      rw [hSl] at hSeq
      obtain ⟨ha, hSc⟩ := Sc_eq_S_of_card_pos gates j_l a (by rw [← hSeq, line_card l]; omega)
      rw [hSc] at hSeq
      have h13 : 13 ≤ a := (S_ge_two_bounds gates a (by rw [← hSeq, line_card l]; omega)).1
      have haOwn : (a - 13) ∈ Own gates l := by
        rw [mem_Own_iff]
        have hadd : 13 + (a - 13) = a := by omega
        rw [hadd, ← hSeq, line_card l]
        exact ⟨by omega, by omega, Finset.Subset.refl _⟩
      have heq_j' : a - 13 = j' := hlt_jl_eq (a - 13) haOwn (by omega)
      have ha_eq : a = 13 + j' := by omega
      have hsafe_j' : Safe gates (13 + j') l := by
        refine ⟨by rw [← ha_eq, ← hSeq], ?_⟩
        intro u v hu hv
        have h1 := hval (pt2 u v)
        rw [cval, if_pos ha, ha_eq] at h1
        rw [← h1]
        exact hsafe_l.2 u v hu hv
      have hc' : 3 ≤ (S gates (13 + j')).card := by rw [← ha_eq, ← hSeq, line_card l]; omega
      obtain ⟨k, hklt, hkmem⟩ := safe_has_pred gates hgates l j' hj'_lt_len hc' hsafe_j'
      exact False.elim (hno_lt_j' k hklt hkmem)
    | [a, b] =>
      rcases hop with hand | hor
      · have hSeq : line l = Sc gates j_l a ∩ Sc gates j_l b := by
          rw [← hSl]
          ext v
          simp [mem_S_iff, mem_Sc_iff, wval_gate gates j_l hj_l, hin, hand, GateOp.eval]
        have hsubA : line l ⊆ Sc gates j_l a := hSeq ▸ Finset.inter_subset_left
        have hsubB : line l ⊆ Sc gates j_l b := hSeq ▸ Finset.inter_subset_right
        obtain ⟨ha, hScA⟩ := Sc_eq_S_of_card_pos gates j_l a
          (by have := Finset.card_le_card hsubA; rw [line_card l] at this; omega)
        obtain ⟨hb, hScB⟩ := Sc_eq_S_of_card_pos gates j_l b
          (by have := Finset.card_le_card hsubB; rw [line_card l] at this; omega)
        rw [hScA] at hsubA
        rw [hScB] at hsubB
        have hval_ab : ∀ x : Fin 13 → Bool,
            wval gates (13 + j_l) x = (wval gates a x && wval gates b x) := by
          intro x
          simp [wval_gate gates j_l hj_l, hin, hand, GateOp.eval, cval, ha, hb]
        have huv : ∃ u v : ℕ, u < 13 + j_l ∧ v < 13 + j_l ∧
            line l ⊆ S gates u ∧ line l ⊆ S gates v ∧ S gates u ⊆ line l ∧
            ∀ x : Fin 13 → Bool,
              wval gates (13 + j_l) x = (wval gates u x && wval gates v x) := by
          rcases and_safe_subset gates hmono (13 + j_l) a b l hval_ab hsafe_l with hSa | hSb
          · exact ⟨a, b, ha, hb, hsubA, hsubB, hSa, hval_ab⟩
          · refine ⟨b, a, hb, ha, hsubB, hsubA, hSb, ?_⟩
            intro x
            rw [hval_ab x, Bool.and_comm]
        rcases huv with ⟨u, v, hu, hv, hlu, hlv, hul, hval_uv⟩
        have hSu : S gates u = line l := Finset.Subset.antisymm hul hlu
        have hu13 : 13 ≤ u := (S_ge_two_bounds gates u (by rw [hSu, line_card l]; omega)).1
        have huOwn : (u - 13) ∈ Own gates l := by
          rw [mem_Own_iff]
          have hadd : 13 + (u - 13) = u := by omega
          rw [hadd, hSu, line_card l]
          exact ⟨by omega, by omega, Finset.Subset.refl _⟩
        have hu_j' : u - 13 = j' := hlt_jl_eq (u - 13) huOwn (by omega)
        have hu_eq : u = 13 + j' := by omega
        have hv_not_sub : ¬ S gates v ⊆ line l := by
          intro hvl
          have hSv : S gates v = line l := Finset.Subset.antisymm hvl hlv
          have hv13 : 13 ≤ v := (S_ge_two_bounds gates v (by rw [hSv, line_card l]; omega)).1
          have hvOwn : (v - 13) ∈ Own gates l := by
            rw [mem_Own_iff]
            have hadd : 13 + (v - 13) = v := by omega
            rw [hadd, hSv, line_card l]
            exact ⟨by omega, by omega, Finset.Subset.refl _⟩
          have hv_j' : v - 13 = j' := hlt_jl_eq (v - 13) hvOwn (by omega)
          have hv_eq : v = 13 + j' := by omega
          have hsafe_j' : Safe gates (13 + j') l := by
            refine ⟨by rw [← hu_eq, hSu], ?_⟩
            intro x1 x2 hx1 hx2
            have h1 := hval_uv (pt2 x1 x2)
            rw [hu_eq, hv_eq, Bool.and_self] at h1
            rw [← h1]
            exact hsafe_l.2 x1 x2 hx1 hx2
          have hc' : 3 ≤ (S gates (13 + j')).card := by rw [← hu_eq, hSu, line_card l]; omega
          obtain ⟨k, hklt, hkmem⟩ := safe_has_pred gates hgates l j' hj'_lt_len hc' hsafe_j'
          exact hno_lt_j' k hklt hkmem
        obtain ⟨hv13, hcOut, hc5, hcNe⟩ :=
          outside_of_strict_superset gates l v (by omega) hlv hv_not_sub
        have hv_add : 13 + (v - 13) = v := by omega
        refine ⟨v - 13, hcOut, by rw [hv_add]; exact hlv, by rw [hv_add]; exact hc5,
          by rw [hv_add]; exact hcNe, by rw [← hu_eq]; exact hSu, ?_⟩
        intro x
        rw [← hu_eq, hv_add]
        exact hval_uv x
      · have hval : ∀ x : Fin 13 → Bool,
            wval gates (13 + j_l) x = (cval gates j_l a x || cval gates j_l b x) := by
          intro x
          simp [wval_gate gates j_l hj_l, hin, hor, GateOp.eval]
        have hSeq : line l = Sc gates j_l a ∪ Sc gates j_l b := by
          rw [← hSl]
          ext v
          rw [mem_S_iff, Finset.mem_union, mem_Sc_iff, mem_Sc_iff, hval, Bool.or_eq_true]
        have hsubA : Sc gates j_l a ⊆ line l := hSeq ▸ Finset.subset_union_left
        have hsubB : Sc gates j_l b ⊆ line l := hSeq ▸ Finset.subset_union_right
        have hsum := Finset.card_union_le (Sc gates j_l a) (Sc gates j_l b)
        rw [← hSeq, line_card l] at hsum
        by_cases hcA : 3 ≤ (Sc gates j_l a).card
        · obtain ⟨ha, hScA⟩ := Sc_eq_S_of_card_pos gates j_l a (by omega)
          rw [hScA] at hcA hsubA
          have h13 : 13 ≤ a := (S_ge_two_bounds gates a (by omega)).1
          have haOwn : (a - 13) ∈ Own gates l := by
            rw [mem_Own_iff]
            have hadd : 13 + (a - 13) = a := by omega
            rw [hadd]
            exact ⟨by omega, by omega, hsubA⟩
          have ha_eq : a = 13 + j' := by
            have := hlt_jl_eq (a - 13) haOwn (by omega)
            omega
          have hsafe_j' : Safe gates (13 + j') l := by
            refine ⟨by rw [← ha_eq]; exact hsubA, ?_⟩
            intro u v hu hv
            have hf := hsafe_l.2 u v hu hv
            rw [hval, cval, if_pos ha, ha_eq] at hf
            exact (Bool.or_eq_false_iff.mp hf).1
          obtain ⟨k, hklt, hkmem⟩ :=
            safe_has_pred gates hgates l j' hj'_lt_len (by rw [← ha_eq]; exact hcA) hsafe_j'
          exact False.elim (hno_lt_j' k hklt hkmem)
        · by_cases hcB : 3 ≤ (Sc gates j_l b).card
          · obtain ⟨hb, hScB⟩ := Sc_eq_S_of_card_pos gates j_l b (by omega)
            rw [hScB] at hcB hsubB
            have h13 : 13 ≤ b := (S_ge_two_bounds gates b (by omega)).1
            have hbOwn : (b - 13) ∈ Own gates l := by
              rw [mem_Own_iff]
              have hadd : 13 + (b - 13) = b := by omega
              rw [hadd]
              exact ⟨by omega, by omega, hsubB⟩
            have hb_eq : b = 13 + j' := by
              have := hlt_jl_eq (b - 13) hbOwn (by omega)
              omega
            have hsafe_j' : Safe gates (13 + j') l := by
              refine ⟨by rw [← hb_eq]; exact hsubB, ?_⟩
              intro u v hu hv
              have hf := hsafe_l.2 u v hu hv
              rw [hval] at hf
              have hcb : cval gates j_l b (pt2 u v) = wval gates (13 + j') (pt2 u v) := by
                rw [cval, if_pos hb, hb_eq]
              rw [hcb] at hf
              exact (Bool.or_eq_false_iff.mp hf).2
            obtain ⟨k, hklt, hkmem⟩ :=
              safe_has_pred gates hgates l j' hj'_lt_len (by rw [← hb_eq]; exact hcB) hsafe_j'
            exact False.elim (hno_lt_j' k hklt hkmem)
          · have hcA2 : (Sc gates j_l a).card = 2 := by omega
            have hcB2 : (Sc gates j_l b).card = 2 := by omega
            obtain ⟨ha, hScA⟩ := Sc_eq_S_of_card_pos gates j_l a (by omega)
            obtain ⟨hb, hScB⟩ := Sc_eq_S_of_card_pos gates j_l b (by omega)
            rw [hScA] at hcA2 hsubA
            rw [hScB] at hcB2 hsubB
            have ha13 : 13 ≤ a := (S_ge_two_bounds gates a (by omega)).1
            have hb13 : 13 ≤ b := (S_ge_two_bounds gates b (by omega)).1
            have haOwn : (a - 13) ∈ Own gates l := by
              rw [mem_Own_iff]
              have hadd : 13 + (a - 13) = a := by omega
              rw [hadd]
              exact ⟨by omega, by omega, hsubA⟩
            have hbOwn : (b - 13) ∈ Own gates l := by
              rw [mem_Own_iff]
              have hadd : 13 + (b - 13) = b := by omega
              rw [hadd]
              exact ⟨by omega, by omega, hsubB⟩
            have hab : a = b := by
              have ha' := hlt_jl_eq (a - 13) haOwn (by omega)
              have hb' := hlt_jl_eq (b - 13) hbOwn (by omega)
              omega
            subst hab
            rw [Finset.union_idempotent, hScA] at hSeq
            have h4 : (line l).card = 2 := by rw [hSeq, hcA2]
            rw [line_card l] at h4
            omega
    | _ :: _ :: _ :: _ =>
      rw [hin] at hlen
      simp at hlen
  rcases hstep1 with ⟨c, hcOut, hlc, hc5, hcNe, hSj', hval_jl⟩
  have hstep2 : ∃ b d : ℕ, b ∈ Outside gates ∧ d ∈ Outside gates ∧
      line l ⊆ S gates (13 + b) ∧ line l ⊆ S gates (13 + d) ∧
      5 ≤ (S gates (13 + b)).card ∧ 5 ≤ (S gates (13 + d)).card ∧
      (S gates (13 + b) \ line l).Nonempty ∧ (S gates (13 + d) \ line l).Nonempty ∧
      ∀ x : Fin 13 → Bool,
        wval gates (13 + j') x = (wval gates (13 + b) x && wval gates (13 + d) x) := by
    rcases hgates (gates[j']) (List.getElem_mem hj'_lt_len) with ⟨hop, hlen⟩
    match hin : (gates[j']).inputs with
    | [] =>
      rcases hop with hand | hor
      · have hall : S gates (13 + j') = Finset.univ := by
          ext v
          simp [mem_S_iff, wval_gate gates j' hj'_lt_len, hin, hand, GateOp.eval]
        have hc : (S gates (13 + j')).card = 13 := by simp [hall]
        rw [hSj', line_card l] at hc
        omega
      · have hemp : S gates (13 + j') = ∅ := by
          ext v
          simp [mem_S_iff, wval_gate gates j' hj'_lt_len, hin, hor, GateOp.eval]
        have hc : (S gates (13 + j')).card = 0 := by simp [hemp]
        rw [hSj', line_card l] at hc
        omega
    | [p] =>
      have hSeq : S gates (13 + j') = Sc gates j' p := by
        ext v
        rw [mem_S_iff, mem_Sc_iff, wval_gate gates j' hj'_lt_len, hin]
        rcases hop with h | h <;> simp [h, GateOp.eval]
      rw [hSj'] at hSeq
      obtain ⟨hp, hScp⟩ := Sc_eq_S_of_card_pos gates j' p (by rw [← hSeq, line_card l]; omega)
      rw [hScp] at hSeq
      have hp13 : 13 ≤ p := (S_ge_two_bounds gates p (by rw [← hSeq, line_card l]; omega)).1
      have hpOwn : (p - 13) ∈ Own gates l := by
        rw [mem_Own_iff]
        have hadd : 13 + (p - 13) = p := by omega
        rw [hadd, ← hSeq, line_card l]
        exact ⟨by omega, by omega, Finset.Subset.refl _⟩
      exact False.elim (hno_lt_j' (p - 13) (by omega) hpOwn)
    | [p, q] =>
      rcases hop with hand | hor
      · have hSeq : line l = Sc gates j' p ∩ Sc gates j' q := by
          rw [← hSj']
          ext v
          simp [mem_S_iff, mem_Sc_iff, wval_gate gates j' hj'_lt_len, hin, hand, GateOp.eval]
        have hsubP : line l ⊆ Sc gates j' p := hSeq ▸ Finset.inter_subset_left
        have hsubQ : line l ⊆ Sc gates j' q := hSeq ▸ Finset.inter_subset_right
        obtain ⟨hp, hScP⟩ := Sc_eq_S_of_card_pos gates j' p
          (by have := Finset.card_le_card hsubP; rw [line_card l] at this; omega)
        obtain ⟨hq, hScQ⟩ := Sc_eq_S_of_card_pos gates j' q
          (by have := Finset.card_le_card hsubQ; rw [line_card l] at this; omega)
        rw [hScP] at hsubP
        rw [hScQ] at hsubQ
        have hp_not : ¬ S gates p ⊆ line l := by
          intro hpl
          have hSp : S gates p = line l := Finset.Subset.antisymm hpl hsubP
          have hp13 : 13 ≤ p := (S_ge_two_bounds gates p (by rw [hSp, line_card l]; omega)).1
          have hpOwn : (p - 13) ∈ Own gates l := by
            rw [mem_Own_iff]
            have hadd : 13 + (p - 13) = p := by omega
            rw [hadd, hSp, line_card l]
            exact ⟨by omega, by omega, Finset.Subset.refl _⟩
          exact hno_lt_j' (p - 13) (by omega) hpOwn
        have hq_not : ¬ S gates q ⊆ line l := by
          intro hql
          have hSq : S gates q = line l := Finset.Subset.antisymm hql hsubQ
          have hq13 : 13 ≤ q := (S_ge_two_bounds gates q (by rw [hSq, line_card l]; omega)).1
          have hqOwn : (q - 13) ∈ Own gates l := by
            rw [mem_Own_iff]
            have hadd : 13 + (q - 13) = q := by omega
            rw [hadd, hSq, line_card l]
            exact ⟨by omega, by omega, Finset.Subset.refl _⟩
          exact hno_lt_j' (q - 13) (by omega) hqOwn
        obtain ⟨hp13, hbOut, hb5, hbNe⟩ :=
          outside_of_strict_superset gates l p (by omega) hsubP hp_not
        obtain ⟨hq13, hdOut, hd5, hdNe⟩ :=
          outside_of_strict_superset gates l q (by omega) hsubQ hq_not
        have hp_add : 13 + (p - 13) = p := by omega
        have hq_add : 13 + (q - 13) = q := by omega
        refine ⟨p - 13, q - 13, hbOut, hdOut,
          by rw [hp_add]; exact hsubP, by rw [hq_add]; exact hsubQ,
          by rw [hp_add]; exact hb5, by rw [hq_add]; exact hd5,
          by rw [hp_add]; exact hbNe, by rw [hq_add]; exact hdNe, ?_⟩
        intro x
        rw [hp_add, hq_add]
        simp [wval_gate gates j' hj'_lt_len, hin, hand, GateOp.eval, cval, hp, hq]
      · have hSeq : line l = Sc gates j' p ∪ Sc gates j' q := by
          rw [← hSj']
          ext v
          simp [mem_S_iff, mem_Sc_iff, wval_gate gates j' hj'_lt_len, hin, hor, GateOp.eval]
        have hsum := Finset.card_union_le (Sc gates j' p) (Sc gates j' q)
        rw [← hSeq, line_card l] at hsum
        by_cases hcP : 2 ≤ (Sc gates j' p).card
        · obtain ⟨hp, hScP⟩ := Sc_eq_S_of_card_pos gates j' p (by omega)
          rw [hScP] at hcP
          have hp13 : 13 ≤ p := (S_ge_two_bounds gates p hcP).1
          have hsubP : S gates p ⊆ line l := by
            have hs : Sc gates j' p ⊆ line l := hSeq ▸ Finset.subset_union_left
            rw [hScP] at hs
            exact hs
          have hpOwn : (p - 13) ∈ Own gates l := by
            rw [mem_Own_iff]
            have hadd : 13 + (p - 13) = p := by omega
            rw [hadd]
            exact ⟨by omega, hcP, hsubP⟩
          exact False.elim (hno_lt_j' (p - 13) (by omega) hpOwn)
        · have hcQ : 2 ≤ (Sc gates j' q).card := by omega
          obtain ⟨hq, hScQ⟩ := Sc_eq_S_of_card_pos gates j' q (by omega)
          rw [hScQ] at hcQ
          have hq13 : 13 ≤ q := (S_ge_two_bounds gates q hcQ).1
          have hsubQ : S gates q ⊆ line l := by
            have hs : Sc gates j' q ⊆ line l := hSeq ▸ Finset.subset_union_right
            rw [hScQ] at hs
            exact hs
          have hqOwn : (q - 13) ∈ Own gates l := by
            rw [mem_Own_iff]
            have hadd : 13 + (q - 13) = q := by omega
            rw [hadd]
            exact ⟨by omega, hcQ, hsubQ⟩
          exact False.elim (hno_lt_j' (q - 13) (by omega) hqOwn)
    | _ :: _ :: _ :: _ =>
      rw [hin] at hlen
      simp at hlen
  rcases hstep2 with ⟨b, d, hbOut, hdOut, hlb, hld, hb5, hd5, hbNe, hdNe, hval_j'⟩
  have hforbid_bdc : ∀ u v : Fin 13, u ∉ line l → v ∉ line l →
      ¬ (wval gates (13 + b) (pt2 u v) = true ∧ wval gates (13 + d) (pt2 u v) = true ∧
         wval gates (13 + c) (pt2 u v) = true) := by
    intro u v hu hv ⟨hbT, hdT, hcT⟩
    have htrue : wval gates (13 + j_l) (pt2 u v) = true := by
      rw [hval_jl, hval_j', hbT, hdT, hcT]
      rfl
    have hfalse := hsafe_l.2 u v hu hv
    rw [htrue] at hfalse
    cases hfalse
  have hdisj_bd : Disjoint (S gates (13 + b) \ line l) (S gates (13 + d) \ line l) :=
    disjoint_diff_of_triple gates hmono (13 + b) (13 + d) (13 + c) l hcNe hforbid_bdc
  have hdisj_bc : Disjoint (S gates (13 + b) \ line l) (S gates (13 + c) \ line l) := by
    apply disjoint_diff_of_triple gates hmono (13 + b) (13 + c) (13 + d) l hdNe
    intro u v hu hv ⟨hbT, hcT, hdT⟩
    exact hforbid_bdc u v hu hv ⟨hbT, hdT, hcT⟩
  have hdisj_dc : Disjoint (S gates (13 + d) \ line l) (S gates (13 + c) \ line l) := by
    apply disjoint_diff_of_triple gates hmono (13 + d) (13 + c) (13 + b) l hbNe
    intro u v hu hv ⟨hdT, hcT, hbT⟩
    exact hforbid_bdc u v hu hv ⟨hbT, hdT, hcT⟩
  have hbd : b ≠ d := by
    intro h
    subst h
    rcases hbNe with ⟨z, hz⟩
    exact (Finset.disjoint_left.mp hdisj_bd) hz hz
  have hbc : b ≠ c := by
    intro h
    subst h
    rcases hbNe with ⟨z, hz⟩
    exact (Finset.disjoint_left.mp hdisj_bc) hz hz
  have hdc : d ≠ c := by
    intro h
    subst h
    rcases hdNe with ⟨z, hz⟩
    exact (Finset.disjoint_left.mp hdisj_dc) hz hz
  have hdisj_bd_c :
      Disjoint (S gates (13 + b) \ line l ∪ S gates (13 + d) \ line l) (S gates (13 + c) \ line l) :=
    Finset.disjoint_union_left.mpr ⟨hdisj_bc, hdisj_dc⟩
  have hunion_sub :
      S gates (13 + b) \ line l ∪ S gates (13 + d) \ line l ∪ S gates (13 + c) \ line l ⊆
        Finset.univ \ line l := by
    intro z hz
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and] at hz ⊢
    rcases hz with (⟨_, hz⟩ | ⟨_, hz⟩) | ⟨_, hz⟩ <;> exact hz
  have hcompl_card : (Finset.univ \ line l).card = 9 := by
    have hsd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (line l))
    rw [Finset.card_univ, Fintype.card_fin, line_card l] at hsd
    omega
  have hsum_diff :
      (S gates (13 + b) \ line l).card + (S gates (13 + d) \ line l).card +
        (S gates (13 + c) \ line l).card ≤ 9 := by
    have hle := Finset.card_le_card hunion_sub
    rw [Finset.card_union_of_disjoint hdisj_bd_c, Finset.card_union_of_disjoint hdisj_bd,
      hcompl_card] at hle
    exact hle
  have hsb := Finset.card_sdiff_add_card_eq_card hlb
  have hsd := Finset.card_sdiff_add_card_eq_card hld
  have hsc := Finset.card_sdiff_add_card_eq_card hlc
  rw [line_card l] at hsb hsd hsc
  exact ⟨b, d, c, hbOut, hdOut, hcOut, hbd, hbc, hdc, hlb, hld, hlc, hb5, hd5, hc5, by omega⟩

private def wt (s : ℕ) : ℕ :=
  if s ≤ 6 then 2 else if s ≤ 8 then 1 else 0

private lemma wt_triple (s1 s2 s3 : ℕ) (h1 : 5 ≤ s1) (h2 : 5 ≤ s2) (h3 : 5 ≤ s3)
    (hsum : s1 + s2 + s3 ≤ 21) : 2 ≤ wt s1 + wt s2 + wt s3 := by
  unfold wt
  split_ifs <;> omega

private lemma deg_mul_wt_le_two (T : Finset (Fin 13)) :
    (Finset.univ.filter fun l : Fin 13 => line l ⊆ T).card * wt T.card ≤ 2 := by
  unfold wt
  split_ifs with h6 h8
  · have h1 := lines_subset_card_le_one h6
    omega
  · have h2 := lines_subset_card_le_two h8
    omega
  · omega

private lemma main_bound (gates : List Gate) (out : Fin 13 → ℕ)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ line w, x v = true)) :
    39 ≤ gates.length := by
  let R : Finset (Fin 13) := Finset.univ.filter (fun l => (Own gates l).card = 2)
  have hrow : ∀ l ∈ R,
      2 ≤ ∑ u ∈ Outside gates,
        if line l ⊆ S gates (13 + u) then wt (S gates (13 + u)).card else 0 := by
    intro l hl
    have hl2 : (Own gates l).card = 2 := (Finset.mem_filter.mp hl).2
    obtain ⟨b, d, c, hbOut, hdOut, hcOut, hbd, hbc, hdc, hlb, hld, hlc, hb5, hd5, hc5, hsum⟩ :=
      own_card_eq_two_triple gates out hgates heval l hl2
    let f : ℕ → ℕ := fun u =>
      if line l ⊆ S gates (13 + u) then wt (S gates (13 + u)).card else 0
    have hsub : ({b, d, c} : Finset ℕ) ⊆ Outside gates := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    have hsum3 : ∑ u ∈ ({b, d, c} : Finset ℕ), f u =
        wt (S gates (13 + b)).card + wt (S gates (13 + d)).card + wt (S gates (13 + c)).card := by
      have hnb : b ∉ ({d, c} : Finset ℕ) := by simp [hbd, hbc]
      have hnd : d ∉ ({c} : Finset ℕ) := by simp [hdc]
      rw [Finset.sum_insert hnb, Finset.sum_insert hnd, Finset.sum_singleton]
      simp only [f, if_pos hlb, if_pos hld, if_pos hlc]
      omega
    have hwt2 : 2 ≤ wt (S gates (13 + b)).card + wt (S gates (13 + d)).card +
        wt (S gates (13 + c)).card :=
      wt_triple _ _ _ hb5 hd5 hc5 hsum
    have hle : ∑ u ∈ ({b, d, c} : Finset ℕ), f u ≤ ∑ u ∈ Outside gates, f u :=
      Finset.sum_le_sum_of_subset hsub
    exact le_trans hwt2 (hsum3 ▸ hle)
  have hdouble : 2 * R.card ≤ 2 * (Outside gates).card := by
    calc
      2 * R.card = ∑ _l ∈ R, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ l ∈ R, ∑ u ∈ Outside gates,
            if line l ⊆ S gates (13 + u) then wt (S gates (13 + u)).card else 0 :=
          Finset.sum_le_sum hrow
      _ = ∑ u ∈ Outside gates, ∑ l ∈ R,
            if line l ⊆ S gates (13 + u) then wt (S gates (13 + u)).card else 0 :=
          Finset.sum_comm
      _ ≤ ∑ u ∈ Outside gates, ∑ l : Fin 13,
            if line l ⊆ S gates (13 + u) then wt (S gates (13 + u)).card else 0 := by
          apply Finset.sum_le_sum
          intro u _
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ R)
      _ = ∑ u ∈ Outside gates,
            (Finset.univ.filter fun l : Fin 13 => line l ⊆ S gates (13 + u)).card *
              wt (S gates (13 + u)).card := by
          apply Finset.sum_congr rfl
          intro u _
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ _u ∈ Outside gates, 2 := by
          apply Finset.sum_le_sum
          intro u _
          exact deg_mul_wt_le_two (S gates (13 + u))
      _ = 2 * (Outside gates).card := by simp [Nat.mul_comm]
  have hR_le_out : R.card ≤ (Outside gates).card := by omega
  have hown_lb : ∀ l : Fin 13, (if l ∈ R then 2 else 3) ≤ (Own gates l).card := by
    intro l
    have hge2 := own_card_ge_two gates out hgates heval l
    by_cases hl : l ∈ R
    · rw [if_pos hl]
      exact hge2
    · rw [if_neg hl]
      have hne2 : (Own gates l).card ≠ 2 := by
        intro heq
        exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ l, heq⟩)
      omega
  have hsum_own : (∑ l : Fin 13, if l ∈ R then 2 else 3) ≤ ∑ l : Fin 13, (Own gates l).card :=
    Finset.sum_le_sum (fun l _ => hown_lb l)
  have hsum39 : (∑ l : Fin 13, if l ∈ R then 2 else 3) + R.card = 39 := by
    have hRcard : R.card = ∑ l : Fin 13, if l ∈ R then 1 else 0 := by
      simp [Finset.sum_ite_mem]
    rw [hRcard, ← Finset.sum_add_distrib]
    have h3 : ∀ l : Fin 13, (if l ∈ R then 2 else 3) + (if l ∈ R then 1 else 0) = 3 := by
      intro l
      split_ifs <;> omega
    simp [h3]
  have hpart := own_add_outside_le gates
  omega

end PEqualNP.Outside.L_meta_667

theorem PEqualNP.Outside.L_meta_667 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 13) (x : Fin 13 → Bool), (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)), x v = true)) → 39 ≤ gates.length := by
  intro gates out hgates heval
  exact PEqualNP.Outside.L_meta_667.main_bound gates out hgates heval
