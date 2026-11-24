import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5160

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.HeptadCover

lemma getD_app_left {α : Type*} (l1 l2 : List α) (d : α) {i : ℕ} (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_app_right {α : Type*} (l1 l2 : List α) (d : α) {i : ℕ} (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [getD_app_right _ _ _ (le_refl _), Nat.sub_self]
  rfl

lemma list_split_getD {α : Type*} (l : List α) (d : α) {k : ℕ} (hk : k < l.length) :
    l = l.take k ++ [l.getD k d] ++ l.drop (k + 1) := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a t ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
      simp only [List.take_succ_cons, List.getD_cons_succ, List.drop_succ_cons, List.cons_append]
      congr 1
      exact ih hk

lemma gateAt_mem {C : Circuit} {k : ℕ} (hk : k < C.gates.length) :
    gateAt C k ∈ C.gates := by
  have h : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
  have heq : gateAt C k = C.gates[k] := by
    simp [gateAt, List.getD_eq_getElem?_getD, h]
  rw [heq]
  exact List.getElem_mem hk

lemma gateAt_append_left (gs1 gs2 : List Gate) {o1 o2 k : ℕ} (hk : k < gs1.length) :
    gateAt ⟨gs1 ++ gs2, o1⟩ k = gateAt ⟨gs1, o2⟩ k :=
  getD_app_left gs1 gs2 ⟨GateOp.or, []⟩ hk

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wireStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl wireStep w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (wireStep w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_⟩
    rw [List.foldl_cons, ht]
    simp [wireStep, List.append_assoc]

lemma foldl_wireStep_getD_lt (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (gs.foldl wireStep w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := foldl_wireStep_prefix gs w
  rw [ht, getD_app_left _ _ _ hi]

lemma foldl_wireStep_take_getD (gs1 gs2 : List Gate) (xs : List Bool) {i : ℕ}
    (hi : i < xs.length + gs1.length) :
    ((gs1 ++ gs2).foldl wireStep xs).getD i false = (gs1.foldl wireStep xs).getD i false := by
  rw [List.foldl_append]
  exact foldl_wireStep_getD_lt gs2 (gs1.foldl wireStep xs) (by rw [foldl_wireStep_length]; exact hi)

lemma foldl_wireStep_at (gs : List Gate) (xs : List Bool) {k : ℕ} (hk : k < gs.length) :
    (gs.foldl wireStep xs).getD (xs.length + k) false =
      (gs.getD k ⟨GateOp.or, []⟩).op.eval
        ((gs.getD k ⟨GateOp.or, []⟩).inputs.map fun i =>
          ((gs.take k).foldl wireStep xs).getD i false) := by
  have hsp := list_split_getD gs ⟨GateOp.or, []⟩ hk
  have hlen : (gs.take k ++ [gs.getD k ⟨GateOp.or, []⟩]).length = k + 1 := by
    simp [List.length_take, Nat.min_eq_left (le_of_lt hk)]
  have h1 : (gs.foldl wireStep xs).getD (xs.length + k) false =
      ((gs.take k ++ [gs.getD k ⟨GateOp.or, []⟩]).foldl wireStep xs).getD
        (xs.length + k) false := by
    conv_lhs => rw [hsp]
    exact foldl_wireStep_take_getD _ _ xs (by rw [hlen]; omega)
  rw [h1, List.foldl_append, List.foldl_cons, List.foldl_nil, wireStep]
  have hlen2 : ((gs.take k).foldl wireStep xs).length = xs.length + k := by
    rw [foldl_wireStep_length, List.length_take, Nat.min_eq_left (le_of_lt hk)]
  conv_lhs => arg 2; rw [← hlen2]
  exact getD_snoc_eq _ _ _

lemma readsBack_wire_at (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) (xs : List Bool)
    (hxs : xs.length = n) {k : ℕ} (hk : k < C.gates.length) :
    (C.wires xs).getD (n + k) false =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires xs).getD i false) := by
  have h1 : (C.wires xs).getD (n + k) false =
      (C.gates.foldl wireStep xs).getD (xs.length + k) false := by
    rw [hxs]; rfl
  rw [h1, foldl_wireStep_at C.gates xs hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < n + k := hrb k hk i hi
  have hlen : (C.gates.take k).length = k := List.length_take_of_le (le_of_lt hk)
  have hsp : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
  show ((C.gates.take k).foldl wireStep xs).getD i false = (C.gates.foldl wireStep xs).getD i false
  conv_rhs => rw [hsp]
  exact (foldl_wireStep_take_getD (C.gates.take k) (C.gates.drop k) xs
    (by rw [hxs, hlen]; exact hlt)).symm

lemma wires_length_eq (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.gates.length :=
  foldl_wireStep_length C.gates xs

lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma foldl_coneStep_prefix (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    ∃ t, gs.foldl (coneStep n) cs = cs ++ t := by
  induction gs generalizing cs with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (coneStep n cs g)
    refine ⟨((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])) :: t, ?_⟩
    rw [List.foldl_cons, ht]
    simp [coneStep, List.append_assoc]

lemma foldl_coneStep_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) {j : ℕ}
    (hj : j < cs.length) :
    (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
  obtain ⟨t, ht⟩ := foldl_coneStep_prefix n gs cs
  rw [ht, getD_app_left _ _ _ hj]

lemma foldl_coneStep_take_getD (n : ℕ) (gs1 gs2 : List Gate) {j : ℕ} (hj : j < gs1.length) :
    ((gs1 ++ gs2).foldl (coneStep n) []).getD j [] = (gs1.foldl (coneStep n) []).getD j [] := by
  rw [List.foldl_append]
  exact foldl_coneStep_getD_lt n gs2 _ (by rw [foldl_coneStep_length]; simp; exact hj)

lemma cones_eq_at (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  have hsp := list_split_getD C.gates ⟨GateOp.or, []⟩ hj
  rw [show C.gates.getD j ⟨GateOp.or, []⟩ = gateAt C j from rfl] at hsp
  have hlen : (C.gates.take j ++ [gateAt C j]).length = j + 1 := by
    simp [List.length_take, Nat.min_eq_left (le_of_lt hj)]
  have h1 : (cones n C).getD j [] =
      ((C.gates.take j ++ [gateAt C j]).foldl (coneStep n) []).getD j [] := by
    unfold cones
    conv_lhs => rw [hsp]
    exact foldl_coneStep_take_getD n _ _ (by rw [hlen]; omega)
  rw [h1, List.foldl_append, List.foldl_cons, List.foldl_nil, coneStep]
  have hlen2 : ((C.gates.take j).foldl (coneStep n) []).length = j := by
    rw [foldl_coneStep_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (le_of_lt hj)]
  have h2 : ((((C.gates.take j).foldl (coneStep n) []) ++
      [((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: ((C.gates.take j).foldl (coneStep n) []).getD (w - n) [])]).getD j []) =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: ((C.gates.take j).foldl (coneStep n) []).getD (w - n) []) := by
    conv_lhs => arg 2; rw [← hlen2]
    exact getD_snoc_eq _ _ _
  rw [hlen2, h2, List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro w hw
  have hmem := (List.mem_filter.mp hw).2
  simp only [decide_eq_true_eq] at hmem
  congr 1
  have hwlt : w - n < j := by omega
  have hsp2 : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  unfold cones
  conv_rhs => rw [hsp2]
  exact (foldl_coneStep_take_getD n (C.gates.take j) (C.gates.drop j)
    (by rw [List.length_take_of_le (le_of_lt hj)]; exact hwlt)).symm

lemma inCone_iff_lt (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  by_cases hj : j < C.gates.length
  · rw [cones_eq_at n C hj, List.mem_flatMap]
    constructor
    · rintro ⟨w, hw, hi⟩
      have hw' := List.mem_filter.mp hw
      simp only [decide_eq_true_eq] at hw'
      refine ⟨hj, w, hw'.1, hw'.2.1, hw'.2.2, ?_⟩
      simpa [List.mem_cons] using hi
    · rintro ⟨_, w, hw, hlo, hhi, hi⟩
      refine ⟨w, List.mem_filter.mpr ⟨hw, ?_⟩, ?_⟩
      · simp [hlo, hhi]
      · simpa [List.mem_cons] using hi
  · constructor
    · intro hi
      have hlen : (cones n C).length ≤ j := by
        unfold cones
        rw [foldl_coneStep_length, List.length_nil, Nat.zero_add]
        omega
      rw [List.getD_eq_default _ _ hlen] at hi
      simp at hi
    · intro h
      exact False.elim (hj h.1)

lemma inCone_lt (n : ℕ) (C : Circuit) {i j : ℕ} :
    InCone n C i j → i < j ∧ j < C.gates.length := by
  induction j using Nat.strong_induction_on generalizing i with
  | ind j ih =>
    intro h
    rw [inCone_iff_lt] at h
    rcases h with ⟨hj, w, _, hlo, hhi, hi⟩
    refine ⟨?_, hj⟩
    rcases hi with rfl | hi
    · omega
    · have hwlt : w - n < j := by omega
      have hsub := (ih (w - n) hwlt hi).1
      omega

lemma inCone_trans (n : ℕ) (C : Circuit) {i k j : ℕ} :
    InCone n C i k → InCone n C k j → InCone n C i j := by
  intro hik hkj
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [inCone_iff_lt] at hkj ⊢
    rcases hkj with ⟨hj, w, hw, hlo, hhi, hk⟩
    refine ⟨hj, w, hw, hlo, hhi, Or.inr ?_⟩
    rcases hk with rfl | hk
    · exact hik
    · exact ih (w - n) (by omega) hk

lemma inCone_direct (n : ℕ) (C : Circuit) {j w : ℕ} (hj : j < C.gates.length)
    (hw : w ∈ (gateAt C j).inputs) (hlo : n ≤ w) (hhi : w < n + j) :
    InCone n C (w - n) j := by
  rw [inCone_iff_lt]
  exact ⟨hj, w, hw, hlo, hhi, Or.inl rfl⟩

lemma inCone_append_left (n : ℕ) (gs1 gs2 : List Gate) {i j : ℕ} (hj : j < gs1.length) :
    InCone n ⟨gs1 ++ gs2, 0⟩ i j ↔ InCone n ⟨gs1, 0⟩ i j := by
  unfold InCone cones
  simp only [foldl_coneStep_take_getD n gs1 gs2 hj]

lemma headD_filter_not_mem {l : List ℕ} {z : ℕ → Bool}
    (hlen : l.length ≤ 2) (hany : l.any z = true) (hall : ¬ (l.all z = true)) :
    let y := (l.filter (fun i => !z i)).headD 0
    y ∈ l ∧ z y = false ∧ ∀ i ∈ l, i = y ∨ z i = true := by
  cases l with
  | nil => simp at hany
  | cons a t =>
    cases t with
    | nil =>
      simp only [List.any_cons, List.any_nil, Bool.or_false] at hany
      simp [hany] at hall
    | cons b u =>
      cases u with
      | nil =>
        simp only [List.any_cons, List.any_nil, Bool.or_false] at hany
        simp only [List.all_cons, List.all_nil, Bool.and_true] at hall
        by_cases ha : z a = true <;> by_cases hb : z b = true
        · simp [ha, hb] at hall
        · have hbf : z b = false := Bool.eq_false_iff.mpr hb
          simp [ha, hbf]
        · have haf : z a = false := Bool.eq_false_iff.mpr ha
          simp [haf, hb]
        · have haf : z a = false := Bool.eq_false_iff.mpr ha
          have hbf : z b = false := Bool.eq_false_iff.mpr hb
          simp [haf, hbf] at hany
      | cons c v =>
        simp only [List.length_cons] at hlen
        omega

def compInit : List Gate × List ℕ × (ℕ → ℕ) × (ℕ → Bool) :=
  ([], [], fun w => w, fun _ => false)

def compStep (C : Circuit) (x5 n : ℕ)
    (st : List Gate × List ℕ × (ℕ → ℕ) × (ℕ → Bool)) :
    List Gate × List ℕ × (ℕ → ℕ) × (ℕ → Bool) :=
  let d := st.1
  let orig := st.2.1
  let r := st.2.2.1
  let z := st.2.2.2
  let gt := gateAt C n
  if n ≤ x5 then
    (d ++ [gt], orig ++ [n],
      (fun w => if w = 26 + n then 26 + d.length else r w),
      (fun w => if w = 26 + n then decide (n = x5) else z w))
  else
    match gt.op with
    | GateOp.and =>
      if gt.inputs.any z then
        (d, orig,
          (fun w => if w = 26 + n then 0 else r w),
          (fun w => if w = 26 + n then true else z w))
      else
        (d ++ [⟨GateOp.and, gt.inputs.map r⟩], orig ++ [n],
          (fun w => if w = 26 + n then 26 + d.length else r w),
          (fun w => if w = 26 + n then false else z w))
    | GateOp.or =>
      if gt.inputs.all z then
        (d, orig,
          (fun w => if w = 26 + n then 0 else r w),
          (fun w => if w = 26 + n then true else z w))
      else if gt.inputs.any z then
        let y := (gt.inputs.filter (fun i => !z i)).headD 0
        (d, orig,
          (fun w => if w = 26 + n then r y else r w),
          (fun w => if w = 26 + n then false else z w))
      else
        (d ++ [⟨GateOp.or, gt.inputs.map r⟩], orig ++ [n],
          (fun w => if w = 26 + n then 26 + d.length else r w),
          (fun w => if w = 26 + n then false else z w))
    | op =>
      (d ++ [⟨op, gt.inputs.map r⟩], orig ++ [n],
        (fun w => if w = 26 + n then 26 + d.length else r w),
        (fun w => if w = 26 + n then false else z w))

def compRun (C : Circuit) (x5 : ℕ) : ℕ → List Gate × List ℕ × (ℕ → ℕ) × (ℕ → Bool)
  | 0 => compInit
  | n + 1 => compStep C x5 n (compRun C x5 n)

abbrev compD (C : Circuit) (x5 n : ℕ) : List Gate := (compRun C x5 n).1
abbrev compOrig (C : Circuit) (x5 n : ℕ) : List ℕ := (compRun C x5 n).2.1
abbrev compR (C : Circuit) (x5 n : ℕ) : ℕ → ℕ := (compRun C x5 n).2.2.1
abbrev compZ (C : Circuit) (x5 n : ℕ) : ℕ → Bool := (compRun C x5 n).2.2.2

lemma comp_step_cases (C : Circuit) (x5 n : ℕ) :
    (∃ g, compD C x5 (n + 1) = compD C x5 n ++ [g] ∧
      compOrig C x5 (n + 1) = compOrig C x5 n ++ [n]) ∨
    (compD C x5 (n + 1) = compD C x5 n ∧ compOrig C x5 (n + 1) = compOrig C x5 n) := by
  dsimp [compD, compOrig, compRun, compStep]
  by_cases hnx : n ≤ x5
  · simp [hnx]
  · simp only [hnx, ↓reduceIte]
    cases (gateAt C n).op <;> dsimp
    · by_cases h1 : (gateAt C n).inputs.any (compZ C x5 n) = true <;> simp [h1]
    · by_cases h1 : (gateAt C n).inputs.all (compZ C x5 n) = true
      · simp [h1]
      · by_cases h2 : (gateAt C n).inputs.any (compZ C x5 n) = true <;> simp [h1, h2]
    · exact Or.inl ⟨_, rfl, rfl⟩
    · exact Or.inl ⟨_, rfl, rfl⟩
    · exact Or.inl ⟨_, rfl, rfl⟩

lemma comp_rz_eq_else (C : Circuit) (x5 n w : ℕ) (hw : w ≠ 26 + n) :
    compR C x5 (n + 1) w = compR C x5 n w ∧ compZ C x5 (n + 1) w = compZ C x5 n w := by
  dsimp [compR, compZ, compRun, compStep]
  by_cases hnx : n ≤ x5
  · simp [hnx, hw]
  · simp only [hnx, ↓reduceIte]
    cases (gateAt C n).op <;> dsimp
    · by_cases h1 : (gateAt C n).inputs.any (compZ C x5 n) = true <;> simp [h1, hw]
    · by_cases h1 : (gateAt C n).inputs.all (compZ C x5 n) = true
      · simp [h1, hw]
      · by_cases h2 : (gateAt C n).inputs.any (compZ C x5 n) = true <;> simp [h1, h2, hw]
    · simp [hw]
    · simp [hw]
    · simp [hw]

lemma comp_len (C : Circuit) (x5 n : ℕ) :
    (compD C x5 n).length = (compOrig C x5 n).length ∧ (compD C x5 n).length ≤ n := by
  induction n with
  | zero => simp [compD, compOrig, compRun, compInit]
  | succ n ih =>
    rcases comp_step_cases C x5 n with ⟨g, hd, ho⟩ | ⟨hd, ho⟩
    · rw [hd, ho, List.length_append, List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [hd, ho]
      omega

lemma comp_mono_prefix (C : Circuit) (x5 : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    (∃ td, compD C x5 m = compD C x5 n ++ td) ∧
      (∃ to_, compOrig C x5 m = compOrig C x5 n ++ to_) := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
  | succ m ih =>
    by_cases h : n ≤ m
    · obtain ⟨⟨td, htd⟩, ⟨to_, hto⟩⟩ := ih h
      rcases comp_step_cases C x5 m with ⟨g, hd, ho⟩ | ⟨hd, ho⟩
      · exact ⟨⟨td ++ [g], by rw [hd, htd, List.append_assoc]⟩,
          ⟨to_ ++ [m], by rw [ho, hto, List.append_assoc]⟩⟩
      · exact ⟨⟨td, by rw [hd, htd]⟩, ⟨to_, by rw [ho, hto]⟩⟩
    · have hn : n = m + 1 := by omega
      subst hn
      exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

lemma comp_len_mono (C : Circuit) (x5 : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    (compD C x5 n).length ≤ (compD C x5 m).length := by
  obtain ⟨⟨td, htd⟩, _⟩ := comp_mono_prefix C x5 hnm
  rw [htd, List.length_append]
  omega

lemma comp_len_growth (C : Circuit) (x5 : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    (compD C x5 m).length ≤ (compD C x5 n).length + (m - n) := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    simp
  | succ m ih =>
    by_cases h : n ≤ m
    · have hih := ih h
      rcases comp_step_cases C x5 m with ⟨g, hd, _⟩ | ⟨hd, _⟩
      · rw [hd, List.length_append]
        simp only [List.length_cons, List.length_nil]
        omega
      · rw [hd]
        omega
    · have hn : n = m + 1 := by omega
      subst hn
      simp

lemma comp_stable (C : Circuit) (x5 : ℕ) {n m w : ℕ} (hnm : n ≤ m) (hw : w < 26 + n) :
    compR C x5 m w = compR C x5 n w ∧ compZ C x5 m w = compZ C x5 n w := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    by_cases h : n ≤ m
    · have h1 := ih h
      have h2 := comp_rz_eq_else C x5 m w (by omega)
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
    · have hn : n = m + 1 := by omega
      subst hn
      exact ⟨rfl, rfl⟩

lemma comp_prefix_le (C : Circuit) (x5 : ℕ) (hx : x5 < C.gates.length) :
    ∀ n ≤ x5 + 1,
      compD C x5 n = C.gates.take n ∧
      compOrig C x5 n = List.range n ∧
      (∀ w < 26 + n, compR C x5 n w = w) ∧
      (∀ w, compZ C x5 n w = decide (n = x5 + 1 ∧ w = 26 + x5)) := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨by simp [compD, compRun, compInit], by simp [compOrig, compRun, compInit], ?_, ?_⟩
    · intro w _; rfl
    · intro w; simp [compZ, compRun, compInit]
  | succ n ih =>
    rcases ih (by omega) with ⟨hd, ho, hr, hz⟩
    have hle : n ≤ x5 := by omega
    have hnk : n < C.gates.length := by omega
    have htake : C.gates.take (n + 1) = C.gates.take n ++ [gateAt C n] := by
      have hsp := list_split_getD C.gates ⟨GateOp.or, []⟩ hnk
      rw [show C.gates.getD n ⟨GateOp.or, []⟩ = gateAt C n from rfl] at hsp
      have hlen : (C.gates.take n ++ [gateAt C n]).length = n + 1 := by
        simp [List.length_take, Nat.min_eq_left (le_of_lt hnk)]
      have h3 := congrArg (List.take (n + 1)) hsp
      rw [List.take_left' hlen] at h3
      exact h3
    have hd1 : compD C x5 (n + 1) = compD C x5 n ++ [gateAt C n] := by
      simp [compD, compRun, compStep, hle]
    have ho1 : compOrig C x5 (n + 1) = compOrig C x5 n ++ [n] := by
      simp [compOrig, compRun, compStep, hle]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hd1, hd, htake]
    · rw [ho1, ho, List.range_succ]
    · intro w hw
      by_cases hw2 : w = 26 + n
      · subst hw2
        have hdl : (compD C x5 n).length = n := by rw [hd, List.length_take_of_le (le_of_lt hnk)]
        simp [compR, compRun, compStep, hle, hdl]
      · rw [(comp_rz_eq_else C x5 n w hw2).1]
        exact hr w (by omega)
    · intro w
      by_cases hw2 : w = 26 + n
      · subst hw2
        simp only [compZ, compRun, compStep, hle, ↓reduceIte]
        by_cases hnx : n = x5
        · subst hnx; simp
        · simp [hnx]
      · rw [(comp_rz_eq_else C x5 n w hw2).2, hz w]
        have h1 : decide (n = x5 + 1 ∧ w = 26 + x5) = false := by
          simp only [decide_eq_false_iff_not, not_and]; intro h; omega
        have h2 : decide (n + 1 = x5 + 1 ∧ w = 26 + x5) = false := by
          simp only [decide_eq_false_iff_not, not_and]; intro h hw3; apply hw2; omega
        rw [h1, h2]

lemma comp_orig_props (C : Circuit) (x5 : ℕ) (hm : Monotone2 C) (hrb : ReadsBack 26 C)
    (hx : x5 < C.gates.length) :
    ∀ n ≤ C.gates.length,
      (∀ j' < (compOrig C x5 n).length,
        (compOrig C x5 n).getD j' 0 < n ∧
        (gateAt ⟨compD C x5 n, 0⟩ j').op = (gateAt C ((compOrig C x5 n).getD j' 0)).op ∧
        (gateAt ⟨compD C x5 n, 0⟩ j').inputs =
          (gateAt C ((compOrig C x5 n).getD j' 0)).inputs.map (compR C x5 n) ∧
        (∀ w ∈ (gateAt C ((compOrig C x5 n).getD j' 0)).inputs, compZ C x5 n w = false)) ∧
      (∀ j1 j2, j1 < j2 → j2 < (compOrig C x5 n).length →
        (compOrig C x5 n).getD j1 0 < (compOrig C x5 n).getD j2 0) := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro j' hj'; simp [compOrig, compRun, compInit] at hj'
    · intro j1 j2 _ hj2; simp [compOrig, compRun, compInit] at hj2
  | succ n ih =>
    rcases ih (by omega) with ⟨ih1, ih2⟩
    have hnk : n < C.gates.length := by omega
    have hlen_eq := (comp_len C x5 n).1
    have hlt_old : ∀ j' < (compOrig C x5 n).length,
        (compOrig C x5 n).getD j' 0 < n + 1 ∧
        (gateAt ⟨compD C x5 n, 0⟩ j').op = (gateAt C ((compOrig C x5 n).getD j' 0)).op ∧
        (gateAt ⟨compD C x5 n, 0⟩ j').inputs =
          (gateAt C ((compOrig C x5 n).getD j' 0)).inputs.map (compR C x5 (n + 1)) ∧
        (∀ w ∈ (gateAt C ((compOrig C x5 n).getD j' 0)).inputs, compZ C x5 (n + 1) w = false) := by
      intro j' hj'
      rcases ih1 j' hj' with ⟨hk, hop, hin, hz⟩
      refine ⟨by omega, hop, ?_, ?_⟩
      · rw [hin]
        apply List.map_congr_left
        intro w hw
        have hwlt : w < 26 + n := by
          have := hrb ((compOrig C x5 n).getD j' 0) (by omega) w hw
          omega
        exact (comp_rz_eq_else C x5 n w (by omega)).1.symm
      · intro w hw
        have hwlt : w < 26 + n := by
          have := hrb ((compOrig C x5 n).getD j' 0) (by omega) w hw
          omega
        rw [(comp_rz_eq_else C x5 n w (by omega)).2]
        exact hz w hw
    by_cases hnx : n ≤ x5
    · have hd1 : compD C x5 (n + 1) = compD C x5 n ++ [gateAt C n] := by
        simp [compD, compRun, compStep, hnx]
      have ho1 : compOrig C x5 (n + 1) = compOrig C x5 n ++ [n] := by
        simp [compOrig, compRun, compStep, hnx]
      refine ⟨?_, ?_⟩
      · intro j' hj'
        rw [ho1, List.length_append] at hj'
        simp only [List.length_cons, List.length_nil] at hj'
        by_cases hjold : j' < (compOrig C x5 n).length
        · rcases hlt_old j' hjold with ⟨hk, hop, hin, hz⟩
          rw [ho1, getD_app_left _ _ _ hjold]
          have hjD : j' < (compD C x5 n).length := by omega
          have hg : gateAt ⟨compD C x5 (n + 1), 0⟩ j' = gateAt ⟨compD C x5 n, 0⟩ j' := by
            rw [hd1]; exact gateAt_append_left _ _ hjD
          rw [hg]
          exact ⟨hk, hop, hin, hz⟩
        · have hj_eq : j' = (compOrig C x5 n).length := by omega
          subst hj_eq
          have ho_eq : (compOrig C x5 (n + 1)).getD (compOrig C x5 n).length 0 = n := by
            rw [ho1]; exact getD_snoc_eq _ _ _
          have hg : gateAt ⟨compD C x5 (n + 1), 0⟩ (compOrig C x5 n).length = gateAt C n := by
            unfold gateAt
            simp only [hd1, ← hlen_eq]
            exact getD_snoc_eq _ _ _
          rw [ho_eq, hg]
          have hpre := comp_prefix_le C x5 hx n (by omega)
          refine ⟨by omega, rfl, ?_, ?_⟩
          · conv_lhs => rw [← List.map_id (gateAt C n).inputs]
            apply List.map_congr_left
            intro w hw
            have hwlt : w < 26 + n := hrb n hnk w hw
            rw [(comp_rz_eq_else C x5 n w (by omega)).1]
            exact (hpre.2.2.1 w hwlt).symm
          · intro w hw
            have hwlt : w < 26 + n := hrb n hnk w hw
            rw [(comp_rz_eq_else C x5 n w (by omega)).2, hpre.2.2.2 w]
            have hne : n ≠ x5 + 1 := by omega
            simp [hne]
      · intro j1 j2 h12 hj2
        rw [ho1, List.length_append] at hj2
        simp only [List.length_cons, List.length_nil] at hj2
        rw [ho1]
        by_cases hj2o : j2 < (compOrig C x5 n).length
        · rw [getD_app_left _ _ _ (by omega), getD_app_left _ _ _ hj2o]
          exact ih2 j1 j2 h12 hj2o
        · have hj2e : j2 = (compOrig C x5 n).length := by omega
          subst hj2e
          rw [getD_app_left _ _ _ (by omega), getD_snoc_eq]
          exact (ih1 j1 (by omega)).1
    · have hgt_op := (hm (gateAt C n) (gateAt_mem hnk)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgt_op
      rcases hgt_op with hop | hop
      · by_cases hany : (gateAt C n).inputs.any (compZ C x5 n) = true
        · have hd1 : compD C x5 (n + 1) = compD C x5 n := by
            simp [compD, compRun, compStep, hnx, hop, hany]
          have ho1 : compOrig C x5 (n + 1) = compOrig C x5 n := by
            simp [compOrig, compRun, compStep, hnx, hop, hany]
          rw [hd1, ho1]
          exact ⟨hlt_old, ih2⟩
        · have hd1 : compD C x5 (n + 1) =
              compD C x5 n ++ [⟨GateOp.and, (gateAt C n).inputs.map (compR C x5 n)⟩] := by
            simp [compD, compRun, compStep, hnx, hop, hany]
          have ho1 : compOrig C x5 (n + 1) = compOrig C x5 n ++ [n] := by
            simp [compOrig, compRun, compStep, hnx, hop, hany]
          refine ⟨?_, ?_⟩
          · intro j' hj'
            rw [ho1, List.length_append] at hj'
            simp only [List.length_cons, List.length_nil] at hj'
            by_cases hjold : j' < (compOrig C x5 n).length
            · rcases hlt_old j' hjold with ⟨hk, hop2, hin, hz⟩
              rw [ho1, getD_app_left _ _ _ hjold]
              have hg : gateAt ⟨compD C x5 (n + 1), 0⟩ j' = gateAt ⟨compD C x5 n, 0⟩ j' := by
                rw [hd1]; exact gateAt_append_left _ _ (by omega)
              rw [hg]
              exact ⟨hk, hop2, hin, hz⟩
            · have hj_eq : j' = (compOrig C x5 n).length := by omega
              subst hj_eq
              have ho_eq : (compOrig C x5 (n + 1)).getD (compOrig C x5 n).length 0 = n := by
                rw [ho1]; exact getD_snoc_eq _ _ _
              have hg : gateAt ⟨compD C x5 (n + 1), 0⟩ (compOrig C x5 n).length =
                  ⟨GateOp.and, (gateAt C n).inputs.map (compR C x5 n)⟩ := by
                unfold gateAt; simp only [hd1, ← hlen_eq]; exact getD_snoc_eq _ _ _
              rw [ho_eq, hg]
              refine ⟨by omega, hop.symm, ?_, ?_⟩
              · apply List.map_congr_left
                intro w hw
                have hwlt : w < 26 + n := hrb n hnk w hw
                exact (comp_rz_eq_else C x5 n w (by omega)).1.symm
              · intro w hw
                have hwlt : w < 26 + n := hrb n hnk w hw
                rw [(comp_rz_eq_else C x5 n w (by omega)).2]
                by_contra hzt
                have hzt' : compZ C x5 n w = true := by
                  cases hzw : compZ C x5 n w <;> simp_all
                exact hany (List.any_eq_true.mpr ⟨w, hw, hzt'⟩)
          · intro j1 j2 h12 hj2
            rw [ho1, List.length_append] at hj2
            simp only [List.length_cons, List.length_nil] at hj2
            rw [ho1]
            by_cases hj2o : j2 < (compOrig C x5 n).length
            · rw [getD_app_left _ _ _ (by omega), getD_app_left _ _ _ hj2o]
              exact ih2 j1 j2 h12 hj2o
            · have hj2e : j2 = (compOrig C x5 n).length := by omega
              subst hj2e
              rw [getD_app_left _ _ _ (by omega), getD_snoc_eq]
              exact (ih1 j1 (by omega)).1
      · by_cases hall : (gateAt C n).inputs.all (compZ C x5 n) = true
        · have hd1 : compD C x5 (n + 1) = compD C x5 n := by
            simp [compD, compRun, compStep, hnx, hop, hall]
          have ho1 : compOrig C x5 (n + 1) = compOrig C x5 n := by
            simp [compOrig, compRun, compStep, hnx, hop, hall]
          rw [hd1, ho1]
          exact ⟨hlt_old, ih2⟩
        · by_cases hany : (gateAt C n).inputs.any (compZ C x5 n) = true
          · have hd1 : compD C x5 (n + 1) = compD C x5 n := by
              simp [compD, compRun, compStep, hnx, hop, hall, hany]
            have ho1 : compOrig C x5 (n + 1) = compOrig C x5 n := by
              simp [compOrig, compRun, compStep, hnx, hop, hall, hany]
            rw [hd1, ho1]
            exact ⟨hlt_old, ih2⟩
          · have hd1 : compD C x5 (n + 1) =
                compD C x5 n ++ [⟨GateOp.or, (gateAt C n).inputs.map (compR C x5 n)⟩] := by
              simp [compD, compRun, compStep, hnx, hop, hall, hany]
            have ho1 : compOrig C x5 (n + 1) = compOrig C x5 n ++ [n] := by
              simp [compOrig, compRun, compStep, hnx, hop, hall, hany]
            refine ⟨?_, ?_⟩
            · intro j' hj'
              rw [ho1, List.length_append] at hj'
              simp only [List.length_cons, List.length_nil] at hj'
              by_cases hjold : j' < (compOrig C x5 n).length
              · rcases hlt_old j' hjold with ⟨hk, hop2, hin, hz⟩
                rw [ho1, getD_app_left _ _ _ hjold]
                have hg : gateAt ⟨compD C x5 (n + 1), 0⟩ j' = gateAt ⟨compD C x5 n, 0⟩ j' := by
                  rw [hd1]; exact gateAt_append_left _ _ (by omega)
                rw [hg]
                exact ⟨hk, hop2, hin, hz⟩
              · have hj_eq : j' = (compOrig C x5 n).length := by omega
                subst hj_eq
                have ho_eq : (compOrig C x5 (n + 1)).getD (compOrig C x5 n).length 0 = n := by
                  rw [ho1]; exact getD_snoc_eq _ _ _
                have hg : gateAt ⟨compD C x5 (n + 1), 0⟩ (compOrig C x5 n).length =
                    ⟨GateOp.or, (gateAt C n).inputs.map (compR C x5 n)⟩ := by
                  unfold gateAt; simp only [hd1, ← hlen_eq]; exact getD_snoc_eq _ _ _
                rw [ho_eq, hg]
                refine ⟨by omega, hop.symm, ?_, ?_⟩
                · apply List.map_congr_left
                  intro w hw
                  have hwlt : w < 26 + n := hrb n hnk w hw
                  exact (comp_rz_eq_else C x5 n w (by omega)).1.symm
                · intro w hw
                  have hwlt : w < 26 + n := hrb n hnk w hw
                  rw [(comp_rz_eq_else C x5 n w (by omega)).2]
                  by_contra hzt
                  have hzt' : compZ C x5 n w = true := by
                    cases hzw : compZ C x5 n w <;> simp_all
                  exact hany (List.any_eq_true.mpr ⟨w, hw, hzt'⟩)
            · intro j1 j2 h12 hj2
              rw [ho1, List.length_append] at hj2
              simp only [List.length_cons, List.length_nil] at hj2
              rw [ho1]
              by_cases hj2o : j2 < (compOrig C x5 n).length
              · rw [getD_app_left _ _ _ (by omega), getD_app_left _ _ _ hj2o]
                exact ih2 j1 j2 h12 hj2o
              · have hj2e : j2 = (compOrig C x5 n).length := by omega
                subst hj2e
                rw [getD_app_left _ _ _ (by omega), getD_snoc_eq]
                exact (ih1 j1 (by omega)).1

lemma comp_range (C : Circuit) (x5 : ℕ) (hx : x5 < C.gates.length) (hm : Monotone2 C)
    (hrb : ReadsBack 26 C) :
    ∀ n ≤ C.gates.length, ∀ w < 26 + n, compZ C x5 n w = false →
      compR C x5 n w < 26 + (compD C x5 n).length ∧
      compR C x5 n w ≠ 26 + x5 ∧
      (compR C x5 n w < 26 ∨
        26 ≤ w ∧ ∃ j' < (compD C x5 n).length,
          compR C x5 n w = 26 + j' ∧
          ((compOrig C x5 n).getD j' 0 = w - 26 ∨
            InCone 26 C ((compOrig C x5 n).getD j' 0) (w - 26))) := by
  intro n hn
  induction n with
  | zero =>
    intro w hw _
    dsimp [compR, compRun, compInit]
    refine ⟨by omega, by omega, Or.inl hw⟩
  | succ n ih =>
    have hnk : n < C.gates.length := by omega
    intro w hw hzw
    by_cases hw_old : w < 26 + n
    · have hrz := comp_rz_eq_else C x5 n w (by omega)
      rw [hrz.2] at hzw
      rw [hrz.1]
      rcases ih (by omega) w hw_old hzw with ⟨hlt, hne, hor⟩
      have hmono := comp_len_mono C x5 (Nat.le_add_right n 1)
      refine ⟨by omega, hne, ?_⟩
      rcases hor with h26 | ⟨hw26, j', hj', hrj, hcone⟩
      · exact Or.inl h26
      · refine Or.inr ⟨hw26, j', by omega, hrj, ?_⟩
        obtain ⟨_, ⟨to_, hto⟩⟩ := comp_mono_prefix C x5 (Nat.le_add_right n 1)
        have hj'_orig : j' < (compOrig C x5 n).length := by
          rw [← (comp_len C x5 n).1]; exact hj'
        rw [hto, getD_app_left _ _ _ hj'_orig]
        exact hcone
    · have hw_eq : w = 26 + n := by omega
      subst hw_eq
      by_cases hnx : n ≤ x5
      · have hpre := comp_prefix_le C x5 hx (n + 1) (by omega)
        have hz_eq := hpre.2.2.2 (26 + n)
        rw [hz_eq] at hzw
        have hlt_x5 : n < x5 := by
          by_contra hge
          have hnx2 : n = x5 := by omega
          subst hnx2
          simp at hzw
        have hr_eq : compR C x5 (n + 1) (26 + n) = 26 + n := hpre.2.2.1 (26 + n) (by omega)
        have hd_eq : (compD C x5 (n + 1)).length = n + 1 := by
          rw [hpre.1, List.length_take_of_le (by omega)]
        have ho_eq : (compOrig C x5 (n + 1)).getD n 0 = n := by
          rw [hpre.2.1, List.getD_eq_getElem?_getD, List.getElem?_range (by omega)]
          rfl
        refine ⟨by omega, by omega, Or.inr ⟨by omega, n, by omega, hr_eq, Or.inl ?_⟩⟩
        rw [ho_eq]; omega
      · have hx1 : x5 + 1 ≤ n := by omega
        have hpre_x5 := comp_prefix_le C x5 hx (x5 + 1) (le_refl _)
        have hlen_x5 : (compD C x5 (x5 + 1)).length = x5 + 1 := by
          rw [hpre_x5.1, List.length_take_of_le (by omega)]
        have hge_x5 : x5 + 1 ≤ (compD C x5 n).length := by
          rw [← hlen_x5]; exact comp_len_mono C x5 hx1
        have hgt := hm (gateAt C n) (gateAt_mem hnk)
        have hgt_op := hgt.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgt_op
        rcases hgt_op with hop | hop
        · have hany : ¬ ((gateAt C n).inputs.any (compZ C x5 n) = true) := by
            intro hany
            have hzt : compZ C x5 (n + 1) (26 + n) = true := by
              simp [compZ, compRun, compStep, hnx, hop, hany]
            rw [hzt] at hzw
            cases hzw
          have hd1 : compD C x5 (n + 1) =
              compD C x5 n ++ [⟨GateOp.and, (gateAt C n).inputs.map (compR C x5 n)⟩] := by
            simp [compD, compRun, compStep, hnx, hop, hany]
          have ho1 : compOrig C x5 (n + 1) = compOrig C x5 n ++ [n] := by
            simp [compOrig, compRun, compStep, hnx, hop, hany]
          have hr1 : compR C x5 (n + 1) (26 + n) = 26 + (compD C x5 n).length := by
            simp [compR, compRun, compStep, hnx, hop, hany]
          have hdl1 : (compD C x5 (n + 1)).length = (compD C x5 n).length + 1 := by
            rw [hd1, List.length_append]; simp
          have ho_at : (compOrig C x5 (n + 1)).getD (compD C x5 n).length 0 = n := by
            rw [ho1, (comp_len C x5 n).1]; exact getD_snoc_eq _ _ _
          refine ⟨by omega, by omega,
            Or.inr ⟨by omega, (compD C x5 n).length, by omega, hr1, Or.inl ?_⟩⟩
          rw [ho_at]; omega
        · have hall : ¬ ((gateAt C n).inputs.all (compZ C x5 n) = true) := by
            intro hall
            have hzt : compZ C x5 (n + 1) (26 + n) = true := by
              simp [compZ, compRun, compStep, hnx, hop, hall]
            rw [hzt] at hzw
            cases hzw
          by_cases hany : (gateAt C n).inputs.any (compZ C x5 n) = true
          · set y := ((gateAt C n).inputs.filter (fun i => !compZ C x5 n i)).headD 0
            have hy := headD_filter_not_mem hgt.2 hany hall
            have hylt : y < 26 + n := hrb n hnk y hy.1
            have hd1 : compD C x5 (n + 1) = compD C x5 n := by
              simp [compD, compRun, compStep, hnx, hop, hall, hany]
            have ho1 : compOrig C x5 (n + 1) = compOrig C x5 n := by
              simp [compOrig, compRun, compStep, hnx, hop, hall, hany]
            have hr1 : compR C x5 (n + 1) (26 + n) = compR C x5 n y := by
              dsimp only [compR, compRun, compStep]
              simp only [hnx, ↓reduceIte, hop, hall, hany, Bool.false_eq_true]
              rfl
            rw [hd1, ho1, hr1]
            rcases ih (by omega) y hylt hy.2.1 with ⟨hlt, hne, hor⟩
            refine ⟨hlt, hne, ?_⟩
            rcases hor with h26 | ⟨hy26, j', hj', hrj, hcone⟩
            · exact Or.inl h26
            · refine Or.inr ⟨by omega, j', hj', hrj, Or.inr ?_⟩
              have hdir : InCone 26 C (y - 26) n := inCone_direct 26 C hnk hy.1 hy26 hylt
              rw [Nat.add_sub_cancel_left]
              rcases hcone with heq | hsub
              · rw [heq]; exact hdir
              · exact inCone_trans 26 C hsub hdir
          · have hd1 : compD C x5 (n + 1) =
                compD C x5 n ++ [⟨GateOp.or, (gateAt C n).inputs.map (compR C x5 n)⟩] := by
              simp [compD, compRun, compStep, hnx, hop, hall, hany]
            have ho1 : compOrig C x5 (n + 1) = compOrig C x5 n ++ [n] := by
              simp [compOrig, compRun, compStep, hnx, hop, hall, hany]
            have hr1 : compR C x5 (n + 1) (26 + n) = 26 + (compD C x5 n).length := by
              simp [compR, compRun, compStep, hnx, hop, hall, hany]
            have hdl1 : (compD C x5 (n + 1)).length = (compD C x5 n).length + 1 := by
              rw [hd1, List.length_append]; simp
            have ho_at : (compOrig C x5 (n + 1)).getD (compD C x5 n).length 0 = n := by
              rw [ho1, (comp_len C x5 n).1]; exact getD_snoc_eq _ _ _
            refine ⟨by omega, by omega,
              Or.inr ⟨by omega, (compD C x5 n).length, by omega, hr1, Or.inl ?_⟩⟩
            rw [ho_at]; omega

lemma comp_monotone2 (C : Circuit) (x5 : ℕ) (hx : x5 < C.gates.length)
    (hm : Monotone2 C) (hrb : ReadsBack 26 C) :
    ∀ n ≤ C.gates.length, Monotone2 ⟨compD C x5 n, 0⟩ := by
  intro n hn g hg
  have hop := (comp_orig_props C x5 hm hrb hx n hn).1
  have hlen_eq := (comp_len C x5 n).1
  obtain ⟨j', hj', hgj'⟩ := List.getElem_of_mem hg
  dsimp only at hj'
  rcases hop j' (by omega) with ⟨hk, hop2, hin, _⟩
  have hgj : gateAt ⟨compD C x5 n, 0⟩ j' = g := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', hgj']
  rw [hgj] at hop2 hin
  have hgt := hm (gateAt C ((compOrig C x5 n).getD j' 0)) (gateAt_mem (by omega))
  refine ⟨?_, ?_⟩
  · rw [hop2]; exact hgt.1
  · rw [hin, List.length_map]; exact hgt.2

lemma comp_readsBack (C : Circuit) (x5 : ℕ) (hx : x5 < C.gates.length) (hm : Monotone2 C)
    (hrb : ReadsBack 26 C) :
    ∀ n ≤ C.gates.length, ReadsBack 26 ⟨compD C x5 n, 0⟩ := by
  intro n hn
  induction n with
  | zero =>
    intro j hj
    simp [compD, compRun, compInit] at hj
  | succ n ih =>
    have hnk : n < C.gates.length := by omega
    have ih' := ih (by omega)
    by_cases hnx : n ≤ x5
    · have hd1 : compD C x5 (n + 1) = compD C x5 n ++ [gateAt C n] := by
        simp [compD, compRun, compStep, hnx]
      have hlen : (compD C x5 n).length = n := by
        rw [(comp_prefix_le C x5 hx n (by omega)).1, List.length_take_of_le (by omega)]
      intro j hj i hi
      rw [hd1, List.length_append] at hj
      simp only [List.length_cons, List.length_nil] at hj
      by_cases hjold : j < (compD C x5 n).length
      · rw [hd1, gateAt_append_left _ _ hjold] at hi
        exact ih' j hjold i hi
      · have hjeq : j = (compD C x5 n).length := by omega
        subst hjeq
        have hg : gateAt ⟨compD C x5 (n + 1), 0⟩ (compD C x5 n).length = gateAt C n := by
          unfold gateAt; rw [hd1]; exact getD_snoc_eq _ _ _
        rw [hg] at hi
        have h1 := hrb n hnk i hi
        omega
    · have hgt_op := (hm (gateAt C n) (gateAt_mem hnk)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgt_op
      rcases hgt_op with hop | hop
      · by_cases hany : (gateAt C n).inputs.any (compZ C x5 n) = true
        · have hd1 : compD C x5 (n + 1) = compD C x5 n := by
            simp [compD, compRun, compStep, hnx, hop, hany]
          rw [hd1]; exact ih'
        · have hd1 : compD C x5 (n + 1) =
              compD C x5 n ++ [⟨GateOp.and, (gateAt C n).inputs.map (compR C x5 n)⟩] := by
            simp [compD, compRun, compStep, hnx, hop, hany]
          intro j hj i hi
          rw [hd1, List.length_append] at hj
          simp only [List.length_cons, List.length_nil] at hj
          by_cases hjold : j < (compD C x5 n).length
          · rw [hd1, gateAt_append_left _ _ hjold] at hi
            exact ih' j hjold i hi
          · have hjeq : j = (compD C x5 n).length := by omega
            subst hjeq
            have hg : gateAt ⟨compD C x5 (n + 1), 0⟩ (compD C x5 n).length =
                ⟨GateOp.and, (gateAt C n).inputs.map (compR C x5 n)⟩ := by
              unfold gateAt; rw [hd1]; exact getD_snoc_eq _ _ _
            rw [hg, List.mem_map] at hi
            rcases hi with ⟨w, hw, rfl⟩
            have hwlt : w < 26 + n := hrb n hnk w hw
            have hwz : compZ C x5 n w = false := by
              cases hzw : compZ C x5 n w
              · rfl
              · exact False.elim (hany (List.any_eq_true.mpr ⟨w, hw, hzw⟩))
            exact (comp_range C x5 hx hm hrb n (by omega) w hwlt hwz).1
      · by_cases hall : (gateAt C n).inputs.all (compZ C x5 n) = true
        · have hd1 : compD C x5 (n + 1) = compD C x5 n := by
            simp [compD, compRun, compStep, hnx, hop, hall]
          rw [hd1]; exact ih'
        · by_cases hany : (gateAt C n).inputs.any (compZ C x5 n) = true
          · have hd1 : compD C x5 (n + 1) = compD C x5 n := by
              simp [compD, compRun, compStep, hnx, hop, hall, hany]
            rw [hd1]; exact ih'
          · have hd1 : compD C x5 (n + 1) =
                compD C x5 n ++ [⟨GateOp.or, (gateAt C n).inputs.map (compR C x5 n)⟩] := by
              simp [compD, compRun, compStep, hnx, hop, hall, hany]
            intro j hj i hi
            rw [hd1, List.length_append] at hj
            simp only [List.length_cons, List.length_nil] at hj
            by_cases hjold : j < (compD C x5 n).length
            · rw [hd1, gateAt_append_left _ _ hjold] at hi
              exact ih' j hjold i hi
            · have hjeq : j = (compD C x5 n).length := by omega
              subst hjeq
              have hg : gateAt ⟨compD C x5 (n + 1), 0⟩ (compD C x5 n).length =
                  ⟨GateOp.or, (gateAt C n).inputs.map (compR C x5 n)⟩ := by
                unfold gateAt; rw [hd1]; exact getD_snoc_eq _ _ _
              rw [hg, List.mem_map] at hi
              rcases hi with ⟨w, hw, rfl⟩
              have hwlt : w < 26 + n := hrb n hnk w hw
              have hwz : compZ C x5 n w = false := by
                cases hzw : compZ C x5 n w
                · rfl
                · exact False.elim (hany (List.any_eq_true.mpr ⟨w, hw, hzw⟩))
              exact (comp_range C x5 hx hm hrb n (by omega) w hwlt hwz).1

lemma comp_eval_equiv (C : Circuit) (x5 : ℕ) (hx : x5 < C.gates.length) (hm : Monotone2 C)
    (hrb : ReadsBack 26 C) (xs : List Bool) (hxs : xs.length = 26)
    (h5 : (C.wires xs).getD (26 + x5) false = false) :
    ∀ n ≤ C.gates.length,
      (∀ w < 26 + n, compZ C x5 n w = true → (C.wires xs).getD w false = false) ∧
      (∀ w < 26 + n, compZ C x5 n w = false →
        (Circuit.wires ⟨compD C x5 n, 0⟩ xs).getD (compR C x5 n w) false =
          (C.wires xs).getD w false) := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro w _ hz; simp [compZ, compRun, compInit] at hz
    · intro w hw _
      have hrw : compR C x5 0 w = w := rfl
      have hdw : Circuit.wires ⟨compD C x5 0, 0⟩ xs = xs := by
        simp [compD, compRun, compInit, Circuit.wires]
      rw [hrw, hdw]
      exact (foldl_wireStep_getD_lt C.gates xs (by omega)).symm
  | succ n ih =>
    have hnk : n < C.gates.length := by omega
    rcases ih (by omega) with ⟨ih1, ih2⟩
    have hrbD1 : ReadsBack 26 ⟨compD C x5 (n + 1), 0⟩ :=
      comp_readsBack C x5 hx hm hrb (n + 1) hn
    have hold_agree : ∀ w < 26 + n, compZ C x5 n w = false →
        (Circuit.wires ⟨compD C x5 (n + 1), 0⟩ xs).getD (compR C x5 n w) false =
          (C.wires xs).getD w false := by
      intro w hw hzw
      obtain ⟨⟨td, htd⟩, _⟩ := comp_mono_prefix C x5 (Nat.le_add_right n 1)
      have hrlt : compR C x5 n w < 26 + (compD C x5 n).length :=
        (comp_range C x5 hx hm hrb n (by omega) w hw hzw).1
      have heq1 : (Circuit.wires ⟨compD C x5 (n + 1), 0⟩ xs).getD (compR C x5 n w) false =
          (Circuit.wires ⟨compD C x5 n, 0⟩ xs).getD (compR C x5 n w) false := by
        show ((compD C x5 (n + 1)).foldl wireStep xs).getD _ false =
          ((compD C x5 n).foldl wireStep xs).getD _ false
        rw [htd]
        exact foldl_wireStep_take_getD _ _ xs (by omega)
      rw [heq1]
      exact ih2 w hw hzw
    have hstep1 : ∀ w < 26 + n, compZ C x5 (n + 1) w = true → (C.wires xs).getD w false = false := by
      intro w hw hz
      rw [(comp_rz_eq_else C x5 n w (by omega)).2] at hz
      exact ih1 w hw hz
    have hstep2 : ∀ w < 26 + n, compZ C x5 (n + 1) w = false →
        (Circuit.wires ⟨compD C x5 (n + 1), 0⟩ xs).getD (compR C x5 (n + 1) w) false =
          (C.wires xs).getD w false := by
      intro w hw hz
      have hrz := comp_rz_eq_else C x5 n w (by omega)
      rw [hrz.2] at hz
      rw [hrz.1]
      exact hold_agree w hw hz
    refine ⟨?_, ?_⟩
    · intro w hw hz
      by_cases hwold : w < 26 + n
      · exact hstep1 w hwold hz
      · have hweq : w = 26 + n := by omega
        subst hweq
        by_cases hnx : n ≤ x5
        · have hz_eq : compZ C x5 (n + 1) (26 + n) = decide (n = x5) := by
            simp [compZ, compRun, compStep, hnx]
          rw [hz_eq] at hz
          have hne : n = x5 := by simpa using hz
          subst hne
          exact h5
        · have hC : (C.wires xs).getD (26 + n) false =
              (gateAt C n).op.eval ((gateAt C n).inputs.map fun i => (C.wires xs).getD i false) :=
            readsBack_wire_at 26 C hrb xs hxs hnk
          rw [hC]
          have hgt_op := (hm (gateAt C n) (gateAt_mem hnk)).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgt_op
          rcases hgt_op with hop | hop
          · by_cases hany : (gateAt C n).inputs.any (compZ C x5 n) = true
            · rw [hop]
              simp only [GateOp.eval]
              rw [List.all_eq_false]
              obtain ⟨i, hi, hzi⟩ := List.any_eq_true.mp hany
              refine ⟨false, List.mem_map.mpr ⟨i, hi, ?_⟩, by decide⟩
              exact ih1 i (hrb n hnk i hi) hzi
            · have hzf : compZ C x5 (n + 1) (26 + n) = false := by
                simp [compZ, compRun, compStep, hnx, hop, hany]
              rw [hzf] at hz
              cases hz
          · by_cases hall : (gateAt C n).inputs.all (compZ C x5 n) = true
            · rw [hop]
              simp only [GateOp.eval]
              rw [List.any_eq_false]
              intro b hb
              rw [List.mem_map] at hb
              rcases hb with ⟨i, hi, rfl⟩
              have hzi : compZ C x5 n i = true := (List.all_eq_true.mp hall) i hi
              rw [ih1 i (hrb n hnk i hi) hzi]
              decide
            · by_cases hany : (gateAt C n).inputs.any (compZ C x5 n) = true
              · have hzf : compZ C x5 (n + 1) (26 + n) = false := by
                  simp [compZ, compRun, compStep, hnx, hop, hall, hany]
                rw [hzf] at hz
                cases hz
              · have hzf : compZ C x5 (n + 1) (26 + n) = false := by
                  simp [compZ, compRun, compStep, hnx, hop, hall, hany]
                rw [hzf] at hz
                cases hz
    · intro w hw hz
      by_cases hwold : w < 26 + n
      · exact hstep2 w hwold hz
      · have hweq : w = 26 + n := by omega
        subst hweq
        by_cases hnx : n ≤ x5
        · have hz_eq : compZ C x5 (n + 1) (26 + n) = decide (n = x5) := by
            simp [compZ, compRun, compStep, hnx]
          rw [hz_eq] at hz
          have hlt : n < x5 := by
            by_contra hge
            have hne : n = x5 := by omega
            subst hne; simp at hz
          have hpre := comp_prefix_le C x5 hx (n + 1) (by omega)
          have hr_eq : compR C x5 (n + 1) (26 + n) = 26 + n := hpre.2.2.1 (26 + n) (by omega)
          rw [hr_eq]
          show ((compD C x5 (n + 1)).foldl wireStep xs).getD (26 + n) false =
            (C.gates.foldl wireStep xs).getD (26 + n) false
          rw [hpre.1]
          have hsp : C.gates = C.gates.take (n + 1) ++ C.gates.drop (n + 1) :=
            (List.take_append_drop (n + 1) C.gates).symm
          conv_rhs => rw [hsp]
          have hlen_t : (C.gates.take (n + 1)).length = n + 1 :=
            List.length_take_of_le (by omega)
          exact (foldl_wireStep_take_getD (C.gates.take (n + 1)) (C.gates.drop (n + 1)) xs
            (by rw [hxs, hlen_t]; omega)).symm
        · have hC : (C.wires xs).getD (26 + n) false =
              (gateAt C n).op.eval ((gateAt C n).inputs.map fun i => (C.wires xs).getD i false) :=
            readsBack_wire_at 26 C hrb xs hxs hnk
          have hgt := hm (gateAt C n) (gateAt_mem hnk)
          have hgt_op := hgt.1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgt_op
          rcases hgt_op with hop | hop
          · have hany : ¬ ((gateAt C n).inputs.any (compZ C x5 n) = true) := by
              intro hany
              have hzt : compZ C x5 (n + 1) (26 + n) = true := by
                simp [compZ, compRun, compStep, hnx, hop, hany]
              rw [hzt] at hz; cases hz
            have hd1 : compD C x5 (n + 1) =
                compD C x5 n ++ [⟨GateOp.and, (gateAt C n).inputs.map (compR C x5 n)⟩] := by
              simp [compD, compRun, compStep, hnx, hop, hany]
            have hr1 : compR C x5 (n + 1) (26 + n) = 26 + (compD C x5 n).length := by
              simp [compR, compRun, compStep, hnx, hop, hany]
            rw [hr1, hC]
            have hD1 := readsBack_wire_at 26 ⟨compD C x5 (n + 1), 0⟩ hrbD1 xs hxs
              (k := (compD C x5 n).length) (by rw [hd1, List.length_append]; simp)
            have hg : gateAt ⟨compD C x5 (n + 1), 0⟩ (compD C x5 n).length =
                ⟨GateOp.and, (gateAt C n).inputs.map (compR C x5 n)⟩ := by
              unfold gateAt; rw [hd1]; exact getD_snoc_eq _ _ _
            rw [hD1, hg, hop, List.map_map]
            congr 1
            apply List.map_congr_left
            intro i hi
            have hilt : i < 26 + n := hrb n hnk i hi
            have hiz : compZ C x5 n i = false := by
              cases hzi : compZ C x5 n i
              · rfl
              · exact False.elim (hany (List.any_eq_true.mpr ⟨i, hi, hzi⟩))
            exact hold_agree i hilt hiz
          · have hall : ¬ ((gateAt C n).inputs.all (compZ C x5 n) = true) := by
              intro hall
              have hzt : compZ C x5 (n + 1) (26 + n) = true := by
                simp [compZ, compRun, compStep, hnx, hop, hall]
              rw [hzt] at hz; cases hz
            by_cases hany : (gateAt C n).inputs.any (compZ C x5 n) = true
            · set y := ((gateAt C n).inputs.filter (fun i => !compZ C x5 n i)).headD 0
              have hy := headD_filter_not_mem hgt.2 hany hall
              have hylt : y < 26 + n := hrb n hnk y hy.1
              have hd1 : compD C x5 (n + 1) = compD C x5 n := by
                simp [compD, compRun, compStep, hnx, hop, hall, hany]
              have hr1 : compR C x5 (n + 1) (26 + n) = compR C x5 n y := by
                dsimp only [compR, compRun, compStep]
                simp only [hnx, ↓reduceIte, hop, hall, hany, Bool.false_eq_true]
                rfl
              rw [hr1, hd1, hC, hop]
              rw [ih2 y hylt hy.2.1]
              simp only [GateOp.eval]
              cases hcy : (C.wires xs).getD y false
              · symm
                rw [List.any_eq_false]
                intro b hb
                rw [List.mem_map] at hb
                rcases hb with ⟨i, hi, rfl⟩
                rcases hy.2.2 i hi with rfl | hzi
                · rw [hcy]; decide
                · rw [ih1 i (hrb n hnk i hi) hzi]; decide
              · symm
                rw [List.any_eq_true]
                exact ⟨true, List.mem_map.mpr ⟨y, hy.1, hcy⟩, rfl⟩
            · have hd1 : compD C x5 (n + 1) =
                  compD C x5 n ++ [⟨GateOp.or, (gateAt C n).inputs.map (compR C x5 n)⟩] := by
                simp [compD, compRun, compStep, hnx, hop, hall, hany]
              have hr1 : compR C x5 (n + 1) (26 + n) = 26 + (compD C x5 n).length := by
                simp [compR, compRun, compStep, hnx, hop, hall, hany]
              rw [hr1, hC]
              have hD1 := readsBack_wire_at 26 ⟨compD C x5 (n + 1), 0⟩ hrbD1 xs hxs
                (k := (compD C x5 n).length) (by rw [hd1, List.length_append]; simp)
              have hg : gateAt ⟨compD C x5 (n + 1), 0⟩ (compD C x5 n).length =
                  ⟨GateOp.or, (gateAt C n).inputs.map (compR C x5 n)⟩ := by
                unfold gateAt; rw [hd1]; exact getD_snoc_eq _ _ _
              rw [hD1, hg, hop, List.map_map]
              congr 1
              apply List.map_congr_left
              intro i hi
              have hilt : i < 26 + n := hrb n hnk i hi
              have hiz : compZ C x5 n i = false := by
                cases hzi : compZ C x5 n i
                · rfl
                · exact False.elim (hany (List.any_eq_true.mpr ⟨i, hi, hzi⟩))
              exact hold_agree i hilt hiz

lemma comp_cone_drop_at (C : Circuit) (x5 : ℕ) (hx : x5 < C.gates.length) (hm : Monotone2 C) :
    ∀ g < C.gates.length, InCone 26 C x5 g → (compD C x5 (g + 1)).length ≤ g := by
  intro g
  induction g using Nat.strong_induction_on with
  | ind g ih =>
    intro hg hcone
    have hxlt : x5 < g := (inCone_lt 26 C hcone).1
    rw [inCone_iff_lt] at hcone
    rcases hcone with ⟨_, w, hw, hlo, hhi, hor⟩
    rcases hor with hweq | hsub
    · have hnx : ¬ (g ≤ x5) := by omega
      have hpre := comp_prefix_le C x5 hx (x5 + 1) (le_refl _)
      have hz_x5 : compZ C x5 g (26 + x5) = true := by
        have hstb := (comp_stable C x5 (n := x5 + 1) (m := g) (w := 26 + x5)
          (by omega) (by omega)).2
        rw [hstb, hpre.2.2.2]
        simp
      have hw_eq : w = 26 + x5 := by omega
      rw [← hw_eq] at hz_x5
      have hany : (gateAt C g).inputs.any (compZ C x5 g) = true :=
        List.any_eq_true.mpr ⟨w, hw, hz_x5⟩
      have hgt_op := (hm (gateAt C g) (gateAt_mem hg)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgt_op
      have hd1 : compD C x5 (g + 1) = compD C x5 g := by
        rcases hgt_op with hop | hop
        · simp [compD, compRun, compStep, hnx, hop, hany]
        · by_cases hall : (gateAt C g).inputs.all (compZ C x5 g) = true
          · simp [compD, compRun, compStep, hnx, hop, hall]
          · simp [compD, compRun, compStep, hnx, hop, hall, hany]
      rw [hd1]
      exact (comp_len C x5 g).2
    · have hwlt : w - 26 < g := by omega
      have hih := ih (w - 26) hwlt (by omega) hsub
      have hgr := comp_len_growth C x5 (n := w - 26 + 1) (m := g + 1) (by omega)
      omega

lemma comp_cone_drop (C : Circuit) (x5 x6 : ℕ) (hm : Monotone2 C) (hcone : InCone 26 C x5 x6) :
    (compD C x5 C.gates.length).length + 1 ≤ C.gates.length := by
  have hxlt := inCone_lt 26 C hcone
  have h1 := comp_cone_drop_at C x5 (by omega) hm x6 hxlt.2 hcone
  have h2 := comp_len_growth C x5 (n := x6 + 1) (m := C.gates.length) (by omega)
  omega

lemma inCone_D_to_C (C : Circuit) (x5 : ℕ) (hx : x5 < C.gates.length) (hm : Monotone2 C)
    (hrb : ReadsBack 26 C) :
    ∀ b' a', InCone 26 ⟨compD C x5 C.gates.length, 0⟩ a' b' →
      a' < (compD C x5 C.gates.length).length ∧
      b' < (compD C x5 C.gates.length).length ∧
      InCone 26 C ((compOrig C x5 C.gates.length).getD a' 0)
        ((compOrig C x5 C.gates.length).getD b' 0) := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | ind b' ih =>
    intro a' hcone
    have hlt := inCone_lt 26 ⟨compD C x5 C.gates.length, 0⟩ hcone
    have hb' : b' < (compD C x5 C.gates.length).length := hlt.2
    have ha' : a' < (compD C x5 C.gates.length).length := by omega
    refine ⟨ha', hb', ?_⟩
    rw [inCone_iff_lt] at hcone
    rcases hcone with ⟨_, w', hw', hlo', hhi', hor⟩
    have hlen_eq := (comp_len C x5 C.gates.length).1
    have hop := (comp_orig_props C x5 hm hrb hx C.gates.length (le_refl _)).1
    rcases hop b' (by omega) with ⟨hbN, _, hbin, hbz⟩
    rw [hbin, List.mem_map] at hw'
    rcases hw' with ⟨w, hw, rfl⟩
    set N := C.gates.length
    set b := (compOrig C x5 N).getD b' 0
    have hwltN : w < 26 + N := by
      have := hrb b hbN w hw
      omega
    have hwb : w < 26 + b := hrb b hbN w hw
    have hzr := comp_range C x5 hx hm hrb N (le_refl _) w hwltN (hbz w hw)
    rcases hzr.2.2 with h26 | ⟨hw26, c', hc', hrc, hccone⟩
    · omega
    · have hc'_eq : c' = compR C x5 N w - 26 := by omega
      have hc'_lt : c' < b' := by omega
      have hdir : InCone 26 C (w - 26) b := inCone_direct 26 C hbN hw hw26 hwb
      have hcb : InCone 26 C ((compOrig C x5 N).getD c' 0) b := by
        rcases hccone with heq | hsub
        · rw [heq]; exact hdir
        · exact inCone_trans 26 C hsub hdir
      rcases hor with rfl | hsubD
      · rw [← hc'_eq]; exact hcb
      · rw [← hc'_eq] at hsubD
        have hih := (ih c' hc'_lt a' hsubD).2.2
        exact inCone_trans 26 C hih hcb

lemma not_inCone_D_x5 (C : Circuit) (x5 : ℕ) (hx : x5 < C.gates.length) (hm : Monotone2 C)
    (hrb : ReadsBack 26 C) :
    ∀ b' < (compD C x5 C.gates.length).length,
      ¬ InCone 26 ⟨compD C x5 C.gates.length, 0⟩ x5 b' := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | ind b' ih =>
    intro hb' hcone
    rw [inCone_iff_lt] at hcone
    rcases hcone with ⟨_, w', hw', hlo', hhi', hor⟩
    have hlen_eq := (comp_len C x5 C.gates.length).1
    have hop := (comp_orig_props C x5 hm hrb hx C.gates.length (le_refl _)).1
    rcases hop b' (by omega) with ⟨hbN, _, hbin, hbz⟩
    rw [hbin, List.mem_map] at hw'
    rcases hw' with ⟨w, hw, rfl⟩
    set N := C.gates.length
    set b := (compOrig C x5 N).getD b' 0
    have hwltN : w < 26 + N := by
      have := hrb b hbN w hw
      omega
    have hne := (comp_range C x5 hx hm hrb N (le_refl _) w hwltN (hbz w hw)).2.1
    rcases hor with heq | hsub
    · omega
    · exact ih (compR C x5 N w - 26) (by omega) (by omega) hsub

lemma andPairs_lt (C : Circuit) (x5 x6 : ℕ) (hm : Monotone2 C) (hrb : ReadsBack 26 C)
    (hx5op : (gateAt C x5).op = GateOp.and) (hx6op : (gateAt C x6).op = GateOp.and)
    (hcone : InCone 26 C x5 x6) (hout : ℕ) :
    andPairs 26 ⟨compD C x5 C.gates.length ++ [⟨GateOp.or, [hout, 26 + x5]⟩],
      26 + (compD C x5 C.gates.length).length⟩ < andPairs 26 C := by
  have hxlt := inCone_lt 26 C hcone
  have hx5 : x5 < C.gates.length := by omega
  set N := C.gates.length
  set Dgs := compD C x5 N
  set D : Circuit := ⟨Dgs, 0⟩
  set topOr : Gate := ⟨GateOp.or, [hout, 26 + x5]⟩
  set C' : Circuit := ⟨Dgs ++ [topOr], 26 + Dgs.length⟩
  have hprops := comp_orig_props C x5 hm hrb hx5 N (le_refl _)
  have hlen_eq : Dgs.length = (compOrig C x5 N).length := (comp_len C x5 N).1
  have hS'_lt : ∀ p : ℕ × ℕ, p.1 < C'.gates.length → p.2 < C'.gates.length →
      (gateAt C' p.1).op = GateOp.and → (gateAt C' p.2).op = GateOp.and →
      p.1 < Dgs.length ∧ p.2 < Dgs.length := by
    intro p hp1 hp2 hop1 hop2
    have hC'len : C'.gates.length = Dgs.length + 1 := by
      simp [C', List.length_append]
    have hnot1 : p.1 ≠ Dgs.length := by
      intro heq
      rw [heq] at hop1
      have hg : gateAt C' Dgs.length = topOr := by
        unfold gateAt; exact getD_snoc_eq _ _ _
      rw [hg] at hop1
      cases hop1
    have hnot2 : p.2 ≠ Dgs.length := by
      intro heq
      rw [heq] at hop2
      have hg : gateAt C' Dgs.length = topOr := by
        unfold gateAt; exact getD_snoc_eq _ _ _
      rw [hg] at hop2
      cases hop2
    omega
  unfold andPairs
  let f : ℕ × ℕ → ℕ × ℕ := fun p => ((compOrig C x5 N).getD p.1 0, (compOrig C x5 N).getD p.2 0)
  rw [← Finset.card_image_of_injOn (f := f) (by
    intro p1 hp1 p2 hp2 heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp1 hp2
    obtain ⟨hp1a, hp1b⟩ := hS'_lt p1 hp1.1.1 hp1.1.2 hp1.2.1 hp1.2.2.1
    obtain ⟨hp2a, hp2b⟩ := hS'_lt p2 hp2.1.1 hp2.1.2 hp2.2.1 hp2.2.2.1
    have h1 : p1.1 = p2.1 := by
      have he1 := congrArg Prod.fst heq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact absurd he1 (ne_of_lt (hprops.2 p1.1 p2.1 hlt (by omega)))
      · exact absurd he1 (ne_of_gt (hprops.2 p2.1 p1.1 hgt (by omega)))
    have h2 : p1.2 = p2.2 := by
      have he2 := congrArg Prod.snd heq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact absurd he2 (ne_of_lt (hprops.2 p1.2 p2.2 hlt (by omega)))
      · exact absurd he2 (ne_of_gt (hprops.2 p2.2 p1.2 hgt (by omega)))
    exact Prod.ext h1 h2)]
  refine Finset.card_lt_card ⟨?_, fun hts => ?_⟩
  · intro q hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨p, hp, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    obtain ⟨hp1, hp2⟩ := hS'_lt p hp.1.1 hp.1.2 hp.2.1 hp.2.2.1
    have hconeD : InCone 26 D p.1 p.2 := (inCone_append_left 26 Dgs [topOr] hp2).mp hp.2.2.2
    have hDC := inCone_D_to_C C x5 hx5 hm hrb p.2 p.1 hconeD
    have h1 := hprops.1 p.1 (by omega)
    have h2 := hprops.1 p.2 (by omega)
    have hg1 : gateAt C' p.1 = gateAt D p.1 := gateAt_append_left Dgs [topOr] hp1
    have hg2 : gateAt C' p.2 = gateAt D p.2 := gateAt_append_left Dgs [topOr] hp2
    refine ⟨⟨h1.1, h2.1⟩, ?_, ?_, hDC.2.2⟩
    · rw [← h1.2.1, ← hg1]; exact hp.2.1
    · rw [← h2.2.1, ← hg2]; exact hp.2.2.1
  · have hmem := @hts (x5, x6) (by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hx5, hxlt.2⟩, hx5op, hx6op, hcone⟩)
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨p, hp, hfp⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨hp1, hp2⟩ := hS'_lt p hp.1.1 hp.1.2 hp.2.1 hp.2.2.1
    have hpre_x5 := comp_prefix_le C x5 hx5 (x5 + 1) (le_refl _)
    obtain ⟨_, ⟨to_, hto⟩⟩ := comp_mono_prefix C x5 (n := x5 + 1) (m := N) (by omega)
    have hx5_len : x5 < (compOrig C x5 (x5 + 1)).length := by
      rw [hpre_x5.2.1, List.length_range]; omega
    have hox5 : (compOrig C x5 N).getD x5 0 = x5 := by
      rw [hto, getD_app_left _ _ _ hx5_len, hpre_x5.2.1, List.getD_eq_getElem?_getD,
        List.getElem?_range (by omega)]
      rfl
    have hx5_orig : x5 < (compOrig C x5 N).length := by
      rw [hto, List.length_append]; omega
    have hp1_eq : p.1 = x5 := by
      have heq1 : (compOrig C x5 N).getD p.1 0 = (compOrig C x5 N).getD x5 0 := by
        rw [hox5]; exact congrArg Prod.fst hfp
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt1 | hgt1
      · exact absurd heq1 (ne_of_lt (hprops.2 p.1 x5 hlt1 hx5_orig))
      · exact absurd heq1 (ne_of_gt (hprops.2 x5 p.1 hgt1 (by omega)))
    have hconeD : InCone 26 D x5 p.2 := by
      rw [← hp1_eq]
      exact (inCone_append_left 26 Dgs [topOr] hp2).mp hp.2.2.2
    exact not_inCone_D_x5 C x5 hx5 hm hrb p.2 hp2 hconeD

lemma main_proof : have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x5 x6 ∧ ∀ (x7 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x7 → (x3.wires (x1 x7)).getD ((26 : ℕ) + x5) Bool.false = Bool.false) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 ∧ (x6.size < x3.size ∨ x6.size = x3.size ∧ PEqualNP.TopForm.andPairs (26 : ℕ) x6 < PEqualNP.TopForm.andPairs (26 : ℕ) x3) := by
  intro x1 x2 C hC hwit
  rcases hC with ⟨hm, hrb, hpos, hneg⟩
  rcases hwit with ⟨x5, x6, hx5op, hx6op, hcone, hx5q⟩
  have hxlt := inCone_lt 26 C hcone
  have hx5 : x5 < C.gates.length := by omega
  have hout_lt : C.output < 26 + C.gates.length := by
    have h0 : (0 : Fin 13) ∈ singerLines3 (0 : Fin 13) := by decide
    have hp0 := hpos 0 0 h0
    set xs0 := (List.ofFn fun x6 : Fin 13 => decide (x6 = (0 : Fin 13))) ++
      List.ofFn fun x6 : Fin 13 => decide (x6 = (0 : Fin 13))
    have hlen0 : (C.wires xs0).length = 26 + C.gates.length := by
      rw [wires_length_eq]
      simp [xs0]
    by_contra hge
    have hge' : (C.wires xs0).length ≤ C.output := by omega
    have hdef : C.eval xs0 = false := List.getD_eq_default (C.wires xs0) false hge'
    rw [hp0] at hdef
    cases hdef
  have hx1_len : ∀ Q : Finset (Fin 13), (x1 Q).length = 26 := by
    intro Q
    simp [x1]
  have hpair_len : ∀ p l : Fin 13,
      ((List.ofFn fun x6 : Fin 13 => decide (x6 = p)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = l)).length = 26 := by
    intro p l
    simp
  by_cases hzout : compZ C x5 C.gates.length C.output = true
  · set C' : Circuit := ⟨C.gates.take (x5 + 1), 26 + x5⟩
    refine ⟨C', ⟨?_, ?_, ?_, ?_⟩, Or.inl ?_⟩
    · intro g hg
      exact hm g (List.mem_of_mem_take hg)
    · intro j hj i hi
      have hjlen : j < x5 + 1 := by
        simp [C', List.length_take] at hj; omega
      have hgate : gateAt C' j = gateAt C j := by
        unfold gateAt
        have hsp : C.gates = C.gates.take (x5 + 1) ++ C.gates.drop (x5 + 1) :=
          (List.take_append_drop (x5 + 1) C.gates).symm
        conv_rhs => rw [hsp]
        exact (getD_app_left _ _ _ hj).symm
      rw [hgate] at hi
      exact hrb j (by omega) i hi
    · intro p l hpl
      set xs := (List.ofFn fun x6 : Fin 13 => decide (x6 = p)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = l)
      have hCtrue := hpos p l hpl
      have hx5true : (C.wires xs).getD (26 + x5) false = true := by
        by_contra hx5f
        have hx5f' : (C.wires xs).getD (26 + x5) false = false :=
          Bool.eq_false_iff.mpr hx5f
        have heq := (comp_eval_equiv C x5 hx5 hm hrb xs (hpair_len p l) hx5f'
          C.gates.length (le_refl _)).1 C.output hout_lt hzout
        change C.eval xs = false at heq
        rw [hCtrue] at heq
        cases heq
      have hpre_agree : (C'.wires xs).getD (26 + x5) false = (C.wires xs).getD (26 + x5) false := by
        change ((C.gates.take (x5 + 1)).foldl wireStep xs).getD (26 + x5) false =
          (C.gates.foldl wireStep xs).getD (26 + x5) false
        have hsp : C.gates = C.gates.take (x5 + 1) ++ C.gates.drop (x5 + 1) :=
          (List.take_append_drop (x5 + 1) C.gates).symm
        conv_rhs => rw [hsp]
        have hlen_t : (C.gates.take (x5 + 1)).length = x5 + 1 :=
          List.length_take_of_le (by omega)
        exact (foldl_wireStep_take_getD _ _ xs (by rw [hpair_len p l, hlen_t]; omega)).symm
      change (C'.wires xs).getD (26 + x5) false = true
      rw [hpre_agree, hx5true]
    · intro Q hQ
      have hx5f := hx5q Q hQ
      have hpre_agree : (C'.wires (x1 Q)).getD (26 + x5) false =
          (C.wires (x1 Q)).getD (26 + x5) false := by
        change ((C.gates.take (x5 + 1)).foldl wireStep (x1 Q)).getD (26 + x5) false =
          (C.gates.foldl wireStep (x1 Q)).getD (26 + x5) false
        have hsp : C.gates = C.gates.take (x5 + 1) ++ C.gates.drop (x5 + 1) :=
          (List.take_append_drop (x5 + 1) C.gates).symm
        conv_rhs => rw [hsp]
        have hlen_t : (C.gates.take (x5 + 1)).length = x5 + 1 :=
          List.length_take_of_le (by omega)
        exact (foldl_wireStep_take_getD _ _ (x1 Q) (by rw [hx1_len Q, hlen_t]; omega)).symm
      change (C'.wires (x1 Q)).getD (26 + x5) false = false
      rw [hpre_agree, hx5f]
    · simp only [Circuit.size, C', List.length_take]
      omega
  · have hzout_f : compZ C x5 C.gates.length C.output = false := Bool.eq_false_iff.mpr hzout
    set N := C.gates.length
    set Dgs := compD C x5 N
    set D : Circuit := ⟨Dgs, 0⟩
    set rOut := compR C x5 N C.output
    set topOr : Gate := ⟨GateOp.or, [rOut, 26 + x5]⟩
    set C' : Circuit := ⟨Dgs ++ [topOr], 26 + Dgs.length⟩
    have hmD : Monotone2 D := comp_monotone2 C x5 hx5 hm hrb N (le_refl _)
    have hrbD : ReadsBack 26 D := comp_readsBack C x5 hx5 hm hrb N (le_refl _)
    have hrOut_lt : rOut < 26 + Dgs.length :=
      (comp_range C x5 hx5 hm hrb N (le_refl _) C.output hout_lt hzout_f).1
    have hx5_lt_D : x5 + 1 ≤ Dgs.length := by
      have hpre_x5 := comp_prefix_le C x5 hx5 (x5 + 1) (le_refl _)
      have hlen_x5 : (compD C x5 (x5 + 1)).length = x5 + 1 := by
        rw [hpre_x5.1, List.length_take_of_le (by omega)]
      rw [← hlen_x5]
      exact comp_len_mono C x5 (by omega)
    have hrbC' : ReadsBack 26 C' := by
      intro j hj i hi
      rw [List.length_append] at hj
      simp only [List.length_cons, List.length_nil] at hj
      by_cases hjold : j < Dgs.length
      · rw [gateAt_append_left Dgs [topOr] hjold] at hi
        exact hrbD j hjold i hi
      · have hjeq : j = Dgs.length := by omega
        subst hjeq
        have hg : gateAt C' Dgs.length = topOr := by
          unfold gateAt; exact getD_snoc_eq _ _ _
        rw [hg] at hi
        simp only [topOr, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
    have hD_x5_agree : ∀ xs : List Bool, xs.length = 26 →
        (D.wires xs).getD (26 + x5) false = (C.wires xs).getD (26 + x5) false := by
      intro xs hxs
      have hpre_x5 := comp_prefix_le C x5 hx5 (x5 + 1) (le_refl _)
      obtain ⟨⟨td, htd⟩, _⟩ := comp_mono_prefix C x5 (n := x5 + 1) (m := N) (by omega)
      have hd_sp : Dgs = C.gates.take (x5 + 1) ++ td := by
        rw [← hpre_x5.1]; exact htd
      have hC_sp : C.gates = C.gates.take (x5 + 1) ++ C.gates.drop (x5 + 1) :=
        (List.take_append_drop (x5 + 1) C.gates).symm
      have hlen_t : (C.gates.take (x5 + 1)).length = x5 + 1 :=
        List.length_take_of_le (by omega)
      change (Dgs.foldl wireStep xs).getD (26 + x5) false =
        (C.gates.foldl wireStep xs).getD (26 + x5) false
      conv_lhs => rw [hd_sp]
      conv_rhs => rw [hC_sp]
      rw [foldl_wireStep_take_getD _ _ xs (by rw [hxs, hlen_t]; omega),
        foldl_wireStep_take_getD _ _ xs (by rw [hxs, hlen_t]; omega)]
    have hC'_eval : ∀ xs : List Bool, xs.length = 26 →
        C'.eval xs = ((D.wires xs).getD rOut false || (D.wires xs).getD (26 + x5) false) := by
      intro xs hxs
      have htop := readsBack_wire_at 26 C' hrbC' xs hxs (k := Dgs.length)
        (by simp [C', List.length_append])
      have hg : gateAt C' Dgs.length = topOr := by
        unfold gateAt; exact getD_snoc_eq _ _ _
      change (C'.wires xs).getD (26 + Dgs.length) false = _
      rw [htop, hg]
      have ha1 : (C'.wires xs).getD rOut false = (D.wires xs).getD rOut false := by
        change ((Dgs ++ [topOr]).foldl wireStep xs).getD rOut false =
          (Dgs.foldl wireStep xs).getD rOut false
        exact foldl_wireStep_take_getD _ _ xs (by rw [hxs]; exact hrOut_lt)
      have ha2 : (C'.wires xs).getD (26 + x5) false = (D.wires xs).getD (26 + x5) false := by
        change ((Dgs ++ [topOr]).foldl wireStep xs).getD (26 + x5) false =
          (Dgs.foldl wireStep xs).getD (26 + x5) false
        exact foldl_wireStep_take_getD _ _ xs (by rw [hxs]; omega)
      simp only [topOr, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq]
      rw [ha1, ha2]
    refine ⟨C', ⟨?_, hrbC', ?_, ?_⟩, ?_⟩
    · intro g hg
      simp only [C', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hgD | rfl
      · exact hmD g hgD
      · simp [topOr]
    · intro p l hpl
      set xs := (List.ofFn fun x6 : Fin 13 => decide (x6 = p)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = l)
      have hxs := hpair_len p l
      rw [hC'_eval xs hxs]
      by_cases hx5b : (C.wires xs).getD (26 + x5) false = true
      · rw [hD_x5_agree xs hxs, hx5b, Bool.or_true]
      · have hx5f : (C.wires xs).getD (26 + x5) false = false := Bool.eq_false_iff.mpr hx5b
        have hDr : (D.wires xs).getD rOut false = (C.wires xs).getD C.output false :=
          (comp_eval_equiv C x5 hx5 hm hrb xs hxs hx5f N (le_refl _)).2 C.output hout_lt hzout_f
        have hCtrue : (C.wires xs).getD C.output false = true := hpos p l hpl
        rw [hDr, hCtrue, Bool.true_or]
    · intro Q hQ
      have hx5f := hx5q Q hQ
      have hxs := hx1_len Q
      rw [hC'_eval (x1 Q) hxs]
      have hDr : (D.wires (x1 Q)).getD rOut false = (C.wires (x1 Q)).getD C.output false :=
        (comp_eval_equiv C x5 hx5 hm hrb (x1 Q) hxs hx5f N (le_refl _)).2
          C.output hout_lt hzout_f
      have hCfalse : (C.wires (x1 Q)).getD C.output false = false := hneg Q hQ
      rw [hD_x5_agree (x1 Q) hxs, hx5f, hDr, hCfalse]
      rfl
    · have hdrop := comp_cone_drop C x5 x6 hm hcone
      have hsz : C'.size ≤ C.size := by
        change (Dgs ++ [topOr]).length ≤ C.gates.length
        rw [List.length_append]
        simp only [List.length_cons, List.length_nil]
        exact hdrop
      rcases lt_or_eq_of_le hsz with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, andPairs_lt C x5 x6 hm hrb hx5op hx6op hcone rOut⟩

end PEqualNP.Outside.L_meta_5160

theorem PEqualNP.Outside.L_meta_5160 : have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x5 x6 ∧ ∀ (x7 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x7 → (x3.wires (x1 x7)).getD ((26 : ℕ) + x5) Bool.false = Bool.false) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 ∧ (x6.size < x3.size ∨ x6.size = x3.size ∧ PEqualNP.TopForm.andPairs (26 : ℕ) x6 < PEqualNP.TopForm.andPairs (26 : ℕ) x3) := by
  exact PEqualNP.Outside.L_meta_5160.main_proof
