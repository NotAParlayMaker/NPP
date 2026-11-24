import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1751

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def x1Set : Finset (Fin 13) :=
  {0, 1, 3, 9}

def linePts (w : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun p => p - w ∈ x1Set

def ptLines (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun w => p - w ∈ x1Set

lemma linePts_card (w : Fin 13) : (linePts w).card = 4 := by
  revert w
  decide

lemma ptLines_card (p : Fin 13) : (ptLines p).card = 4 := by
  revert p
  decide

lemma linePts_inter (w1 w2 : Fin 13) (hne : w1 ≠ w2) : (linePts w1 ∩ linePts w2).card ≤ 1 := by
  revert w1 w2 hne
  decide

lemma ptLines_inter (p1 p2 : Fin 13) (hne : p1 ≠ p2) : (ptLines p1 ∩ ptLines p2).card ≤ 1 := by
  revert p1 p2 hne
  decide

lemma incPairs_card :
    (Finset.univ.filter fun pw : Fin 13 × Fin 13 => pw.1 - pw.2 ∈ x1Set).card = 52 := by
  decide

def IsQuad (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ w : Fin 13, {p ∈ Q | p - w ∈ x1Set}.card ≤ 2

def q0 : Finset (Fin 13) :=
  {0, 1, 4, 6}

def q1 : Finset (Fin 13) :=
  {0, 1, 5, 11}

lemma isQuad_q0 : IsQuad q0 := by
  unfold IsQuad
  decide

lemma isQuad_q1 : IsQuad q1 := by
  unfold IsQuad
  decide

def shiftQ (Q : Finset (Fin 13)) (t : Fin 13) : Finset (Fin 13) :=
  Q.image (fun x => x + t)

lemma isQuad_shift (Q : Finset (Fin 13)) (t : Fin 13) (hQ : IsQuad Q) : IsQuad (shiftQ Q t) := by
  constructor
  · unfold shiftQ
    rw [Finset.card_image_of_injective _ (add_left_injective t)]
    exact hQ.1
  · intro w
    have hsub : {p ∈ shiftQ Q t | p - w ∈ x1Set} =
        ({q ∈ Q | q - (w - t) ∈ x1Set}).image (fun x => x + t) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image, shiftQ]
      constructor
      · rintro ⟨⟨q, hq, rfl⟩, hp⟩
        refine ⟨q, ⟨hq, ?_⟩, rfl⟩
        have heq : q - (w - t) = q + t - w := by abel
        rwa [heq]
      · rintro ⟨q, ⟨hq, hqt⟩, rfl⟩
        refine ⟨⟨q, hq, rfl⟩, ?_⟩
        have heq : q + t - w = q - (w - t) := by abel
        rwa [heq]
    rw [hsub, Finset.card_image_of_injective _ (add_left_injective t)]
    exact hQ.2 (w - t)

lemma mem_shiftQ_iff (Q : Finset (Fin 13)) (t p : Fin 13) :
    p ∈ shiftQ Q t ↔ p - t ∈ Q := by
  simp only [shiftQ, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have heq : q + t - t = q := by abel
    rwa [heq]
  · intro h
    exact ⟨p - t, h, by abel⟩

lemma miss_shiftQ_iff (Q : Finset (Fin 13)) (t w : Fin 13) :
    (∀ p ∈ shiftQ Q t, p - w ∉ x1Set) ↔ ∀ q ∈ Q, q - (w - t) ∉ x1Set := by
  simp only [shiftQ, Finset.mem_image]
  constructor
  · intro h q hq
    have heq : q - (w - t) = q + t - w := by abel
    rw [heq]
    exact h (q + t) ⟨q, hq, rfl⟩
  · rintro h p ⟨q, hq, rfl⟩
    have heq : q + t - w = q - (w - t) := by abel
    rw [heq]
    exact h q hq

lemma cov_pw_raw : ∀ p w : Fin 13, p - w ∉ x1Set →
    ∃ t : Fin 13, (p - t ∈ q0 ∧ ∀ q ∈ q0, q - (w - t) ∉ x1Set) ∨
      (p - t ∈ q1 ∧ ∀ q ∈ q1, q - (w - t) ∉ x1Set) := by
  decide

lemma cov_pp_raw : ∀ p1 p2 : Fin 13,
    ∃ t : Fin 13, (p1 - t ∈ q0 ∧ p2 - t ∈ q0) ∨ (p1 - t ∈ q1 ∧ p2 - t ∈ q1) := by
  decide

lemma cov_ll_raw : ∀ w1 w2 : Fin 13,
    ∃ t : Fin 13, ((∀ q ∈ q0, q - (w1 - t) ∉ x1Set) ∧ (∀ q ∈ q0, q - (w2 - t) ∉ x1Set)) ∨
      ((∀ q ∈ q1, q - (w1 - t) ∉ x1Set) ∧ (∀ q ∈ q1, q - (w2 - t) ∉ x1Set)) := by
  decide

lemma exists_quad_noninc (p w : Fin 13) (h : p - w ∉ x1Set) :
    ∃ Q : Finset (Fin 13), IsQuad Q ∧ p ∈ Q ∧ ∀ q ∈ Q, q - w ∉ x1Set := by
  obtain ⟨t, ⟨hp, hw⟩ | ⟨hp, hw⟩⟩ := cov_pw_raw p w h
  · exact ⟨shiftQ q0 t, isQuad_shift q0 t isQuad_q0, (mem_shiftQ_iff q0 t p).mpr hp,
      (miss_shiftQ_iff q0 t w).mpr hw⟩
  · exact ⟨shiftQ q1 t, isQuad_shift q1 t isQuad_q1, (mem_shiftQ_iff q1 t p).mpr hp,
      (miss_shiftQ_iff q1 t w).mpr hw⟩

lemma exists_quad_pp (p1 p2 : Fin 13) :
    ∃ Q : Finset (Fin 13), IsQuad Q ∧ p1 ∈ Q ∧ p2 ∈ Q := by
  obtain ⟨t, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := cov_pp_raw p1 p2
  · exact ⟨shiftQ q0 t, isQuad_shift q0 t isQuad_q0, (mem_shiftQ_iff q0 t p1).mpr h1,
      (mem_shiftQ_iff q0 t p2).mpr h2⟩
  · exact ⟨shiftQ q1 t, isQuad_shift q1 t isQuad_q1, (mem_shiftQ_iff q1 t p1).mpr h1,
      (mem_shiftQ_iff q1 t p2).mpr h2⟩

lemma exists_quad_ll (w1 w2 : Fin 13) :
    ∃ Q : Finset (Fin 13), IsQuad Q ∧ (∀ q ∈ Q, q - w1 ∉ x1Set) ∧ (∀ q ∈ Q, q - w2 ∉ x1Set) := by
  obtain ⟨t, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := cov_ll_raw w1 w2
  · exact ⟨shiftQ q0 t, isQuad_shift q0 t isQuad_q0, (miss_shiftQ_iff q0 t w1).mpr h1,
      (miss_shiftQ_iff q0 t w2).mpr h2⟩
  · exact ⟨shiftQ q1 t, isQuad_shift q1 t isQuad_q1, (miss_shiftQ_iff q1 t w1).mpr h1,
      (miss_shiftQ_iff q1 t w2).mpr h2⟩

lemma exists_quad_pt (p : Fin 13) :
    ∃ Q : Finset (Fin 13), IsQuad Q ∧ p ∈ Q := by
  obtain ⟨Q, hQ, hp, _⟩ := exists_quad_pp p p
  exact ⟨Q, hQ, hp⟩

lemma exists_quad_line (w : Fin 13) :
    ∃ Q : Finset (Fin 13), IsQuad Q ∧ ∀ q ∈ Q, q - w ∉ x1Set := by
  obtain ⟨Q, hQ, hw, _⟩ := exists_quad_ll w w
  exact ⟨Q, hQ, hw⟩

def pairInputVec (p w : Fin 13) : Fin 26 → Bool :=
  fun k => if h : k.val < 13 then decide (⟨k.val, h⟩ = p) else decide (⟨k.val - 13, by omega⟩ = w)

def quadInputVec (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  fun k => if h : k.val < 13 then decide (⟨k.val, h⟩ ∈ Q) else decide (∀ q ∈ Q, q - ⟨k.val - 13, by omega⟩ ∉ x1Set)

lemma ofFn_pairInputVec (p w : Fin 13) :
    List.ofFn (pairInputVec p w) =
      (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun j : Fin 13 => decide (j = w) := by
  refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
  rw [List.getElem_ofFn]
  by_cases h : i < 13
  · rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
    simp only [pairInputVec, h, dite_true]
  · rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn]
    simp only [pairInputVec, h, dite_false, List.length_ofFn]

lemma ofFn_quadInputVec (Q : Finset (Fin 13)) :
    List.ofFn (quadInputVec Q) =
      (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
        List.ofFn fun j : Fin 13 => decide (∀ q ∈ Q, q - j ∉ x1Set) := by
  refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
  rw [List.getElem_ofFn]
  by_cases h : i < 13
  · rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
    simp only [quadInputVec, h, dite_true]
  · rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn]
    simp only [quadInputVec, h, dite_false, List.length_ofFn]

lemma pairInputVec_castAdd (p w q : Fin 13) :
    pairInputVec p w (Fin.castAdd 13 q) = decide (q = p) := by
  simp [pairInputVec, q.isLt]

lemma pairInputVec_natAdd (p w v : Fin 13) :
    pairInputVec p w (Fin.natAdd 13 v) = decide (v = w) := by
  simp [pairInputVec]

lemma quadInputVec_castAdd (Q : Finset (Fin 13)) (q : Fin 13) :
    quadInputVec Q (Fin.castAdd 13 q) = decide (q ∈ Q) := by
  simp [quadInputVec, q.isLt]

lemma quadInputVec_natAdd (Q : Finset (Fin 13)) (v : Fin 13) :
    quadInputVec Q (Fin.natAdd 13 v) = decide (∀ q ∈ Q, q - v ∉ x1Set) := by
  simp [quadInputVec]

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def W (C : Circuit) (x : Fin 26 → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

lemma W_length (C : Circuit) (x : Fin 26 → Bool) :
    (C.wires (List.ofFn x)).length = 26 + C.gates.length := by
  change (wiresFrom C.gates (List.ofFn x)).length = 26 + C.gates.length
  rw [wiresFrom_length, List.length_ofFn]

lemma W_input (C : Circuit) (x : Fin 26 → Bool) (i : ℕ) (hi : i < 26) :
    W C x i = x ⟨i, hi⟩ := by
  unfold W
  change (wiresFrom C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [prefix_val _ _ _ (by simp [hi]), List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

lemma W_beyond (C : Circuit) (x : Fin 26 → Bool) (i : ℕ) (hi : 26 + C.gates.length ≤ i) :
    W C x i = false := by
  unfold W
  rw [List.getD_eq_default _ _ (by rw [W_length]; exact hi)]

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma W_gate (C : Circuit) (hR : ReadsBack 26 C) (x : Fin 26 → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    W C x (26 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => W C x i) := by
  have hsplit : C.gates = (C.gates.take j ++ [gateAt C j]) ++ C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) C.gates]
    rw [List.take_succ_eq_append_getElem hj, gateAt_eq C j hj]
  let w := wiresFrom (C.gates.take j) (List.ofFn x)
  have hw : w.length = 26 + j := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hj.le]
  have hread (i : ℕ) (hi : i < 26 + j) : w.getD i false = W C x i := by
    unfold W
    change w.getD i false = (wiresFrom C.gates (List.ofFn x)).getD i false
    conv_rhs => rw [hsplit, List.append_assoc, wiresFrom_append]
    exact (prefix_val _ w i (hw.symm ▸ hi)).symm
  have he : ((gateAt C j).inputs.map fun i => w.getD i false) =
      (gateAt C j).inputs.map (W C x) := by
    refine List.map_congr_left fun i hi => hread i (hR j hj i hi)
  unfold W
  change (wiresFrom C.gates (List.ofFn x)).getD (26 + j) false = _
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append]
  have hstep : wiresFrom [gateAt C j] w =
      w ++ [(gateAt C j).op.eval ((gateAt C j).inputs.map fun i => w.getD i false)] := rfl
  rw [hstep, prefix_val _ _ _ (by simp [hw])]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w.length ≤ 26 + j),
    hw, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  simp only [List.getD_eq_getElem?_getD] at he
  rw [he]
  congr 1

lemma W_or_iff (C : Circuit) (hR : ReadsBack 26 C) (x : Fin 26 → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    W C x (26 + j) = true ↔ ∃ i ∈ (gateAt C j).inputs, W C x i = true := by
  rw [W_gate C hR x j hj, hop]
  simp [GateOp.eval]

lemma W_and_iff (C : Circuit) (hR : ReadsBack 26 C) (x : Fin 26 → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    W C x (26 + j) = true ↔ ∀ i ∈ (gateAt C j).inputs, W C x i = true := by
  rw [W_gate C hR x j hj, hop]
  simp [GateOp.eval]

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  have hgs : C.gates = C.gates.take k ++ gateAt C k :: C.gates.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.drop_eq_getElem_cons hk, gateAt_eq C k hk]
  have hpre_len : (C.gates.take k).length = k := by simp; omega
  have hc : cones n C = (C.gates.drop (k + 1)).foldl (coneStep n)
      (coneStep n ((C.gates.take k).foldl (coneStep n) []) (gateAt C k)) := by
    simp only [cones]
    conv_lhs => rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : ((C.gates.take k).foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have h1 : (cones n C).getD k [] =
      ((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: ((C.gates.take k).foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n (C.gates.drop (k + 1)) _ k (by simp [coneStep, hl0])]
    have h := coneStep_getD_last n ((C.gates.take k).foldl (coneStep n) []) (gateAt C k)
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = ((C.gates.take k).foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n (C.gates.drop (k + 1)) _ m (by simp [coneStep, hl0]; omega)]
    exact coneStep_getD_lt n _ (gateAt C k) m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma inCone_lt (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j → i < j ∧ j < C.gates.length := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hij
    have hj : j < C.gates.length := by
      by_contra hge
      have hlen : (cones n C).length ≤ j := by
        unfold cones
        rw [coneFold_length]
        simp; omega
      have hem : (cones n C).getD j [] = [] := List.getD_eq_default _ _ hlen
      unfold InCone at hij
      rw [hem] at hij
      simp at hij
    refine ⟨?_, hj⟩
    rw [inCone_iff n C i j hj] at hij
    obtain ⟨w, _, hn, hlt, rfl | hsub⟩ := hij
    · omega
    · have := (ih (w - n) (by omega) hsub).1
      omega

lemma inCone_direct (n : ℕ) (C : Circuit) (hR : ReadsBack n C) (i k : ℕ)
    (hk : k < C.gates.length) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt := hR k hk (n + i) hm
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k j : ℕ)
    (hak : InCone n C a k) (hkj : InCone n C k j) : InCone n C a j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have hj := (inCone_lt n C k j hkj).2
    rw [inCone_iff n C k j hj] at hkj
    obtain ⟨w, hw, hn, hlt, hstep⟩ := hkj
    rw [inCone_iff n C a j hj]
    refine ⟨w, hw, hn, hlt, Or.inr ?_⟩
    rcases hstep with rfl | hsub
    · exact hak
    · exact ih (w - n) (by omega) hsub

def isOrGate (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

def suppStep (s : List (Finset (Fin 26))) (g : Gate) : List (Finset (Fin 26)) :=
  s ++ [if isOrGate g then g.inputs.foldl (fun acc i => acc ∪ s.getD i ∅) ∅ else ∅]

def suppList (C : Circuit) : List (Finset (Fin 26)) :=
  C.gates.foldl suppStep (List.ofFn fun i : Fin 26 => ({i} : Finset (Fin 26)))

def supp (C : Circuit) (w : ℕ) : Finset (Fin 26) :=
  (suppList C).getD w ∅

lemma suppFold_length (gs : List Gate) (s : List (Finset (Fin 26))) :
    (gs.foldl suppStep s).length = s.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [suppStep]
    omega

lemma suppStep_getD_lt (s : List (Finset (Fin 26))) (g : Gate) (i : ℕ) (hi : i < s.length) :
    (suppStep s g).getD i ∅ = s.getD i ∅ := by
  simp [suppStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma suppFold_getD_lt (gs : List Gate) (s : List (Finset (Fin 26))) (i : ℕ) (hi : i < s.length) :
    (gs.foldl suppStep s).getD i ∅ = s.getD i ∅ := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (suppStep s g) (by simp [suppStep]; omega)]
    exact suppStep_getD_lt s g i hi

lemma supp_input (C : Circuit) (i : ℕ) (hi : i < 26) :
    supp C i = {⟨i, hi⟩} := by
  unfold supp suppList
  rw [suppFold_getD_lt _ _ _ (by simp [hi]), List.getD_eq_getElem _ _ (by simp [hi]),
    List.getElem_ofFn]

lemma mem_foldl_union (l : List ℕ) (f : ℕ → Finset (Fin 26)) (acc : Finset (Fin 26))
    (z : Fin 26) :
    z ∈ l.foldl (fun a i => a ∪ f i) acc ↔ z ∈ acc ∨ ∃ u ∈ l, z ∈ f u := by
  induction l generalizing acc with
  | nil => simp
  | cons u l ih =>
    simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨w, hw, hzw⟩)
      · exact Or.inl h
      · exact Or.inr ⟨u, Or.inl rfl, h⟩
      · exact Or.inr ⟨w, Or.inr hw, hzw⟩
    · rintro (h | ⟨w, rfl | hw, hzw⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr hzw)
      · exact Or.inr ⟨w, hw, hzw⟩

lemma mem_supp_or (C : Circuit) (hR : ReadsBack 26 C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (z : Fin 26) :
    z ∈ supp C (26 + j) ↔ ∃ u ∈ (gateAt C j).inputs, z ∈ supp C u := by
  have hgs : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hj, gateAt_eq C j hj]
  let init : List (Finset (Fin 26)) := List.ofFn fun i : Fin 26 => ({i} : Finset (Fin 26))
  let preS := (C.gates.take j).foldl suppStep init
  have hinit_len : init.length = 26 := by simp [init]
  have hpre_len : preS.length = 26 + j := by
    simp only [preS, suppFold_length, hinit_len, List.length_take]
    omega
  have hsupp_eq : suppList C =
      (C.gates.drop (j + 1)).foldl suppStep (suppStep preS (gateAt C j)) := by
    change C.gates.foldl suppStep init = _
    conv_lhs => rw [hgs, List.foldl_append, List.foldl_cons]
  have hget : supp C (26 + j) = (suppStep preS (gateAt C j)).getD (26 + j) ∅ := by
    unfold supp
    rw [hsupp_eq, suppFold_getD_lt _ _ _ (by simp [suppStep, hpre_len])]
  have hlast : (suppStep preS (gateAt C j)).getD (26 + j) ∅ =
      (gateAt C j).inputs.foldl (fun acc i => acc ∪ preS.getD i ∅) ∅ := by
    have his : isOrGate (gateAt C j) = true := by simp [isOrGate, hop]
    simp [suppStep, List.getD_eq_getElem?_getD, hpre_len, his]
  have hpre_get (u : ℕ) (hu : u ∈ (gateAt C j).inputs) : preS.getD u ∅ = supp C u := by
    have hlt := hR j hj u hu
    conv_rhs =>
      unfold supp
      rw [hsupp_eq, suppFold_getD_lt _ _ _ (by simp [suppStep, hpre_len]; omega),
        suppStep_getD_lt _ _ _ (by rw [hpre_len]; exact hlt)]
  rw [hget, hlast, mem_foldl_union]
  simp only [Finset.notMem_empty, false_or]
  constructor
  · rintro ⟨u, hu, hz⟩
    exact ⟨u, hu, by rwa [← hpre_get u hu]⟩
  · rintro ⟨u, hu, hz⟩
    exact ⟨u, hu, by rwa [hpre_get u hu]⟩

def ValidFun (C : Circuit) : Prop :=
  (∀ p w : Fin 13, p - w ∈ x1Set →
    C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 = p)) ++
      List.ofFn fun x6 : Fin 13 => decide (x6 = w)) = true) ∧
  ∀ Q : Finset (Fin 13), Q.card = 4 →
    (∀ w : Fin 13, {p ∈ Q | p - w ∈ x1Set}.card ≤ 2) →
    C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 ∈ Q)) ++
      List.ofFn fun x6 : Fin 13 => decide (∀ q ∈ Q, q - x6 ∉ x1Set)) = false

def HasAndInAndCone (C : Circuit) : Prop :=
  ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j

def PureOr (C : Circuit) (w : ℕ) : Prop :=
  w < 26 ∨ ∃ j < C.gates.length, w = 26 + j ∧ (gateAt C j).op = GateOp.or ∧
    ∀ i, InCone 26 C i j → (gateAt C i).op = GateOp.or

lemma pureOr_step (C : Circuit) (hR : ReadsBack 26 C) (j : ℕ)
    (hj : j < C.gates.length) (hP : PureOr C (26 + j)) (u : ℕ) (hu : u ∈ (gateAt C j).inputs) :
    PureOr C u := by
  by_cases hlt : u < 26
  · exact Or.inl hlt
  · right
    have huR := hR j hj u hu
    refine ⟨u - 26, by omega, by omega, ?_, ?_⟩
    · have hcone : InCone 26 C (u - 26) j := by
        refine inCone_direct 26 C hR (u - 26) j hj ?_
        have heq : 26 + (u - 26) = u := by omega
        rwa [heq]
      rcases hP with h | ⟨j', _, heq, _, hall⟩
      · omega
      · have hjEq : j = j' := by omega
        subst hjEq
        exact hall (u - 26) hcone
    · intro i hi
      have hcone : InCone 26 C (u - 26) j := by
        refine inCone_direct 26 C hR (u - 26) j hj ?_
        have heq : 26 + (u - 26) = u := by omega
        rwa [heq]
      have hit : InCone 26 C i j := inCone_trans 26 C i (u - 26) j hi hcone
      rcases hP with h | ⟨j', _, heq, _, hall⟩
      · omega
      · have hjEq : j = j' := by omega
        subst hjEq
        exact hall i hit

lemma pureOr_of_and_input (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack 26 C)
    (hN : ¬ HasAndInAndCone C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (u : ℕ) (hu : u ∈ (gateAt C a).inputs) :
    PureOr C u := by
  by_cases hlt : u < 26
  · exact Or.inl hlt
  · right
    have huR := hR a ha u hu
    have hk : u - 26 < C.gates.length := by omega
    have hcone : InCone 26 C (u - 26) a := by
      refine inCone_direct 26 C hR (u - 26) a ha ?_
      have heq : 26 + (u - 26) = u := by omega
      rwa [heq]
    have hno_and (k : ℕ) (hklen : k < C.gates.length) (hck : InCone 26 C k a) :
        (gateAt C k).op = GateOp.or := by
      have hm := (hM (C.gates[k]) (List.getElem_mem hklen)).1
      rw [← gateAt_eq C k hklen] at hm
      rcases hm with hand | hor
      · exact False.elim (hN ⟨k, a, hand, hop, hck⟩)
      · exact hor
    refine ⟨u - 26, hk, by omega, hno_and (u - 26) hk hcone, fun i hi => ?_⟩
    have hilen := (inCone_lt 26 C i (u - 26) hi).1
    exact hno_and i (by omega) (inCone_trans 26 C i (u - 26) a hi hcone)

lemma W_pureOr_iff (C : Circuit) (hR : ReadsBack 26 C) (x : Fin 26 → Bool)
    (w : ℕ) (hP : PureOr C w) :
    W C x w = true ↔ ∃ z ∈ supp C w, x z = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    have hPs := hP
    rcases hP with hw | ⟨j, hj, rfl, hop, _⟩
    · rw [W_input C x w hw, supp_input C w hw]
      simp
    · rw [W_or_iff C hR x j hj hop]
      constructor
      · rintro ⟨u, hu, hwu⟩
        have hlt := hR j hj u hu
        have hPu := pureOr_step C hR j hj hPs u hu
        obtain ⟨z, hz, hxz⟩ := (ih u hlt hPu).mp hwu
        exact ⟨z, (mem_supp_or C hR j hj hop z).mpr ⟨u, hu, hz⟩, hxz⟩
      · rintro ⟨z, hz, hxz⟩
        obtain ⟨u, hu, hzu⟩ := (mem_supp_or C hR j hj hop z).mp hz
        have hlt := hR j hj u hu
        have hPu := pureOr_step C hR j hj hPs u hu
        exact ⟨u, hu, (ih u hlt hPu).mpr ⟨z, hzu, hxz⟩⟩

lemma supp_subset_of_inCone (C : Circuit) (hR : ReadsBack 26 C) (j k : ℕ)
    (hP : PureOr C (26 + k)) (hc : InCone 26 C j k) :
    PureOr C (26 + j) ∧ supp C (26 + j) ⊆ supp C (26 + k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hPs := hP
    rcases hP with hlt | ⟨k', hk, heq, hop, _⟩
    · omega
    · have hkEq : k = k' := by omega
      subst hkEq
      rw [inCone_iff 26 C j k hk] at hc
      obtain ⟨w, hw, hn, hlt, rfl | hsub⟩ := hc
      · have hPw := pureOr_step C hR k hk hPs w hw
        have heqw : 26 + (w - 26) = w := by omega
        refine ⟨heqw.symm ▸ hPw, fun z hz => (mem_supp_or C hR k hk hop z).mpr ⟨w, hw, ?_⟩⟩
        rwa [← heqw]
      · have hPw := pureOr_step C hR k hk hPs w hw
        have heqw : 26 + (w - 26) = w := by omega
        have hPw2 : PureOr C (26 + (w - 26)) := heqw.symm ▸ hPw
        obtain ⟨hPj, hsub_supp⟩ := ih (w - 26) (by omega) hPw2 hsub
        refine ⟨hPj, fun z hz => (mem_supp_or C hR k hk hop z).mpr ⟨w, hw, ?_⟩⟩
        rw [← heqw]
        exact hsub_supp hz

def OrStep (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k < C.gates.length, u = 26 + k ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs

def OrReach (C : Circuit) (root w : ℕ) : Prop :=
  Relation.ReflTransGen (OrStep C) root w

lemma orStep_lt (C : Circuit) (hR : ReadsBack 26 C) (u v : ℕ) (h : OrStep C u v) : v < u := by
  obtain ⟨k, hk, rfl, _, hv⟩ := h
  exact hR k hk v hv

lemma orReach_le (C : Circuit) (hR : ReadsBack 26 C) (u v : ℕ) (h : OrReach C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    have := orStep_lt C hR _ _ hstep
    omega

lemma orStep_sound (C : Circuit) (hR : ReadsBack 26 C) (x : Fin 26 → Bool) (u v : ℕ)
    (h : OrStep C u v) (hv : W C x v = true) : W C x u = true := by
  obtain ⟨k, hk, rfl, hop, hin⟩ := h
  exact (W_or_iff C hR x k hk hop).mpr ⟨v, hin, hv⟩

lemma orReach_sound (C : Circuit) (hR : ReadsBack 26 C) (x : Fin 26 → Bool) (u v : ℕ)
    (h : OrReach C u v) (hv : W C x v = true) : W C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_sound C hR x _ _ h1 ih

lemma orReach_leaf (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack 26 C) (x : Fin 26 → Bool) :
    ∀ u, u < 26 + C.gates.length → W C x u = true →
      ∃ v, OrReach C u v ∧ (v < 26 ∨ ∃ k < C.gates.length, v = 26 + k ∧ (gateAt C k).op = GateOp.and) ∧
        W C x v = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hwu
    by_cases hlt : u < 26
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl hlt, hwu⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = 26 + k := ⟨u - 26, by omega⟩
      have hk : k < C.gates.length := by omega
      have hm := (hM (C.gates[k]) (List.getElem_mem hk)).1
      rw [← gateAt_eq C k hk] at hm
      rcases hm with hand | hor
      · exact ⟨26 + k, Relation.ReflTransGen.refl, Or.inr ⟨k, hk, rfl, hand⟩, hwu⟩
      · obtain ⟨w, hw, hww⟩ := (W_or_iff C hR x k hk hor).mp hwu
        have hwlt := hR k hk w hw
        obtain ⟨v, hrv, hleaf, hwv⟩ := ih w hwlt (by omega) hww
        exact ⟨v, Relation.ReflTransGen.head ⟨k, hk, rfl, hor, hw⟩ hrv, hleaf, hwv⟩

lemma orReach_inCone (C : Circuit) (hR : ReadsBack 26 C) (root w : ℕ)
    (h : OrReach C root w) (hw : 26 ≤ w) :
    root = w ∨ (26 ≤ root ∧ InCone 26 C (w - 26) (root - 26)) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a b step _ ih =>
    obtain ⟨k, hk, rfl, _, hab⟩ := step
    right
    refine ⟨by omega, ?_⟩
    have heq : 26 + k - 26 = k := by omega
    rw [heq]
    rcases ih with hbw | ⟨hb, hcone⟩
    · refine inCone_direct 26 C hR (w - 26) k hk ?_
      have heqw : 26 + (w - 26) = b := by omega
      rwa [heqw]
    · have hdir : InCone 26 C (b - 26) k := by
        refine inCone_direct 26 C hR (b - 26) k hk ?_
        have heqb : 26 + (b - 26) = b := by omega
        rwa [heqb]
      exact inCone_trans 26 C (w - 26) (b - 26) k hcone hdir

lemma orReach_pureOr (C : Circuit) (hR : ReadsBack 26 C) (root w : ℕ)
    (hP : PureOr C root) (h : OrReach C root w) : PureOr C w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hP
  | head step _ ih =>
    obtain ⟨k, hk, rfl, _, hin⟩ := step
    exact ih (pureOr_step C hR k hk hP _ hin)

lemma orReach_supp_subset (C : Circuit) (hR : ReadsBack 26 C) (root w : ℕ)
    (hP : PureOr C root) (h : OrReach C root w) : supp C w ⊆ supp C root := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Finset.Subset.rfl
  | head step _ ih =>
    obtain ⟨k, hk, rfl, hop, hin⟩ := step
    have hPmid := pureOr_step C hR k hk hP _ hin
    have hsub := ih hPmid
    intro z hz
    exact (mem_supp_or C hR k hk hop z).mpr ⟨_, hin, hsub hz⟩

lemma eval_quadInputVec_false (C : Circuit) (hV : ValidFun C) (Q : Finset (Fin 13)) (hQ : IsQuad Q) :
    W C (quadInputVec Q) C.output = false := by
  have h := hV.2 Q hQ.1 hQ.2
  rw [← ofFn_quadInputVec Q] at h
  exact h

lemma eval_pairInputVec_true (C : Circuit) (hV : ValidFun C) (p w : Fin 13) (hinc : p - w ∈ x1Set) :
    W C (pairInputVec p w) C.output = true := by
  have h := hV.1 p w hinc
  rw [← ofFn_pairInputVec p w] at h
  exact h

lemma output_lt (C : Circuit) (hV : ValidFun C) : C.output < 26 + C.gates.length := by
  by_contra hge
  have h00 : (0 : Fin 13) - (0 : Fin 13) ∈ x1Set := by decide
  have ht := eval_pairInputVec_true C hV 0 0 h00
  have hf := W_beyond C (pairInputVec 0 0) C.output (by omega)
  rw [hf] at ht
  contradiction

lemma no_input_orReach (C : Circuit) (hR : ReadsBack 26 C) (hV : ValidFun C) (i : ℕ) (hi : i < 26) :
    ¬ OrReach C C.output i := by
  intro hr
  by_cases hp : i < 13
  · obtain ⟨Q, hQ, hmem⟩ := exists_quad_pt ⟨i, hp⟩
    have hwi : W C (quadInputVec Q) i = true := by
      rw [W_input C _ i hi]
      simp [quadInputVec, hp, hmem]
    have hwo := orReach_sound C hR (quadInputVec Q) C.output i hr hwi
    rw [eval_quadInputVec_false C hV Q hQ] at hwo
    contradiction
  · obtain ⟨Q, hQ, hmiss⟩ := exists_quad_line ⟨i - 13, by omega⟩
    have hwi : W C (quadInputVec Q) i = true := by
      rw [W_input C _ i hi]
      simpa [quadInputVec, hp] using hmiss
    have hwo := orReach_sound C hR (quadInputVec Q) C.output i hr hwi
    rw [eval_quadInputVec_false C hV Q hQ] at hwo
    contradiction

def ptOf (S : Finset (Fin 26)) : Finset (Fin 13) :=
  Finset.univ.filter fun p => Fin.castAdd 13 p ∈ S

def lnOf (S : Finset (Fin 26)) : Finset (Fin 13) :=
  Finset.univ.filter fun w => Fin.natAdd 13 w ∈ S

lemma ptOf_empty : ptOf ∅ = ∅ := by
  ext p; simp [ptOf]

lemma lnOf_empty : lnOf ∅ = ∅ := by
  ext w; simp [lnOf]

lemma ptOf_union (S1 S2 : Finset (Fin 26)) : ptOf (S1 ∪ S2) = ptOf S1 ∪ ptOf S2 := by
  ext p; simp [ptOf]

lemma lnOf_union (S1 S2 : Finset (Fin 26)) : lnOf (S1 ∪ S2) = lnOf S1 ∪ lnOf S2 := by
  ext w; simp [lnOf]

lemma ptOf_singleton_card (i : Fin 26) : (ptOf {i}).card ≤ 1 := by
  have hsub : ptOf {i} ⊆ if h : i.val < 13 then {⟨i.val, h⟩} else ∅ := by
    intro p hp
    simp only [ptOf, Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and] at hp
    have hval := congrArg Fin.val hp
    simp only [Fin.val_castAdd] at hval
    have hi : i.val < 13 := by omega
    simp only [hi, dite_true, Finset.mem_singleton]
    exact Fin.ext hval
  refine (Finset.card_le_card hsub).trans ?_
  split_ifs <;> simp

lemma lnOf_singleton_card (i : Fin 26) : (lnOf {i}).card ≤ 1 := by
  have hsub : lnOf {i} ⊆ if h : 13 ≤ i.val then {⟨i.val - 13, by omega⟩} else ∅ := by
    intro w hw
    simp only [lnOf, Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and] at hw
    have hval := congrArg Fin.val hw
    simp only [Fin.val_natAdd] at hval
    have hi : 13 ≤ i.val := by omega
    simp only [hi, dite_true, Finset.mem_singleton]
    exact Fin.ext (show w.val = i.val - 13 by omega)
  refine (Finset.card_le_card hsub).trans ?_
  split_ifs <;> simp

lemma mem_ptOf_iff (S : Finset (Fin 26)) (p : Fin 13) : p ∈ ptOf S ↔ Fin.castAdd 13 p ∈ S := by
  simp [ptOf]

lemma mem_lnOf_iff (S : Finset (Fin 26)) (w : Fin 13) : w ∈ lnOf S ↔ Fin.natAdd 13 w ∈ S := by
  simp [lnOf]

lemma nonempty_ptOf_or_lnOf (S : Finset (Fin 26)) (hS : S.Nonempty) :
    (ptOf S).Nonempty ∨ (lnOf S).Nonempty := by
  obtain ⟨k, hk⟩ := hS
  by_cases h : k.val < 13
  · left
    refine ⟨⟨k.val, h⟩, (mem_ptOf_iff S _).mpr ?_⟩
    convert hk using 1
    ext; simp
  · right
    refine ⟨⟨k.val - 13, by omega⟩, (mem_lnOf_iff S _).mpr ?_⟩
    convert hk using 1
    ext; simp; omega

lemma and_inputs_len2 (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack 26 C) (hV : ValidFun C)
    (hN : ¬ HasAndInAndCone C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (hr : OrReach C C.output (26 + a))
    (x0 : Fin 26 → Bool) (hx0 : W C x0 (26 + a) = true) :
    ∃ u v : ℕ, (gateAt C a).inputs = [u, v] ∧
      ((ptOf (supp C u)).Nonempty ∧ lnOf (supp C u) = ∅ ∧ ptOf (supp C v) = ∅ ∧ (lnOf (supp C v)).Nonempty ∨
       (lnOf (supp C u)).Nonempty ∧ ptOf (supp C u) = ∅ ∧ lnOf (supp C v) = ∅ ∧ (ptOf (supp C v)).Nonempty) := by
  have hlen := (hM (C.gates[a]) (List.getElem_mem ha)).2
  rw [← gateAt_eq C a ha] at hlen
  have hq_false (Q : Finset (Fin 13)) (hQ : IsQuad Q) :
      W C (quadInputVec Q) (26 + a) = false := by
    by_contra hne
    have hqt : W C (quadInputVec Q) (26 + a) = true := Bool.eq_true_of_not_eq_false hne
    have ho := orReach_sound C hR (quadInputVec Q) C.output (26 + a) hr hqt
    rw [eval_quadInputVec_false C hV Q hQ] at ho
    contradiction
  cases hin : (gateAt C a).inputs with
  | nil =>
    have htrue := (W_and_iff C hR (quadInputVec q0) a ha hop).mpr (by simp [hin])
    rw [hq_false q0 isQuad_q0] at htrue
    contradiction
  | cons u rest =>
    cases rest with
    | nil =>
      have hu_in : u ∈ (gateAt C a).inputs := by simp [hin]
      have hPu := pureOr_of_and_input C hM hR hN a ha hop u hu_in
      have hwu : W C x0 u = true := (W_and_iff C hR x0 a ha hop).mp hx0 u hu_in
      obtain ⟨z, hz, _⟩ := (W_pureOr_iff C hR x0 u hPu).mp hwu
      have hne : (supp C u).Nonempty := ⟨z, hz⟩
      rcases nonempty_ptOf_or_lnOf (supp C u) hne with ⟨p, hp⟩ | ⟨w, hw⟩
      · obtain ⟨Q, hQ, hpQ⟩ := exists_quad_pt p
        have hqz : W C (quadInputVec Q) u = true :=
          (W_pureOr_iff C hR (quadInputVec Q) u hPu).mpr
            ⟨Fin.castAdd 13 p, (mem_ptOf_iff _ p).mp hp, by rw [quadInputVec_castAdd]; simp [hpQ]⟩
        have hqa := (W_and_iff C hR (quadInputVec Q) a ha hop).mpr (fun i hi => by
          rw [hin] at hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          subst hi; exact hqz)
        rw [hq_false Q hQ] at hqa
        contradiction
      · obtain ⟨Q, hQ, hwQ⟩ := exists_quad_line w
        have hqz : W C (quadInputVec Q) u = true :=
          (W_pureOr_iff C hR (quadInputVec Q) u hPu).mpr
            ⟨Fin.natAdd 13 w, (mem_lnOf_iff _ w).mp hw, by rw [quadInputVec_natAdd]; simpa using hwQ⟩
        have hqa := (W_and_iff C hR (quadInputVec Q) a ha hop).mpr (fun i hi => by
          rw [hin] at hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          subst hi; exact hqz)
        rw [hq_false Q hQ] at hqa
        contradiction
    | cons v tail =>
      cases tail with
      | nil =>
        refine ⟨u, v, rfl, ?_⟩
        have hu_in : u ∈ (gateAt C a).inputs := by simp [hin]
        have hv_in : v ∈ (gateAt C a).inputs := by simp [hin]
        have hPu := pureOr_of_and_input C hM hR hN a ha hop u hu_in
        have hPv := pureOr_of_and_input C hM hR hN a ha hop v hv_in
        have hwu : W C x0 u = true := (W_and_iff C hR x0 a ha hop).mp hx0 u hu_in
        have hwv : W C x0 v = true := (W_and_iff C hR x0 a ha hop).mp hx0 v hv_in
        obtain ⟨zu, hzu, _⟩ := (W_pureOr_iff C hR x0 u hPu).mp hwu
        obtain ⟨zv, hzv, _⟩ := (W_pureOr_iff C hR x0 v hPv).mp hwv
        have hno_pp : ¬ ((ptOf (supp C u)).Nonempty ∧ (ptOf (supp C v)).Nonempty) := by
          rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩
          obtain ⟨Q, hQ, hQ1, hQ2⟩ := exists_quad_pp p1 p2
          have hqu : W C (quadInputVec Q) u = true :=
            (W_pureOr_iff C hR (quadInputVec Q) u hPu).mpr
              ⟨Fin.castAdd 13 p1, (mem_ptOf_iff _ p1).mp hp1, by rw [quadInputVec_castAdd]; simp [hQ1]⟩
          have hqv : W C (quadInputVec Q) v = true :=
            (W_pureOr_iff C hR (quadInputVec Q) v hPv).mpr
              ⟨Fin.castAdd 13 p2, (mem_ptOf_iff _ p2).mp hp2, by rw [quadInputVec_castAdd]; simp [hQ2]⟩
          have hqa := (W_and_iff C hR (quadInputVec Q) a ha hop).mpr (fun i hi => by
            rw [hin] at hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> assumption)
          rw [hq_false Q hQ] at hqa
          contradiction
        have hno_ll : ¬ ((lnOf (supp C u)).Nonempty ∧ (lnOf (supp C v)).Nonempty) := by
          rintro ⟨⟨w1, hw1⟩, ⟨w2, hw2⟩⟩
          obtain ⟨Q, hQ, hQ1, hQ2⟩ := exists_quad_ll w1 w2
          have hqu : W C (quadInputVec Q) u = true :=
            (W_pureOr_iff C hR (quadInputVec Q) u hPu).mpr
              ⟨Fin.natAdd 13 w1, (mem_lnOf_iff _ w1).mp hw1, by rw [quadInputVec_natAdd]; simpa using hQ1⟩
          have hqv : W C (quadInputVec Q) v = true :=
            (W_pureOr_iff C hR (quadInputVec Q) v hPv).mpr
              ⟨Fin.natAdd 13 w2, (mem_lnOf_iff _ w2).mp hw2, by rw [quadInputVec_natAdd]; simpa using hQ2⟩
          have hqa := (W_and_iff C hR (quadInputVec Q) a ha hop).mpr (fun i hi => by
            rw [hin] at hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> assumption)
          rw [hq_false Q hQ] at hqa
          contradiction
        rcases nonempty_ptOf_or_lnOf (supp C u) ⟨zu, hzu⟩ with hpu | hlu <;>
          rcases nonempty_ptOf_or_lnOf (supp C v) ⟨zv, hzv⟩ with hpv | hlv
        · exact False.elim (hno_pp ⟨hpu, hpv⟩)
        · left
          refine ⟨hpu, ?_, ?_, hlv⟩
          · rw [Finset.eq_empty_iff_forall_notMem]
            intro w hw
            exact hno_ll ⟨⟨w, hw⟩, hlv⟩
          · rw [Finset.eq_empty_iff_forall_notMem]
            intro p hp
            exact hno_pp ⟨hpu, ⟨p, hp⟩⟩
        · right
          refine ⟨hlu, ?_, ?_, hpv⟩
          · rw [Finset.eq_empty_iff_forall_notMem]
            intro p hp
            exact hno_pp ⟨⟨p, hp⟩, hpv⟩
          · rw [Finset.eq_empty_iff_forall_notMem]
            intro w hw
            exact hno_ll ⟨hlu, ⟨w, hw⟩⟩
        · exact False.elim (hno_ll ⟨hlu, hlv⟩)
      | cons _ _ =>
        rw [hin] at hlen
        simp at hlen

def actPts (C : Circuit) (a : ℕ) : Finset (Fin 13) :=
  ptOf (supp C ((gateAt C a).inputs.getD 0 0) ∪ supp C ((gateAt C a).inputs.getD 1 0))

def actLines (C : Circuit) (a : ℕ) : Finset (Fin 13) :=
  lnOf (supp C ((gateAt C a).inputs.getD 0 0) ∪ supp C ((gateAt C a).inputs.getD 1 0))

lemma act_and_props (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack 26 C) (hV : ValidFun C)
    (hN : ¬ HasAndInAndCone C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (hr : OrReach C C.output (26 + a))
    (x0 : Fin 26 → Bool) (hx0 : W C x0 (26 + a) = true) :
    (actPts C a).Nonempty ∧ (actLines C a).Nonempty ∧
    (∀ p ∈ actPts C a, ∀ w ∈ actLines C a, p - w ∈ x1Set) ∧
    ((actPts C a).card = 1 ∨ (actLines C a).card = 1) ∧
    (actPts C a).card ≤ 4 ∧ (actLines C a).card ≤ 4 ∧
    (∀ x, W C x (26 + a) = true ↔
      (∃ p ∈ actPts C a, x (Fin.castAdd 13 p) = true) ∧
      (∃ w ∈ actLines C a, x (Fin.natAdd 13 w) = true)) := by
  obtain ⟨u, v, hin, huv⟩ := and_inputs_len2 C hM hR hV hN a ha hop hr x0 hx0
  have hu0 : (gateAt C a).inputs.getD 0 0 = u := by simp [hin]
  have hv1 : (gateAt C a).inputs.getD 1 0 = v := by simp [hin]
  have hPu : PureOr C u := pureOr_of_and_input C hM hR hN a ha hop u (by simp [hin])
  have hPv : PureOr C v := pureOr_of_and_input C hM hR hN a ha hop v (by simp [hin])
  have hPne : (actPts C a).Nonempty := by
    unfold actPts
    rw [hu0, hv1, ptOf_union]
    rcases huv with ⟨h1, _⟩ | ⟨_, _, _, h2⟩
    · exact h1.mono Finset.subset_union_left
    · exact h2.mono Finset.subset_union_right
  have hLne : (actLines C a).Nonempty := by
    unfold actLines
    rw [hu0, hv1, lnOf_union]
    rcases huv with ⟨_, _, _, h2⟩ | ⟨h1, _⟩
    · exact h2.mono Finset.subset_union_right
    · exact h1.mono Finset.subset_union_left
  have hEval (x : Fin 26 → Bool) : W C x (26 + a) = true ↔
      (∃ p ∈ actPts C a, x (Fin.castAdd 13 p) = true) ∧
      (∃ w ∈ actLines C a, x (Fin.natAdd 13 w) = true) := by
    rw [W_and_iff C hR x a ha hop]
    have hall : (∀ i ∈ (gateAt C a).inputs, W C x i = true) ↔
        W C x u = true ∧ W C x v = true := by
      rw [hin]
      simp
    rw [hall, W_pureOr_iff C hR x u hPu, W_pureOr_iff C hR x v hPv]
    have hsplit (S : Finset (Fin 26)) : (∃ z ∈ S, x z = true) ↔
        (∃ p ∈ ptOf S, x (Fin.castAdd 13 p) = true) ∨
        (∃ w ∈ lnOf S, x (Fin.natAdd 13 w) = true) := by
      constructor
      · rintro ⟨z, hz, hxz⟩
        by_cases h : z.val < 13
        · left
          refine ⟨⟨z.val, h⟩, (mem_ptOf_iff S _).mpr ?_, ?_⟩
          · convert hz using 1; ext; simp
          · convert hxz using 2; ext; simp
        · right
          refine ⟨⟨z.val - 13, by omega⟩, (mem_lnOf_iff S _).mpr ?_, ?_⟩
          · convert hz using 1; ext; simp; omega
          · convert hxz using 2; ext; simp; omega
      · rintro (⟨p, hp, hxp⟩ | ⟨w, hw, hxw⟩)
        · exact ⟨Fin.castAdd 13 p, (mem_ptOf_iff S p).mp hp, hxp⟩
        · exact ⟨Fin.natAdd 13 w, (mem_lnOf_iff S w).mp hw, hxw⟩
    rw [hsplit (supp C u), hsplit (supp C v)]
    unfold actPts actLines
    rw [hu0, hv1, ptOf_union, lnOf_union]
    rcases huv with ⟨_, hlu, hpv, _⟩ | ⟨_, hpu, hlv, _⟩
    · simp only [hlu, hpv, Finset.notMem_empty, false_and, exists_false, or_false, false_or,
        Finset.empty_union, Finset.union_empty]
    · simp only [hpu, hlv, Finset.notMem_empty, false_and, exists_false, or_false, false_or,
        Finset.empty_union, Finset.union_empty]
      exact and_comm
  have hInc : ∀ p ∈ actPts C a, ∀ w ∈ actLines C a, p - w ∈ x1Set := by
    intro p hp w hw
    by_contra hni
    obtain ⟨Q, hQ, hpQ, hwQ⟩ := exists_quad_noninc p w hni
    have hwa : W C (quadInputVec Q) (26 + a) = true := by
      rw [hEval]
      refine ⟨⟨p, hp, by rw [quadInputVec_castAdd]; simp [hpQ]⟩,
        ⟨w, hw, by rw [quadInputVec_natAdd]; simpa using hwQ⟩⟩
    have hwo := orReach_sound C hR (quadInputVec Q) C.output (26 + a) hr hwa
    rw [eval_quadInputVec_false C hV Q hQ] at hwo
    contradiction
  have hStar : (actPts C a).card = 1 ∨ (actLines C a).card = 1 := by
    by_contra hboth
    push Not at hboth
    have hp2 : 1 < (actPts C a).card := by have := hPne.card_pos; omega
    have hl2 : 1 < (actLines C a).card := by have := hLne.card_pos; omega
    obtain ⟨p1, hp1, p2, hp2', hpne⟩ := Finset.one_lt_card.mp hp2
    obtain ⟨w1, hw1, w2, hw2', hwne⟩ := Finset.one_lt_card.mp hl2
    have hsub : {p1, p2} ⊆ linePts w1 ∩ linePts w2 := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      simp only [Finset.mem_inter, linePts, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hp with rfl | rfl
      · exact ⟨hInc p hp1 w1 hw1, hInc p hp1 w2 hw2'⟩
      · exact ⟨hInc p hp2' w1 hw1, hInc p hp2' w2 hw2'⟩
    have hc2 : 2 ≤ (linePts w1 ∩ linePts w2).card := by
      have hcard : ({p1, p2} : Finset (Fin 13)).card = 2 := Finset.card_pair hpne
      rw [← hcard]
      exact Finset.card_le_card hsub
    have hle1 := linePts_inter w1 w2 hwne
    omega
  have hP4 : (actPts C a).card ≤ 4 := by
    rcases hStar with h1 | h1
    · omega
    · obtain ⟨w, hw⟩ := hLne
      have hsub : actPts C a ⊆ linePts w := fun p hp => by
        simp only [linePts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hInc p hp w hw
      exact (Finset.card_le_card hsub).trans (by rw [linePts_card])
  have hL4 : (actLines C a).card ≤ 4 := by
    rcases hStar with h1 | h1
    · obtain ⟨p, hp⟩ := hPne
      have hsub : actLines C a ⊆ ptLines p := fun w hw => by
        simp only [ptLines, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hInc p hp w hw
      exact (Finset.card_le_card hsub).trans (by rw [ptLines_card])
    · omega
  exact ⟨hPne, hLne, hInc, hStar, hP4, hL4, hEval⟩

def colStep (col : Fin 13 → Fin 13) (p : Fin 13 × Fin 13) (z : Fin 13) : Fin 13 :=
  if col z = col p.2 then col p.1 else col z

lemma colStep_eq (col : Fin 13 → Fin 13) (p : Fin 13 × Fin 13) {a b : Fin 13}
    (h : col a = col b) : colStep col p a = colStep col p b := by
  simp [colStep, h]

lemma colStep_pair (col : Fin 13 → Fin 13) (p : Fin 13 × Fin 13) :
    colStep col p p.1 = colStep col p p.2 := by
  by_cases h : col p.1 = col p.2 <;> simp [colStep, h]

lemma foldl_colStep_eq (l : List (Fin 13 × Fin 13)) (col : Fin 13 → Fin 13) {a b : Fin 13}
    (h : col a = col b) : l.foldl colStep col a = l.foldl colStep col b := by
  induction l generalizing col with
  | nil => exact h
  | cons p l ih => exact ih (colStep col p) (colStep_eq col p h)

lemma foldl_colStep_mem (l : List (Fin 13 × Fin 13)) (col : Fin 13 → Fin 13) {p : Fin 13 × Fin 13}
    (hp : p ∈ l) : l.foldl colStep col p.1 = l.foldl colStep col p.2 := by
  induction l generalizing col with
  | nil => simp at hp
  | cons q l ih =>
    simp only [List.mem_cons, List.foldl_cons] at hp ⊢
    rcases hp with rfl | hmem
    · exact foldl_colStep_eq l (colStep col p) (colStep_pair col p)
    · exact ih (colStep col q) hmem

lemma card_image_colStep (S : Finset (Fin 13)) (col : Fin 13 → Fin 13) (p : Fin 13 × Fin 13) :
    (S.image col).card ≤ (S.image (colStep col p)).card + 1 := by
  have hsub : (S.image col).erase (col p.2) ⊆ S.image (colStep col p) := by
    intro c hc
    obtain ⟨hne, hc2⟩ := Finset.mem_erase.mp hc
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hc2
    refine Finset.mem_image.mpr ⟨s, hs, ?_⟩
    simp [colStep, hne]
  have h1 := Finset.card_le_card hsub
  have h2 : (S.image col).card ≤ ((S.image col).erase (col p.2)).card + 1 := by
    by_cases hm : col p.2 ∈ S.image col
    · rw [Finset.card_erase_add_one hm]
    · rw [Finset.erase_eq_of_notMem hm]; omega
  omega

lemma card_image_foldl_colStep (S : Finset (Fin 13)) (l : List (Fin 13 × Fin 13)) :
    S.card ≤ (S.image (l.foldl colStep id)).card + l.length := by
  have hgen : ∀ (col : Fin 13 → Fin 13),
      (S.image col).card ≤ (S.image (l.foldl colStep col)).card + l.length := by
    induction l with
    | nil => intro col; simp
    | cons p l ih =>
      intro col
      simp only [List.foldl_cons, List.length_cons]
      have h1 := card_image_colStep S col p
      have h2 := ih (colStep col p)
      omega
  simpa using hgen id

lemma star_wire_bound (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack 26 C)
    (proj : Finset (Fin 26) → Finset (Fin 13))
    (hEmpty : proj ∅ = ∅)
    (hUnion : ∀ S1 S2 : Finset (Fin 26), proj (S1 ∪ S2) = proj S1 ∪ proj S2)
    (A' B' : Finset ℕ) (sideWire : ℕ → ℕ)
    (hPure : ∀ a ∈ A', PureOr C (sideWire a))
    (hNe : ∀ a ∈ A', (proj (supp C (sideWire a))).Nonempty)
    (hB_or : ∀ j ∈ B', j < C.gates.length ∧ (gateAt C j).op = GateOp.or)
    (hB_closed : ∀ a ∈ A', ∀ w, OrReach C (sideWire a) w →
      2 ≤ (proj (supp C w)).card → ∃ j ∈ B', w = 26 + j) :
    (A'.biUnion fun a => proj (supp C (sideWire a))).card ≤ A'.card + B'.card := by
  classical
  let mergePair? : ℕ → Option (Fin 13 × Fin 13) := fun j =>
    match (gateAt C j).inputs with
    | [u, v] =>
      if hu : (proj (supp C u)).Nonempty then
        if hv : (proj (supp C v)).Nonempty then
          some (hu.choose, hv.choose)
        else none
      else none
    | _ => none
  let merges : List (Fin 13 × Fin 13) := B'.toList.filterMap mergePair?
  let finalCol : Fin 13 → Fin 13 := merges.foldl colStep id
  have hmerges_len : merges.length ≤ B'.card := by
    calc
      merges.length ≤ B'.toList.length := List.length_filterMap_le _ _
      _ = B'.card := Finset.length_toList B'
  have hsupp_or_nil (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
      (hin : (gateAt C j).inputs = []) : supp C (26 + j) = ∅ := by
    ext z
    rw [mem_supp_or C hR j hj hop z, hin]
    simp
  have hsupp_or_single (j u : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
      (hin : (gateAt C j).inputs = [u]) : supp C (26 + j) = supp C u := by
    ext z
    rw [mem_supp_or C hR j hj hop z, hin]
    simp
  have hsupp_or_pair (j u v : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
      (hin : (gateAt C j).inputs = [u, v]) : supp C (26 + j) = supp C u ∪ supp C v := by
    ext z
    rw [mem_supp_or C hR j hj hop z, hin]
    simp
  have hmono : ∀ w, ∀ a ∈ A', OrReach C (sideWire a) w → PureOr C w →
      ∀ x ∈ proj (supp C w), ∀ y ∈ proj (supp C w), finalCol x = finalCol y := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro a ha hrw hPw x hx y hy
      by_cases hc : (proj (supp C w)).card ≤ 1
      · have heq := Finset.card_le_one.mp hc x hx y hy
        rw [heq]
      · have hc2 : 2 ≤ (proj (supp C w)).card := by omega
        obtain ⟨j, hjB, rfl⟩ := hB_closed a ha w hrw hc2
        obtain ⟨hj, hop⟩ := hB_or j hjB
        have hlen := (hM (C.gates[j]) (List.getElem_mem hj)).2
        rw [← gateAt_eq C j hj] at hlen
        cases hin : (gateAt C j).inputs with
        | nil =>
          rw [hsupp_or_nil j hj hop hin, hEmpty] at hc2
          simp at hc2
        | cons u rest =>
          cases rest with
          | nil =>
            have hu_lt := hR j hj u (by simp [hin])
            have hu_step : OrStep C (26 + j) u := ⟨j, hj, rfl, hop, by simp [hin]⟩
            have hu_reach : OrReach C (sideWire a) u := Relation.ReflTransGen.tail hrw hu_step
            have hPu := pureOr_step C hR j hj hPw u (by simp [hin])
            rw [hsupp_or_single j u hj hop hin] at hx hy
            exact ih u hu_lt a ha hu_reach hPu x hx y hy
          | cons v tail =>
            cases tail with
            | nil =>
              have hu_lt := hR j hj u (by simp [hin])
              have hv_lt := hR j hj v (by simp [hin])
              have hu_reach : OrReach C (sideWire a) u :=
                Relation.ReflTransGen.tail hrw ⟨j, hj, rfl, hop, by simp [hin]⟩
              have hv_reach : OrReach C (sideWire a) v :=
                Relation.ReflTransGen.tail hrw ⟨j, hj, rfl, hop, by simp [hin]⟩
              have hPu := pureOr_step C hR j hj hPw u (by simp [hin])
              have hPv := pureOr_step C hR j hj hPw v (by simp [hin])
              rw [hsupp_or_pair j u v hj hop hin, hUnion] at hx hy
              by_cases huNe : (proj (supp C u)).Nonempty
              · by_cases hvNe : (proj (supp C v)).Nonempty
                · have hpair_mem : (huNe.choose, hvNe.choose) ∈ merges := by
                    rw [List.mem_filterMap]
                    refine ⟨j, Finset.mem_toList.mpr hjB, ?_⟩
                    simp only [mergePair?, hin]
                    split_ifs
                    rfl
                  have hcol_eq : finalCol huNe.choose = finalCol hvNe.choose :=
                    foldl_colStep_mem merges id hpair_mem
                  have hx_u : ∀ z ∈ proj (supp C u), finalCol z = finalCol huNe.choose :=
                    fun z hz => ih u hu_lt a ha hu_reach hPu z hz huNe.choose huNe.choose_spec
                  have hy_v : ∀ z ∈ proj (supp C v), finalCol z = finalCol hvNe.choose :=
                    fun z hz => ih v hv_lt a ha hv_reach hPv z hz hvNe.choose hvNe.choose_spec
                  rcases Finset.mem_union.mp hx with hxu | hxv <;>
                    rcases Finset.mem_union.mp hy with hyu | hyv
                  · rw [hx_u x hxu, hx_u y hyu]
                  · rw [hx_u x hxu, hy_v y hyv, hcol_eq]
                  · rw [hy_v x hxv, hx_u y hyu, hcol_eq]
                  · rw [hy_v x hxv, hy_v y hyv]
                · have huEmpty : proj (supp C v) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hvNe
                  rw [huEmpty, Finset.union_empty] at hx hy
                  exact ih u hu_lt a ha hu_reach hPu x hx y hy
              · have huEmpty : proj (supp C u) = ∅ := Finset.not_nonempty_iff_eq_empty.mp huNe
                rw [huEmpty, Finset.empty_union] at hx hy
                exact ih v hv_lt a ha hv_reach hPv x hx y hy
            | cons _ _ =>
              rw [hin] at hlen
              simp at hlen
  let S := A'.biUnion fun a => proj (supp C (sideWire a))
  have himg_sub : S.image finalCol ⊆ A'.image fun a => finalCol (if h : a ∈ A' then (hNe a h).choose else 0) := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨a, ha, hza⟩ := Finset.mem_biUnion.mp hz
    refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
    split_ifs
    exact (hmono (sideWire a) a ha Relation.ReflTransGen.refl (hPure a ha) z hza
      (hNe a ha).choose (hNe a ha).choose_spec).symm
  have h1 := card_image_foldl_colStep S merges
  have h2 := (Finset.card_le_card himg_sub).trans Finset.card_image_le
  change S.card ≤ (S.image finalCol).card + merges.length at h1
  change S.card ≤ A'.card + B'.card
  omega

lemma main_proof (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack 26 C) (hV : ValidFun C)
    (hN : ¬ HasAndInAndCone C) : 64 ≤ C.size := by
  classical
  let T : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = GateOp.or ∧ OrReach C C.output (26 + j)
  let A : Finset ℕ := (Finset.range C.gates.length).filter fun a =>
    (gateAt C a).op = GateOp.and ∧ OrReach C C.output (26 + a) ∧ ∃ x, W C x (26 + a) = true
  let B : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = GateOp.or ∧ (∃ a ∈ A, InCone 26 C j a) ∧ (supp C (26 + j)).Nonempty
  have hAT : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro j hjA hjT
    simp only [A, Finset.mem_filter] at hjA
    simp only [T, Finset.mem_filter] at hjT
    rw [hjA.2.1] at hjT
    exact GateOp.noConfusion hjT.2.1
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro j hjA hjB
    simp only [A, Finset.mem_filter] at hjA
    simp only [B, Finset.mem_filter] at hjB
    rw [hjA.2.1] at hjB
    exact GateOp.noConfusion hjB.2.1
  have hTB : Disjoint T B := by
    rw [Finset.disjoint_left]
    intro j hjT hjB
    simp only [T, Finset.mem_filter, Finset.mem_range] at hjT
    simp only [B, Finset.mem_filter, Finset.mem_range] at hjB
    obtain ⟨hj_len, hj_or, hrj⟩ := hjT
    obtain ⟨_, _, ⟨a, haA, hcone⟩, hne⟩ := hjB
    simp only [A, Finset.mem_filter, Finset.mem_range] at haA
    obtain ⟨ha_len, ha_and, _, _⟩ := haA
    have hPj : PureOr C (26 + j) := by
      refine Or.inr ⟨j, hj_len, rfl, hj_or, fun i hic => ?_⟩
      have hia := inCone_trans 26 C i j a hic hcone
      have hilt := (inCone_lt 26 C i a hia).1
      have hm := (hM (C.gates[i]) (List.getElem_mem (by omega))).1
      rw [← gateAt_eq C i (by omega)] at hm
      rcases hm with hand | hor
      · exact False.elim (hN ⟨i, a, hand, ha_and, hia⟩)
      · exact hor
    obtain ⟨z, hz⟩ := hne
    rcases nonempty_ptOf_or_lnOf _ ⟨z, hz⟩ with ⟨p, hp⟩ | ⟨w, hw⟩
    · obtain ⟨Q, hQ, hpQ⟩ := exists_quad_pt p
      have hwj : W C (quadInputVec Q) (26 + j) = true :=
        (W_pureOr_iff C hR (quadInputVec Q) (26 + j) hPj).mpr
          ⟨Fin.castAdd 13 p, (mem_ptOf_iff _ p).mp hp, by rw [quadInputVec_castAdd]; simp [hpQ]⟩
      have hwo := orReach_sound C hR (quadInputVec Q) C.output (26 + j) hrj hwj
      rw [eval_quadInputVec_false C hV Q hQ] at hwo
      contradiction
    · obtain ⟨Q, hQ, hwQ⟩ := exists_quad_line w
      have hwj : W C (quadInputVec Q) (26 + j) = true :=
        (W_pureOr_iff C hR (quadInputVec Q) (26 + j) hPj).mpr
          ⟨Fin.natAdd 13 w, (mem_lnOf_iff _ w).mp hw, by rw [quadInputVec_natAdd]; simpa using hwQ⟩
      have hwo := orReach_sound C hR (quadInputVec Q) C.output (26 + j) hrj hwj
      rw [eval_quadInputVec_false C hV Q hQ] at hwo
      contradiction
  have hSub_len : A ∪ T ∪ B ⊆ Finset.range C.gates.length := by
    intro j hj
    simp only [Finset.mem_union, A, T, B, Finset.mem_filter] at hj
    rcases hj with (h | h) | h <;> exact h.1
  have hSize_bound : A.card + T.card + B.card ≤ C.size := by
    have hdisj1 : Disjoint (A ∪ T) B := Finset.disjoint_union_left.mpr ⟨hAB, hTB⟩
    have hcard : (A ∪ T ∪ B).card = A.card + T.card + B.card := by
      rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hAT]
    rw [← hcard]
    exact (Finset.card_le_card hSub_len).trans (by simp [Circuit.size])
  have hAct (a : ℕ) (ha : a ∈ A) := by
    simp only [A, Finset.mem_filter, Finset.mem_range] at ha
    exact act_and_props C hM hR hV hN a ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.choose ha.2.2.2.choose_spec
  have hCov (p w : Fin 13) (hinc : p - w ∈ x1Set) :
      ∃ a ∈ A, p ∈ actPts C a ∧ w ∈ actLines C a := by
    have ht := eval_pairInputVec_true C hV p w hinc
    obtain ⟨v, hrv, hleaf, hwv⟩ :=
      orReach_leaf C hM hR (pairInputVec p w) C.output (output_lt C hV) ht
    rcases hleaf with hv26 | ⟨a, ha_len, rfl, ha_and⟩
    · exact False.elim (no_input_orReach C hR hV v hv26 hrv)
    · have haA : a ∈ A := by
        simp only [A, Finset.mem_filter, Finset.mem_range]
        exact ⟨ha_len, ha_and, hrv, ⟨pairInputVec p w, hwv⟩⟩
      have heval := (hAct a haA).2.2.2.2.2.2 (pairInputVec p w)
      obtain ⟨⟨p', hp', hpp'⟩, ⟨w', hw', hww'⟩⟩ := heval.mp hwv
      rw [pairInputVec_castAdd, decide_eq_true_eq] at hpp'
      rw [pairInputVec_natAdd, decide_eq_true_eq] at hww'
      subst hpp' hww'
      exact ⟨a, haA, hp', hw'⟩
  have hA13 : 13 ≤ A.card := by
    let incPairs := Finset.univ.filter fun pw : Fin 13 × Fin 13 => pw.1 - pw.2 ∈ x1Set
    have hsub : incPairs ⊆ A.biUnion fun a => actPts C a ×ˢ actLines C a := by
      intro pw hpw
      simp only [incPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hpw
      obtain ⟨a, haA, hp, hw⟩ := hCov pw.1 pw.2 hpw
      exact Finset.mem_biUnion.mpr ⟨a, haA, Finset.mem_product.mpr ⟨hp, hw⟩⟩
    have hprod_le (a : ℕ) (haA : a ∈ A) : (actPts C a ×ˢ actLines C a).card ≤ 4 := by
      have haP := hAct a haA
      rw [Finset.card_product]
      rcases haP.2.2.2.1 with h1 | h1
      · rw [h1, one_mul]; exact haP.2.2.2.2.2.1
      · rw [h1, mul_one]; exact haP.2.2.2.2.1
    have h52 := incPairs_card
    change incPairs.card = 52 at h52
    have hle := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hsum : ∑ a ∈ A, (actPts C a ×ˢ actLines C a).card ≤ ∑ _a ∈ A, 4 :=
      Finset.sum_le_sum fun a ha => hprod_le a ha
    simp only [Finset.sum_const, smul_eq_mul] at hsum
    omega
  have hT_bound : A.card ≤ T.card + 1 := by
    have hout_lt := output_lt C hV
    have hout_ge : 26 ≤ C.output := by
      by_contra hlt
      exact no_input_orReach C hR hV C.output (by omega) Relation.ReflTransGen.refl
    let outGate := C.output - 26
    have hout_len : outGate < C.gates.length := by omega
    have hout_eq : C.output = 26 + outGate := by omega
    have hout_or : (gateAt C outGate).op = GateOp.or := by
      have hm := (hM (C.gates[outGate]) (List.getElem_mem hout_len)).1
      rw [← gateAt_eq C outGate hout_len] at hm
      rcases hm with hand | hor
      · exfalso
        have hAsub : A ⊆ {outGate} := by
          intro a haA
          simp only [A, Finset.mem_filter, Finset.mem_range] at haA
          have hreach := haA.2.2.1
          rw [hout_eq] at hreach
          rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨v, hstep, _⟩
          · simp only [Finset.mem_singleton]; omega
          · obtain ⟨k, _, hk_eq, hk_or, _⟩ := hstep
            have : outGate = k := by omega
            subst this
            rw [hand] at hk_or
            exact GateOp.noConfusion hk_or
        have hle1 : A.card ≤ 1 := (Finset.card_le_card hAsub).trans (by simp)
        omega
      · exact hor
    have houtT : outGate ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_range]
      exact ⟨hout_len, hout_or, hout_eq ▸ Relation.ReflTransGen.refl⟩
    have hAT_sub : ((A ∪ T).erase outGate).image (fun g => 26 + g) ⊆
        T.biUnion (fun k => (gateAt C k).inputs.toFinset) := by
      intro w hw
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hg_ne, hg_mem⟩ := Finset.mem_erase.mp hg
      have hg_reach : OrReach C C.output (26 + g) := by
        rcases Finset.mem_union.mp hg_mem with hgA | hgT
        · simp only [A, Finset.mem_filter] at hgA; exact hgA.2.2.1
        · simp only [T, Finset.mem_filter] at hgT; exact hgT.2.2
      have hne_out : C.output ≠ 26 + g := by omega
      rcases Relation.ReflTransGen.cases_tail hg_reach with heq | ⟨u, hru, hstep⟩
      · exact False.elim (hne_out heq.symm)
      · obtain ⟨k, hk_len, rfl, hk_or, hk_in⟩ := hstep
        refine Finset.mem_biUnion.mpr ⟨k, ?_, List.mem_toFinset.mpr hk_in⟩
        simp only [T, Finset.mem_filter, Finset.mem_range]
        exact ⟨hk_len, hk_or, hru⟩
    have hLHS : (((A ∪ T).erase outGate).image (fun g => 26 + g)).card = A.card + T.card - 1 := by
      rw [Finset.card_image_of_injective _ (fun x y h => by omega)]
      rw [Finset.card_erase_of_mem (Finset.mem_union_right A houtT), Finset.card_union_of_disjoint hAT]
    have hRHS : (T.biUnion (fun k => (gateAt C k).inputs.toFinset)).card ≤ 2 * T.card := by
      refine (Finset.card_biUnion_le).trans ?_
      have hsum : ∑ k ∈ T, (gateAt C k).inputs.toFinset.card ≤ ∑ _k ∈ T, 2 := by
        refine Finset.sum_le_sum fun k hkT => ?_
        simp only [T, Finset.mem_filter, Finset.mem_range] at hkT
        have hlen := (hM (C.gates[k]) (List.getElem_mem hkT.1)).2
        rw [← gateAt_eq C k hkT.1] at hlen
        exact (List.toFinset_card_le _).trans hlen
      simpa [mul_comm] using hsum
    have hle := (Finset.card_le_card hAT_sub).trans hRHS
    omega
  have hAndSides (a : ℕ) (haA : a ∈ A) :
      ∃ u v : ℕ, (gateAt C a).inputs = [u, v] ∧
        ((ptOf (supp C u) = actPts C a ∧ lnOf (supp C u) = ∅ ∧
          ptOf (supp C v) = ∅ ∧ lnOf (supp C v) = actLines C a) ∨
         (lnOf (supp C u) = actLines C a ∧ ptOf (supp C u) = ∅ ∧
          lnOf (supp C v) = ∅ ∧ ptOf (supp C v) = actPts C a)) := by
    simp only [A, Finset.mem_filter, Finset.mem_range] at haA
    obtain ⟨u, v, hin, huv⟩ := and_inputs_len2 C hM hR hV hN a haA.1 haA.2.1 haA.2.2.1
      haA.2.2.2.choose haA.2.2.2.choose_spec
    have hu0 : (gateAt C a).inputs.getD 0 0 = u := by simp [hin]
    have hv1 : (gateAt C a).inputs.getD 1 0 = v := by simp [hin]
    refine ⟨u, v, hin, ?_⟩
    rcases huv with ⟨_, hlu, hpv, _⟩ | ⟨_, hpu, hlv, _⟩
    · left
      refine ⟨?_, hlu, hpv, ?_⟩
      · unfold actPts; rw [hu0, hv1, ptOf_union, hpv, Finset.union_empty]
      · unfold actLines; rw [hu0, hv1, lnOf_union, hlu, Finset.empty_union]
    · right
      refine ⟨?_, hpu, hlv, ?_⟩
      · unfold actLines; rw [hu0, hv1, lnOf_union, hlv, Finset.union_empty]
      · unfold actPts; rw [hu0, hv1, ptOf_union, hpu, Finset.empty_union]
  let lineSide (a : ℕ) : ℕ :=
    if (lnOf (supp C ((gateAt C a).inputs.getD 0 0))).Nonempty
    then (gateAt C a).inputs.getD 0 0 else (gateAt C a).inputs.getD 1 0
  let ptSide (a : ℕ) : ℕ :=
    if (ptOf (supp C ((gateAt C a).inputs.getD 0 0))).Nonempty
    then (gateAt C a).inputs.getD 0 0 else (gateAt C a).inputs.getD 1 0
  have hLineSide (a : ℕ) (haA : a ∈ A) :
      lineSide a ∈ (gateAt C a).inputs ∧ PureOr C (lineSide a) ∧
      ptOf (supp C (lineSide a)) = ∅ ∧ lnOf (supp C (lineSide a)) = actLines C a := by
    obtain ⟨u, v, hin, hcases⟩ := hAndSides a haA
    have haA' := haA
    simp only [A, Finset.mem_filter, Finset.mem_range] at haA'
    have hneL := (hAct a haA).2.1
    have hu0 : (gateAt C a).inputs.getD 0 0 = u := by simp [hin]
    have hv1 : (gateAt C a).inputs.getD 1 0 = v := by simp [hin]
    rcases hcases with ⟨_, hlu, hpv, hlv⟩ | ⟨hlu, hpu, hlv, _⟩
    · have hls : lineSide a = v := by
        dsimp only [lineSide]
        rw [hu0, hv1]
        split_ifs with hne
        · rw [hlu] at hne; exact False.elim (Finset.not_nonempty_empty hne)
        · rfl
      rw [hls]
      refine ⟨by simp [hin], pureOr_of_and_input C hM hR hN a haA'.1 haA'.2.1 v (by simp [hin]),
        hpv, hlv⟩
    · have hne_u : (lnOf (supp C u)).Nonempty := by rwa [hlu]
      have hls : lineSide a = u := by
        dsimp only [lineSide]
        rw [hu0]
        split_ifs
        rfl
      rw [hls]
      refine ⟨by simp [hin], pureOr_of_and_input C hM hR hN a haA'.1 haA'.2.1 u (by simp [hin]),
        hpu, hlu⟩
  have hPtSide (a : ℕ) (haA : a ∈ A) :
      ptSide a ∈ (gateAt C a).inputs ∧ PureOr C (ptSide a) ∧
      lnOf (supp C (ptSide a)) = ∅ ∧ ptOf (supp C (ptSide a)) = actPts C a := by
    obtain ⟨u, v, hin, hcases⟩ := hAndSides a haA
    have haA' := haA
    simp only [A, Finset.mem_filter, Finset.mem_range] at haA'
    have hneP := (hAct a haA).1
    have hu0 : (gateAt C a).inputs.getD 0 0 = u := by simp [hin]
    have hv1 : (gateAt C a).inputs.getD 1 0 = v := by simp [hin]
    rcases hcases with ⟨hpu, hlu, hpv, _⟩ | ⟨_, hpu, hlv, hpv⟩
    · have hne_u : (ptOf (supp C u)).Nonempty := by rwa [hpu]
      have hps : ptSide a = u := by
        dsimp only [ptSide]
        rw [hu0]
        split_ifs
        rfl
      rw [hps]
      refine ⟨by simp [hin], pureOr_of_and_input C hM hR hN a haA'.1 haA'.2.1 u (by simp [hin]),
        hlu, hpu⟩
    · have hps : ptSide a = v := by
        dsimp only [ptSide]
        rw [hu0, hv1]
        split_ifs with hne
        · rw [hpu] at hne; exact False.elim (Finset.not_nonempty_empty hne)
        · rfl
      rw [hps]
      refine ⟨by simp [hin], pureOr_of_and_input C hM hR hN a haA'.1 haA'.2.1 v (by simp [hin]),
        hlv, hpv⟩
  let centerOfAnd (a : ℕ) : Fin 13 ⊕ Fin 13 :=
    if h : 2 ≤ (actPts C a).card then
      Sum.inr (if hl : (actLines C a).Nonempty then hl.choose else 0)
    else
      Sum.inl (if hp : (actPts C a).Nonempty then hp.choose else 0)
  let Ap (p : Fin 13) : Finset ℕ := A.filter fun a => centerOfAnd a = Sum.inl p
  let Aw (w : Fin 13) : Finset ℕ := A.filter fun a => centerOfAnd a = Sum.inr w
  let Bp (p : Fin 13) : Finset ℕ := B.filter fun j =>
    2 ≤ (lnOf (supp C (26 + j))).card ∧ lnOf (supp C (26 + j)) ⊆ ptLines p
  let Bw (w : Fin 13) : Finset ℕ := B.filter fun j =>
    2 ≤ (ptOf (supp C (26 + j))).card ∧ ptOf (supp C (26 + j)) ⊆ linePts w
  have hAp_props (p : Fin 13) (a : ℕ) (ha : a ∈ Ap p) :
      a ∈ A ∧ actPts C a = {p} ∧ actLines C a ⊆ ptLines p := by
    simp only [Ap, Finset.mem_filter] at ha
    obtain ⟨haA, hcent⟩ := ha
    have haP := hAct a haA
    have hnot2 : ¬ 2 ≤ (actPts C a).card := by
      intro h2
      dsimp only [centerOfAnd] at hcent
      split_ifs at hcent
    have hc1 : (actPts C a).card = 1 := by have := haP.1.card_pos; omega
    have hp_eq : haP.1.choose = p := by
      dsimp only [centerOfAnd] at hcent
      split_ifs at hcent <;> first | exact Sum.inl.inj hcent | exact absurd haP.1 (by assumption)
    have hact_eq : actPts C a = {p} := by
      obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hc1
      have hmem : p ∈ actPts C a := hp_eq ▸ haP.1.choose_spec
      rw [hq, Finset.mem_singleton] at hmem
      rw [hq, hmem]
    refine ⟨haA, hact_eq, fun w hw => ?_⟩
    simp only [ptLines, Finset.mem_filter, Finset.mem_univ, true_and]
    exact haP.2.2.1 p (by rw [hact_eq]; exact Finset.mem_singleton_self p) w hw
  have hAw_props (w : Fin 13) (a : ℕ) (ha : a ∈ Aw w) :
      a ∈ A ∧ actLines C a = {w} ∧ actPts C a ⊆ linePts w := by
    simp only [Aw, Finset.mem_filter] at ha
    obtain ⟨haA, hcent⟩ := ha
    have haP := hAct a haA
    have h2 : 2 ≤ (actPts C a).card := by
      by_contra hnot2
      dsimp only [centerOfAnd] at hcent
      split_ifs at hcent
    have hc1 : (actLines C a).card = 1 := by
      rcases haP.2.2.2.1 with h | h
      · omega
      · exact h
    have hw_eq : haP.2.1.choose = w := by
      dsimp only [centerOfAnd] at hcent
      split_ifs at hcent <;> first | exact Sum.inr.inj hcent | exact absurd haP.2.1 (by assumption)
    have hact_eq : actLines C a = {w} := by
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc1
      have hmem : w ∈ actLines C a := hw_eq ▸ haP.2.1.choose_spec
      rw [hv, Finset.mem_singleton] at hmem
      rw [hv, hmem]
    refine ⟨haA, hact_eq, fun p hp => ?_⟩
    simp only [linePts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact haP.2.2.1 p hp w (by rw [hact_eq]; exact Finset.mem_singleton_self w)
  have hPtStar (p : Fin 13) : ((Ap p).biUnion (actLines C)).card ≤ (Ap p).card + (Bp p).card := by
    have hEq : (Ap p).biUnion (actLines C) = (Ap p).biUnion (fun a => lnOf (supp C (lineSide a))) := by
      refine Finset.biUnion_congr rfl fun a ha => ?_
      exact (hLineSide a (hAp_props p a ha).1).2.2.2.symm
    rw [hEq]
    refine star_wire_bound C hM hR lnOf lnOf_empty lnOf_union (Ap p) (Bp p) lineSide
      (fun a ha => (hLineSide a (hAp_props p a ha).1).2.1)
      (fun a ha => by
        rw [(hLineSide a (hAp_props p a ha).1).2.2.2]
        exact (hAct a (hAp_props p a ha).1).2.1)
      (fun j hj => by
        simp only [Bp, B, Finset.mem_filter, Finset.mem_range] at hj
        exact ⟨hj.1.1, hj.1.2.1⟩)
      ?_
    intro a ha w hrw hw2
    have hAp_a := hAp_props p a ha
    have haA := hAp_a.1
    have hLS := hLineSide a haA
    have hw26 : 26 ≤ w := by
      by_contra hlt
      have hs := supp_input C w (by omega)
      have hcard1 := lnOf_singleton_card ⟨w, by omega⟩
      rw [hs] at hw2
      omega
    have hr_cone := orReach_inCone C hR (lineSide a) w hrw hw26
    have haA' := haA
    simp only [A, Finset.mem_filter, Finset.mem_range] at haA'
    have hj_inCone : InCone 26 C (w - 26) a := by
      rcases hr_cone with h_eq | ⟨h26_ls, hsub_cone⟩
      · refine inCone_direct 26 C hR (w - 26) a haA'.1 ?_
        have hsum : 26 + (w - 26) = lineSide a := by omega
        rw [hsum]
        exact hLS.1
      · refine inCone_trans 26 C (w - 26) (lineSide a - 26) a hsub_cone ?_
        refine inCone_direct 26 C hR (lineSide a - 26) a haA'.1 ?_
        have hsum : 26 + (lineSide a - 26) = lineSide a := by omega
        rw [hsum]
        exact hLS.1
    have hw_pure := orReach_pureOr C hR (lineSide a) w hLS.2.1 hrw
    have hw_len : w - 26 < C.gates.length := (inCone_lt 26 C (w - 26) a hj_inCone).1.trans haA'.1
    have hw_or : (gateAt C (w - 26)).op = GateOp.or := by
      rcases hw_pure with hlt | ⟨j', _, heq, hop, _⟩
      · omega
      · have : w - 26 = j' := by omega
        rwa [this]
    have hw_sub : supp C w ⊆ supp C (lineSide a) := orReach_supp_subset C hR (lineSide a) w hLS.2.1 hrw
    have hw_ne : (supp C w).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty.mp hne, lnOf_empty] at hw2
      simp at hw2
    have hweq : 26 + (w - 26) = w := by omega
    refine ⟨w - 26, ?_, hweq.symm⟩
    simp only [Bp, B, Finset.mem_filter, Finset.mem_range, hweq]
    refine ⟨⟨hw_len, hw_or, ⟨a, haA, hj_inCone⟩, hw_ne⟩, hw2, fun l hl => ?_⟩
    have hl' : l ∈ lnOf (supp C (lineSide a)) := by
      rw [mem_lnOf_iff] at hl ⊢
      exact hw_sub hl
    rw [hLS.2.2.2] at hl'
    exact hAp_a.2.2 hl'
  have hLnStar (w : Fin 13) : ((Aw w).biUnion (actPts C)).card ≤ (Aw w).card + (Bw w).card := by
    have hEq : (Aw w).biUnion (actPts C) = (Aw w).biUnion (fun a => ptOf (supp C (ptSide a))) := by
      refine Finset.biUnion_congr rfl fun a ha => ?_
      exact (hPtSide a (hAw_props w a ha).1).2.2.2.symm
    rw [hEq]
    refine star_wire_bound C hM hR ptOf ptOf_empty ptOf_union (Aw w) (Bw w) ptSide
      (fun a ha => (hPtSide a (hAw_props w a ha).1).2.1)
      (fun a ha => by
        rw [(hPtSide a (hAw_props w a ha).1).2.2.2]
        exact (hAct a (hAw_props w a ha).1).1)
      (fun j hj => by
        simp only [Bw, B, Finset.mem_filter, Finset.mem_range] at hj
        exact ⟨hj.1.1, hj.1.2.1⟩)
      ?_
    intro a ha z hrz hz2
    have hAw_a := hAw_props w a ha
    have haA := hAw_a.1
    have hPS := hPtSide a haA
    have hz26 : 26 ≤ z := by
      by_contra hlt
      have hs := supp_input C z (by omega)
      have hcard1 := ptOf_singleton_card ⟨z, by omega⟩
      rw [hs] at hz2
      omega
    have hr_cone := orReach_inCone C hR (ptSide a) z hrz hz26
    have haA' := haA
    simp only [A, Finset.mem_filter, Finset.mem_range] at haA'
    have hj_inCone : InCone 26 C (z - 26) a := by
      rcases hr_cone with h_eq | ⟨h26_ps, hsub_cone⟩
      · refine inCone_direct 26 C hR (z - 26) a haA'.1 ?_
        have hsum : 26 + (z - 26) = ptSide a := by omega
        rw [hsum]
        exact hPS.1
      · refine inCone_trans 26 C (z - 26) (ptSide a - 26) a hsub_cone ?_
        refine inCone_direct 26 C hR (ptSide a - 26) a haA'.1 ?_
        have hsum : 26 + (ptSide a - 26) = ptSide a := by omega
        rw [hsum]
        exact hPS.1
    have hz_pure := orReach_pureOr C hR (ptSide a) z hPS.2.1 hrz
    have hz_len : z - 26 < C.gates.length := (inCone_lt 26 C (z - 26) a hj_inCone).1.trans haA'.1
    have hz_or : (gateAt C (z - 26)).op = GateOp.or := by
      rcases hz_pure with hlt | ⟨j', _, heq, hop, _⟩
      · omega
      · have : z - 26 = j' := by omega
        rwa [this]
    have hz_sub : supp C z ⊆ supp C (ptSide a) := orReach_supp_subset C hR (ptSide a) z hPS.2.1 hrz
    have hz_ne : (supp C z).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty.mp hne, ptOf_empty] at hz2
      simp at hz2
    have hzeq : 26 + (z - 26) = z := by omega
    refine ⟨z - 26, ?_, hzeq.symm⟩
    simp only [Bw, B, Finset.mem_filter, Finset.mem_range, hzeq]
    refine ⟨⟨hz_len, hz_or, ⟨a, haA, hj_inCone⟩, hz_ne⟩, hz2, fun q hq => ?_⟩
    have hq' : q ∈ ptOf (supp C (ptSide a)) := by
      rw [mem_ptOf_iff] at hq ⊢
      exact hz_sub hq
    rw [hPS.2.2.2] at hq'
    exact hAw_a.2.2 hq'
  have hB_pure_side (j : ℕ) (hjB : j ∈ B) :
      ptOf (supp C (26 + j)) = ∅ ∨ lnOf (supp C (26 + j)) = ∅ := by
    simp only [B, Finset.mem_filter, Finset.mem_range] at hjB
    obtain ⟨hj_len, _, ⟨a, haA, hcone⟩, _⟩ := hjB
    have haA' := haA
    simp only [A, Finset.mem_filter, Finset.mem_range] at haA'
    rw [inCone_iff 26 C j a haA'.1] at hcone
    obtain ⟨w, hw_in, h26, hlt, rfl | hsub⟩ := hcone
    · have hweq : 26 + (w - 26) = w := by omega
      rw [hweq]
      obtain ⟨u, v, hin, hcases⟩ := hAndSides a haA
      rw [hin] at hw_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw_in
      rcases hw_in with rfl | rfl <;> rcases hcases with ⟨_, hlu, hpv, _⟩ | ⟨_, hpu, hlv, _⟩
      · exact Or.inr hlu
      · exact Or.inl hpu
      · exact Or.inl hpv
      · exact Or.inr hlv
    · have hPw := pureOr_of_and_input C hM hR hN a haA'.1 haA'.2.1 w hw_in
      have hweq : 26 + (w - 26) = w := by omega
      have hsub_supp := (supp_subset_of_inCone C hR j (w - 26) (hweq.symm ▸ hPw) hsub).2
      rw [hweq] at hsub_supp
      obtain ⟨u, v, hin, hcases⟩ := hAndSides a haA
      rw [hin] at hw_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw_in
      have hmono_pt : ptOf (supp C w) = ∅ → ptOf (supp C (26 + j)) = ∅ := by
        intro h0
        rw [Finset.eq_empty_iff_forall_notMem] at h0 ⊢
        intro p hp
        exact h0 p ((mem_ptOf_iff _ p).mpr (hsub_supp ((mem_ptOf_iff _ p).mp hp)))
      have hmono_ln : lnOf (supp C w) = ∅ → lnOf (supp C (26 + j)) = ∅ := by
        intro h0
        rw [Finset.eq_empty_iff_forall_notMem] at h0 ⊢
        intro l hl
        exact h0 l ((mem_lnOf_iff _ l).mpr (hsub_supp ((mem_lnOf_iff _ l).mp hl)))
      rcases hw_in with rfl | rfl <;> rcases hcases with ⟨_, hlu, hpv, _⟩ | ⟨_, hpu, hlv, _⟩
      · exact Or.inr (hmono_ln hlu)
      · exact Or.inl (hmono_pt hpu)
      · exact Or.inl (hmono_pt hpv)
      · exact Or.inr (hmono_ln hlv)
  have hB_sum : (∑ p : Fin 13, (Bp p).card) + (∑ w : Fin 13, (Bw w).card) ≤ B.card := by
    have hdisj_pp : ∀ p1 ∈ (Finset.univ : Finset (Fin 13)), ∀ p2 ∈ (Finset.univ : Finset (Fin 13)),
        p1 ≠ p2 → Disjoint (Bp p1) (Bp p2) := by
      intro p1 _ p2 _ hne
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Bp, Finset.mem_filter] at hj1 hj2
      have hsub : lnOf (supp C (26 + j)) ⊆ ptLines p1 ∩ ptLines p2 :=
        Finset.subset_inter hj1.2.2 hj2.2.2
      have hc2 := hj1.2.1.trans (Finset.card_le_card hsub)
      have hle1 := ptLines_inter p1 p2 hne
      omega
    have hdisj_ww : ∀ w1 ∈ (Finset.univ : Finset (Fin 13)), ∀ w2 ∈ (Finset.univ : Finset (Fin 13)),
        w1 ≠ w2 → Disjoint (Bw w1) (Bw w2) := by
      intro w1 _ w2 _ hne
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Bw, Finset.mem_filter] at hj1 hj2
      have hsub : ptOf (supp C (26 + j)) ⊆ linePts w1 ∩ linePts w2 :=
        Finset.subset_inter hj1.2.2 hj2.2.2
      have hc2 := hj1.2.1.trans (Finset.card_le_card hsub)
      have hle1 := linePts_inter w1 w2 hne
      omega
    have hdisj_pw : Disjoint (Finset.univ.biUnion Bp) (Finset.univ.biUnion Bw) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      obtain ⟨p, _, hjp⟩ := Finset.mem_biUnion.mp hj1
      obtain ⟨w, _, hjw⟩ := Finset.mem_biUnion.mp hj2
      simp only [Bp, Finset.mem_filter] at hjp
      simp only [Bw, Finset.mem_filter] at hjw
      rcases hB_pure_side j hjp.1 with hp0 | hl0
      · rw [hp0] at hjw; simp at hjw
      · rw [hl0] at hjp; simp at hjp
    have hsub_B : (Finset.univ.biUnion Bp) ∪ (Finset.univ.biUnion Bw) ⊆ B := by
      intro j hj
      rcases Finset.mem_union.mp hj with h1 | h2
      · obtain ⟨p, _, hjp⟩ := Finset.mem_biUnion.mp h1
        exact (Finset.mem_filter.mp hjp).1
      · obtain ⟨w, _, hjw⟩ := Finset.mem_biUnion.mp h2
        exact (Finset.mem_filter.mp hjw).1
    rw [← Finset.card_biUnion hdisj_pp, ← Finset.card_biUnion hdisj_ww,
      ← Finset.card_union_of_disjoint hdisj_pw]
    exact Finset.card_le_card hsub_B
  have hA_sum : (∑ p : Fin 13, (Ap p).card) + (∑ w : Fin 13, (Aw w).card) = A.card := by
    have hdisj_pp : ∀ p1 ∈ (Finset.univ : Finset (Fin 13)), ∀ p2 ∈ (Finset.univ : Finset (Fin 13)),
        p1 ≠ p2 → Disjoint (Ap p1) (Ap p2) := by
      intro p1 _ p2 _ hne
      rw [Finset.disjoint_left]
      intro a h1 h2
      simp only [Ap, Finset.mem_filter] at h1 h2
      rw [h1.2] at h2
      exact hne (Sum.inl.inj h2.2)
    have hdisj_ww : ∀ w1 ∈ (Finset.univ : Finset (Fin 13)), ∀ w2 ∈ (Finset.univ : Finset (Fin 13)),
        w1 ≠ w2 → Disjoint (Aw w1) (Aw w2) := by
      intro w1 _ w2 _ hne
      rw [Finset.disjoint_left]
      intro a h1 h2
      simp only [Aw, Finset.mem_filter] at h1 h2
      rw [h1.2] at h2
      exact hne (Sum.inr.inj h2.2)
    have hdisj_pw : Disjoint (Finset.univ.biUnion Ap) (Finset.univ.biUnion Aw) := by
      rw [Finset.disjoint_left]
      intro a h1 h2
      obtain ⟨p, _, hap⟩ := Finset.mem_biUnion.mp h1
      obtain ⟨w, _, haw⟩ := Finset.mem_biUnion.mp h2
      simp only [Ap, Finset.mem_filter] at hap
      simp only [Aw, Finset.mem_filter] at haw
      rw [hap.2] at haw
      cases haw.2
    have heq_A : (Finset.univ.biUnion Ap) ∪ (Finset.univ.biUnion Aw) = A := by
      ext a
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Ap, Aw,
        Finset.mem_filter]
      constructor
      · rintro (⟨p, ha, _⟩ | ⟨w, ha, _⟩) <;> exact ha
      · intro ha
        cases hc : centerOfAnd a with
        | inl p => exact Or.inl ⟨p, ha, rfl⟩
        | inr w => exact Or.inr ⟨w, ha, rfl⟩
    rw [← Finset.card_biUnion hdisj_pp, ← Finset.card_biUnion hdisj_ww,
      ← Finset.card_union_of_disjoint hdisj_pw, heq_A]
  have hEdge_sum : 52 ≤ (∑ p : Fin 13, ((Ap p).biUnion (actLines C)).card) +
      (∑ w : Fin 13, ((Aw w).biUnion (actPts C)).card) := by
    let incPairs := Finset.univ.filter fun pw : Fin 13 × Fin 13 => pw.1 - pw.2 ∈ x1Set
    let E_pts : Finset (Fin 13 × Fin 13) :=
      Finset.univ.biUnion fun p : Fin 13 => ({p} ×ˢ ((Ap p).biUnion (actLines C)))
    let E_lns : Finset (Fin 13 × Fin 13) :=
      Finset.univ.biUnion fun w : Fin 13 => (((Aw w).biUnion (actPts C)) ×ˢ {w})
    have hsub : incPairs ⊆ E_pts ∪ E_lns := by
      intro pw hpw
      simp only [incPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hpw
      obtain ⟨a, haA, hp, hw⟩ := hCov pw.1 pw.2 hpw
      cases hc : centerOfAnd a with
      | inl p =>
        have haAp : a ∈ Ap p := Finset.mem_filter.mpr ⟨haA, hc⟩
        have hpeq := (hAp_props p a haAp).2.1
        rw [hpeq, Finset.mem_singleton] at hp
        refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, ?_⟩)
        exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hp, Finset.mem_biUnion.mpr ⟨a, haAp, hw⟩⟩
      | inr w =>
        have haAw : a ∈ Aw w := Finset.mem_filter.mpr ⟨haA, hc⟩
        have hweq := (hAw_props w a haAw).2.1
        rw [hweq, Finset.mem_singleton] at hw
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, ?_⟩)
        exact Finset.mem_product.mpr ⟨Finset.mem_biUnion.mpr ⟨a, haAw, hp⟩, Finset.mem_singleton.mpr hw⟩
    have h52 := incPairs_card
    change incPairs.card = 52 at h52
    have hE1 : E_pts.card ≤ ∑ p : Fin 13, ((Ap p).biUnion (actLines C)).card := by
      refine (Finset.card_biUnion_le).trans ?_
      refine Finset.sum_le_sum fun p _ => ?_
      rw [Finset.card_product, Finset.card_singleton, one_mul]
    have hE2 : E_lns.card ≤ ∑ w : Fin 13, ((Aw w).biUnion (actPts C)).card := by
      refine (Finset.card_biUnion_le).trans ?_
      refine Finset.sum_le_sum fun w _ => ?_
      rw [Finset.card_product, Finset.card_singleton, mul_one]
    have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le E_pts E_lns)
    omega
  have hSum_pt : ∑ p : Fin 13, ((Ap p).biUnion (actLines C)).card ≤
      (∑ p : Fin 13, (Ap p).card) + (∑ p : Fin 13, (Bp p).card) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _ => hPtStar p
  have hSum_ln : ∑ w : Fin 13, ((Aw w).biUnion (actPts C)).card ≤
      (∑ w : Fin 13, (Aw w).card) + (∑ w : Fin 13, (Bw w).card) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun w _ => hLnStar w
  omega

end PEqualNP.Outside.L_meta_1751

theorem PEqualNP.Outside.L_meta_1751 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → ¬x3 x4 → (64 : ℕ) ≤ x4.size := by
  intro _ _ _ C hM hR hV hN
  exact PEqualNP.Outside.L_meta_1751.main_proof C hM hR hV hN
