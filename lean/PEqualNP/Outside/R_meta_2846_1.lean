import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_2846_1_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def buildStep (C : Circuit) (n : ℕ) (acc : Finset ℕ) (i : ℕ) : Finset ℕ :=
  match (gateAt C i).op with
  | GateOp.or =>
    if ∀ u ∈ (gateAt C i).inputs, u ∈ acc then insert (n + i) acc else acc
  | _ => acc

def buildP (Np Nl : ℕ) (C : Circuit) : Finset ℕ :=
  (List.range C.gates.length).foldl (buildStep C (Np + Nl)) (Finset.range Np)

def buildL (Np Nl : ℕ) (C : Circuit) : Finset ℕ :=
  (List.range C.gates.length).foldl (buildStep C (Np + Nl)) (Finset.Ico Np (Np + Nl))

lemma foldl_mono_step (C : Circuit) (n : ℕ) (l : List ℕ) (S : Finset ℕ) :
    S ⊆ l.foldl (buildStep C n) S := by
  induction l generalizing S with
  | nil => exact Finset.Subset.refl S
  | cons i l ih =>
    simp only [List.foldl_cons]
    unfold buildStep
    cases (gateAt C i).op with
    | or =>
      split_ifs
      · exact (Finset.subset_insert _ _).trans (ih _)
      · exact ih _
    | _ => exact ih _

lemma mem_build_of_step (C : Circuit) (n : ℕ) (l₁ l₂ : List ℕ) (i : ℕ) (S : Finset ℕ)
    (hop : (gateAt C i).op = GateOp.or)
    (hin : ∀ u ∈ (gateAt C i).inputs, u ∈ l₁.foldl (buildStep C n) S) :
    n + i ∈ (l₁ ++ i :: l₂).foldl (buildStep C n) S := by
  rw [List.foldl_append, List.foldl_cons]
  have hstep : buildStep C n (l₁.foldl (buildStep C n) S) i =
      insert (n + i) (l₁.foldl (buildStep C n) S) := by
    unfold buildStep
    rw [hop]
    split_ifs
    · rfl
    · contradiction
  rw [hstep]
  exact foldl_mono_step C n l₂ _ (Finset.mem_insert_self _ _)

lemma mem_build_inv (C : Circuit) (n : ℕ) (l : List ℕ) (S : Finset ℕ)
    (hl : ∀ i ∈ l, i < C.gates.length)
    (w : ℕ) (hw : w ∈ l.foldl (buildStep C n) S) :
    w ∈ S ∨ ∃ i ∈ l, w = n + i ∧ (gateAt C i).op = GateOp.or ∧
      ∀ u ∈ (gateAt C i).inputs, u ∈ l.foldl (buildStep C n) S := by
  induction l generalizing S with
  | nil => exact Or.inl hw
  | cons i l ih =>
    simp only [List.foldl_cons] at hw ⊢
    have hl' : ∀ j ∈ l, j < C.gates.length := fun j hj => hl j (List.mem_cons_of_mem i hj)
    cases h_op : (gateAt C i).op
    case or =>
      have hstep : buildStep C n S i =
          if ∀ u ∈ (gateAt C i).inputs, u ∈ S then insert (n + i) S else S := by
        unfold buildStep; rw [h_op]
      rw [hstep] at hw ⊢
      split_ifs at hw with hcond
      · rcases ih (insert (n + i) S) hl' hw with hmem | ⟨j, hj, rfl, hop, hin⟩
        · rcases Finset.mem_insert.mp hmem with rfl | hS
          · refine Or.inr ⟨i, List.mem_cons_self, rfl, h_op, fun u hu => ?_⟩
            split_ifs
            exact foldl_mono_step C n l (insert (n + i) S) (Finset.mem_insert_of_mem (hcond u hu))
          · exact Or.inl hS
        · refine Or.inr ⟨j, List.mem_cons_of_mem i hj, rfl, hop, fun u hu => ?_⟩
          split_ifs
          exact hin u hu
      · rcases ih S hl' hw with hS | ⟨j, hj, rfl, hop, hin⟩
        · exact Or.inl hS
        · refine Or.inr ⟨j, List.mem_cons_of_mem i hj, rfl, hop, fun u hu => ?_⟩
          simp only [hcond, ↓reduceIte]
          exact hin u hu
    all_goals
      have hstep : buildStep C n S i = S := by unfold buildStep; rw [h_op]
      rw [hstep] at hw ⊢
      rcases ih S hl' hw with hS | ⟨j, hj, rfl, hop, hin⟩
      · exact Or.inl hS
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, rfl, hop, hin⟩

lemma buildP_spec (Np Nl : ℕ) (C : Circuit) (w : ℕ) (hw : w ∈ buildP Np Nl C) :
    w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (gateAt C i).op = GateOp.or ∧
      ∀ u ∈ (gateAt C i).inputs, u ∈ buildP Np Nl C := by
  rcases mem_build_inv C (Np + Nl) (List.range C.gates.length) (Finset.range Np)
      (fun i hi => List.mem_range.mp hi) w hw with h | ⟨i, hi, rfl, hop, hin⟩
  · exact Or.inl (Finset.mem_range.mp h)
  · exact Or.inr ⟨i, List.mem_range.mp hi, rfl, hop, hin⟩

lemma buildL_spec (Np Nl : ℕ) (C : Circuit) (w : ℕ) (hw : w ∈ buildL Np Nl C) :
    (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (gateAt C i).op = GateOp.or ∧
      ∀ u ∈ (gateAt C i).inputs, u ∈ buildL Np Nl C := by
  rcases mem_build_inv C (Np + Nl) (List.range C.gates.length) (Finset.Ico Np (Np + Nl))
      (fun i hi => List.mem_range.mp hi) w hw with h | ⟨i, hi, rfl, hop, hin⟩
  · exact Or.inl (Finset.mem_Ico.mp h)
  · exact Or.inr ⟨i, List.mem_range.mp hi, rfl, hop, hin⟩

lemma mem_build_of_inputs (C : Circuit) (n : ℕ) (S : Finset ℕ) (hRB : ReadsBack n C)
    (i : ℕ) (hi : i < C.gates.length) (hop : (gateAt C i).op = GateOp.or)
    (hin : ∀ u ∈ (gateAt C i).inputs, u ∈ (List.range C.gates.length).foldl (buildStep C n) S) :
    n + i ∈ (List.range C.gates.length).foldl (buildStep C n) S := by
  have hi_len : i < (List.range C.gates.length).length := by simp [hi]
  have hsplit : List.range C.gates.length =
      (List.range C.gates.length).take i ++ i :: (List.range C.gates.length).drop (i + 1) := by
    have h1 := List.take_append_drop i (List.range C.gates.length)
    rw [List.drop_eq_getElem_cons hi_len, List.getElem_range] at h1
    exact h1.symm
  rw [hsplit]
  apply mem_build_of_step C n _ _ i S hop
  intro u hu
  have hu_lt : u < n + i := hRB i hi u hu
  have hu_all := hin u hu
  rw [hsplit] at hu_all
  have hdrop : ∀ j ∈ i :: (List.range C.gates.length).drop (i + 1),
      i ≤ j ∧ j < C.gates.length := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hmem
    · exact ⟨le_refl _, hi⟩
    · obtain ⟨k, hk, hkj⟩ := List.mem_iff_getElem.mp hmem
      simp only [List.getElem_drop, List.getElem_range] at hkj
      have hk_lt : i + 1 + k < C.gates.length := by
        simp only [List.length_drop, List.length_range] at hk
        omega
      omega
  rw [List.foldl_append] at hu_all
  have htail := mem_build_inv C n (i :: (List.range C.gates.length).drop (i + 1)) _
    (fun j hj => (hdrop j hj).2) u hu_all
  rcases htail with hpre | ⟨j, hj, rfl, _, _⟩
  · exact hpre
  · exfalso
    have := (hdrop j hj).1
    omega

lemma wire_preserved (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD k false =
      w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp; omega
    rw [ih _ hk', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma foldl_wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wire_gate_eval (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hRB : ∀ i ∈ (gateAt C j).inputs, i < x.length + j) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have := List.take_append_drop j C.gates
    rw [List.drop_eq_getElem_cons hj] at this
    exact this.symm
  unfold Circuit.wires
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set w0 := (C.gates.take j).foldl
    (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have hw0_len : w0.length = x.length + j := by
    rw [foldl_wires_length, List.length_take, min_eq_left (le_of_lt hj)]
  set v := C.gates[j].op.eval (C.gates[j].inputs.map fun i => w0.getD i false)
  have hpres := wire_preserved (C.gates.drop (j + 1)) (w0 ++ [v]) (x.length + j) (by simp [hw0_len])
  rw [hpres]
  have hlast : (w0 ++ [v]).getD (x.length + j) false = v := by
    rw [← hw0_len]
    simp [List.getD_eq_getElem?_getD]
  rw [hlast]
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hgate]
  dsimp only [v]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < w0.length := by
    rw [hw0_len]
    exact hRB i (by rw [hgate]; exact hi)
  have h1 : (C.wires x).getD i false = w0.getD i false := by
    unfold Circuit.wires
    rw [hsplit, List.foldl_append, List.foldl_cons]
    have hilt' : i < (w0 ++ [v]).length := by simp; omega
    rw [wire_preserved _ _ i hilt', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hilt]
  exact h1.symm

lemma coneStep_length (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).length = cs.length + 1 := by
  simp [coneStep]

lemma cones_take (n : ℕ) (C : Circuit) (k : ℕ) (hk : k ≤ C.gates.length) :
    ((C.gates.take k).foldl (coneStep n) []).length = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < C.gates.length := hk
    rw [List.take_succ_eq_append_getElem hk', List.foldl_append, List.foldl_cons, List.foldl_nil,
      coneStep_length, ih (le_of_lt hk')]

lemma cones_getD (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have := List.take_append_drop j C.gates
    rw [List.drop_eq_getElem_cons hj] at this
    exact this.symm
  have hpres : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ), k < cs.length →
      (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
    intro gs
    induction gs with
    | nil => intro cs k _; rfl
    | cons g gs ih =>
      intro cs k hk
      rw [List.foldl_cons, ih _ k (by rw [coneStep_length]; omega)]
      simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  unfold cones
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set cs0 := (C.gates.take j).foldl (coneStep n) []
  have hcs0_len : cs0.length = j := cones_take n C j (le_of_lt hj)
  rw [hpres _ _ j (by rw [coneStep_length, hcs0_len]; omega)]
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hgate]
  have hget : (coneStep n cs0 C.gates[j]).getD j [] =
      (C.gates[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: cs0.getD (w - n) []) := by
    unfold coneStep
    simp only [hcs0_len, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by rw [hcs0_len])]
    simp [hcs0_len]
  rw [hget]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  congr 1
  have hw_lt : w - n < cs0.length := by rw [hcs0_len]; omega
  have h1 : (cones n C).getD (w - n) [] = cs0.getD (w - n) [] := by
    unfold cones
    rw [hsplit, List.foldl_append, List.foldl_cons]
    have hlen1 : (coneStep n cs0 C.gates[j]).length = cs0.length + 1 :=
      coneStep_length n cs0 C.gates[j]
    rw [hpres (C.gates.drop (j + 1)) (coneStep n cs0 C.gates[j]) (w - n) (by omega)]
    unfold coneStep
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw_lt]
  exact h1.symm

lemma inCone_of_mem_inputs (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (j k : ℕ) (hj : j < C.gates.length) (hk : n + k ∈ (gateAt C j).inputs) :
    InCone n C k j := by
  unfold InCone
  rw [cones_getD n C j hj, List.mem_flatMap]
  have hlt : n + k < n + j := hRB j hj (n + k) hk
  refine ⟨n + k, ?_, ?_⟩
  · simp [List.mem_filter, hk, show n ≤ n + k by omega, hlt]
  · simp

lemma inCone_trans (n : ℕ) (C : Circuit) (m k j : ℕ) (hj : j < C.gates.length)
    (hmk : InCone n C m k) (hkj : InCone n C k j) :
    InCone n C m j := by
  unfold InCone at hkj ⊢
  rw [cones_getD n C j hj, List.mem_flatMap] at hkj ⊢
  rcases hkj with ⟨w, hw, hkw⟩
  refine ⟨w, hw, ?_⟩
  simp only [List.mem_cons] at hkw ⊢
  rcases hkw with rfl | hmem
  · exact Or.inr hmk
  · have hlt : w - n < j := by
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      omega
    exact Or.inr (inCone_trans n C m k (w - n) (lt_trans hlt hj) hmk hmem)

lemma wire_input_eval (C : Circuit) (n : ℕ) (z : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn z)).getD w false = z ⟨w, hw⟩ := by
  unfold Circuit.wires
  rw [wire_preserved C.gates (List.ofFn z) w (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

lemma pureOr_nonempty (Np Nl : ℕ) (C : Circuit) (hAO : IsAO2 (Np + Nl) C)
    (w : ℕ) (hw : w < Np + Nl + C.gates.length)
    (hOr : ∀ j < C.gates.length, w = Np + Nl + j → (gateAt C j).op = GateOp.or)
    (hCone : ∀ j < C.gates.length, w = Np + Nl + j → ∀ k < C.gates.length,
      InCone (Np + Nl) C k j → (gateAt C k).op = GateOp.or) :
    (C.wires (List.ofFn (fun k : Fin (Np + Nl) => decide (k.val < Np)))).getD w false = true ∨
      (C.wires (List.ofFn (fun k : Fin (Np + Nl) => decide (Np ≤ k.val)))).getD w false = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    set zP : Fin (Np + Nl) → Bool := fun k => decide (k.val < Np)
    set zL : Fin (Np + Nl) → Bool := fun k => decide (Np ≤ k.val)
    by_cases hlt : w < Np + Nl
    · rw [wire_input_eval C (Np + Nl) zP w hlt, wire_input_eval C (Np + Nl) zL w hlt]
      by_cases hp : w < Np
      · exact Or.inl (by simp [zP, hp])
      · exact Or.inr (by simp [zL]; omega)
    · have hj_lt : w - (Np + Nl) < C.gates.length := by omega
      set j := w - (Np + Nl)
      have hw_eq : w = Np + Nl + j := by omega
      have hj_op : (gateAt C j).op = GateOp.or := hOr j hj_lt hw_eq
      have hj_len : (gateAt C j).inputs.length = 2 := by
        apply hAO.2.2
        simp [gateAt, List.getD_eq_getElem?_getD, hj_lt, List.getElem_mem]
      obtain ⟨u, v, huv⟩ : ∃ u v, (gateAt C j).inputs = [u, v] := by
        cases h : (gateAt C j).inputs with
        | nil => simp [h] at hj_len
        | cons u rest =>
          cases rest with
          | nil => simp [h] at hj_len
          | cons v rest2 =>
            cases rest2 with
            | nil => exact ⟨u, v, rfl⟩
            | cons _ _ => simp [h] at hj_len
      have hu_lt : u < Np + Nl + j := hAO.2.1 j hj_lt u (by rw [huv]; simp)
      have hu_w : u < w := by omega
      have hu_or : ∀ m < C.gates.length, u = Np + Nl + m → (gateAt C m).op = GateOp.or := by
        intro m hm hum
        apply hCone j hj_lt hw_eq m hm
        apply inCone_of_mem_inputs (Np + Nl) C hAO.2.1 j m hj_lt
        rw [← hum, huv]; simp
      have hu_cone : ∀ m < C.gates.length, u = Np + Nl + m → ∀ k < C.gates.length,
          InCone (Np + Nl) C k m → (gateAt C k).op = GateOp.or := by
        intro m hm hum k hk hkm
        apply hCone j hj_lt hw_eq k hk
        apply inCone_trans (Np + Nl) C k m j hj_lt hkm
        apply inCone_of_mem_inputs (Np + Nl) C hAO.2.1 j m hj_lt
        rw [← hum, huv]; simp
      have hrec := ih u hu_w (by omega) hu_or hu_cone
      have hevalP := wire_gate_eval C (List.ofFn zP) j hj_lt (fun i hi => by
        simpa using hAO.2.1 j hj_lt i hi)
      have hevalL := wire_gate_eval C (List.ofFn zL) j hj_lt (fun i hi => by
        simpa using hAO.2.1 j hj_lt i hi)
      simp only [List.length_ofFn] at hevalP hevalL
      rw [← hw_eq] at hevalP hevalL
      rw [hevalP, hevalL, hj_op, huv]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      rcases hrec with h | h
      · exact Or.inl (by rw [h]; simp)
      · exact Or.inr (by rw [h]; simp)

lemma pureOr_false_zL_mem_buildP (Np Nl : ℕ) (C : Circuit) (hAO : IsAO2 (Np + Nl) C)
    (w : ℕ) (hw : w < Np + Nl + C.gates.length)
    (hOr : ∀ j < C.gates.length, w = Np + Nl + j → (gateAt C j).op = GateOp.or)
    (hCone : ∀ j < C.gates.length, w = Np + Nl + j → ∀ k < C.gates.length,
      InCone (Np + Nl) C k j → (gateAt C k).op = GateOp.or)
    (hfalse : (C.wires (List.ofFn (fun k : Fin (Np + Nl) => decide (Np ≤ k.val)))).getD w false = false) :
    w ∈ buildP Np Nl C := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    set zL : Fin (Np + Nl) → Bool := fun k => decide (Np ≤ k.val)
    by_cases hlt : w < Np + Nl
    · rw [wire_input_eval C (Np + Nl) zL w hlt] at hfalse
      have hwp : w < Np := by
        simp only [zL, decide_eq_false_iff_not, not_le] at hfalse
        exact hfalse
      exact foldl_mono_step C (Np + Nl) (List.range C.gates.length) (Finset.range Np)
        (Finset.mem_range.mpr hwp)
    · have hj_lt : w - (Np + Nl) < C.gates.length := by omega
      set j := w - (Np + Nl)
      have hw_eq : w = Np + Nl + j := by omega
      have hj_op : (gateAt C j).op = GateOp.or := hOr j hj_lt hw_eq
      rw [hw_eq]
      apply mem_build_of_inputs C (Np + Nl) (Finset.range Np) hAO.2.1 j hj_lt hj_op
      intro u hu
      have hu_lt : u < Np + Nl + j := hAO.2.1 j hj_lt u hu
      have hu_w : u < w := by omega
      have hu_or : ∀ m < C.gates.length, u = Np + Nl + m → (gateAt C m).op = GateOp.or := by
        intro m hm hum
        apply hCone j hj_lt hw_eq m hm
        apply inCone_of_mem_inputs (Np + Nl) C hAO.2.1 j m hj_lt
        rwa [← hum]
      have hu_cone : ∀ m < C.gates.length, u = Np + Nl + m → ∀ k < C.gates.length,
          InCone (Np + Nl) C k m → (gateAt C k).op = GateOp.or := by
        intro m hm hum k hk hkm
        apply hCone j hj_lt hw_eq k hk
        apply inCone_trans (Np + Nl) C k m j hj_lt hkm
        apply inCone_of_mem_inputs (Np + Nl) C hAO.2.1 j m hj_lt
        rwa [← hum]
      have hu_false : (C.wires (List.ofFn zL)).getD u false = false := by
        have hevalL := wire_gate_eval C (List.ofFn zL) j hj_lt (fun i hi => by
          simpa using hAO.2.1 j hj_lt i hi)
        simp only [List.length_ofFn] at hevalL
        rw [← hw_eq, hfalse, hj_op] at hevalL
        have hany : (List.map (fun i => (C.wires (List.ofFn zL)).getD i false)
            (gateAt C j).inputs).any id = false := by
          simpa [GateOp.eval] using hevalL.symm
        rw [List.any_eq_false] at hany
        have hmem := hany ((C.wires (List.ofFn zL)).getD u false) (List.mem_map_of_mem hu)
        cases hc : (C.wires (List.ofFn zL)).getD u false
        · rfl
        · exfalso; exact hmem (by simpa using hc)
      exact ih u hu_w (by omega) hu_or hu_cone hu_false

lemma pureOr_false_zP_mem_buildL (Np Nl : ℕ) (C : Circuit) (hAO : IsAO2 (Np + Nl) C)
    (w : ℕ) (hw : w < Np + Nl + C.gates.length)
    (hOr : ∀ j < C.gates.length, w = Np + Nl + j → (gateAt C j).op = GateOp.or)
    (hCone : ∀ j < C.gates.length, w = Np + Nl + j → ∀ k < C.gates.length,
      InCone (Np + Nl) C k j → (gateAt C k).op = GateOp.or)
    (hfalse : (C.wires (List.ofFn (fun k : Fin (Np + Nl) => decide (k.val < Np)))).getD w false = false) :
    w ∈ buildL Np Nl C := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    set zP : Fin (Np + Nl) → Bool := fun k => decide (k.val < Np)
    by_cases hlt : w < Np + Nl
    · rw [wire_input_eval C (Np + Nl) zP w hlt] at hfalse
      have hwl : Np ≤ w := by
        simp only [zP, decide_eq_false_iff_not, not_lt] at hfalse
        exact hfalse
      exact foldl_mono_step C (Np + Nl) (List.range C.gates.length) (Finset.Ico Np (Np + Nl))
        (Finset.mem_Ico.mpr ⟨hwl, hlt⟩)
    · have hj_lt : w - (Np + Nl) < C.gates.length := by omega
      set j := w - (Np + Nl)
      have hw_eq : w = Np + Nl + j := by omega
      have hj_op : (gateAt C j).op = GateOp.or := hOr j hj_lt hw_eq
      rw [hw_eq]
      apply mem_build_of_inputs C (Np + Nl) (Finset.Ico Np (Np + Nl)) hAO.2.1 j hj_lt hj_op
      intro u hu
      have hu_lt : u < Np + Nl + j := hAO.2.1 j hj_lt u hu
      have hu_w : u < w := by omega
      have hu_or : ∀ m < C.gates.length, u = Np + Nl + m → (gateAt C m).op = GateOp.or := by
        intro m hm hum
        apply hCone j hj_lt hw_eq m hm
        apply inCone_of_mem_inputs (Np + Nl) C hAO.2.1 j m hj_lt
        rwa [← hum]
      have hu_cone : ∀ m < C.gates.length, u = Np + Nl + m → ∀ k < C.gates.length,
          InCone (Np + Nl) C k m → (gateAt C k).op = GateOp.or := by
        intro m hm hum k hk hkm
        apply hCone j hj_lt hw_eq k hk
        apply inCone_trans (Np + Nl) C k m j hj_lt hkm
        apply inCone_of_mem_inputs (Np + Nl) C hAO.2.1 j m hj_lt
        rwa [← hum]
      have hu_false : (C.wires (List.ofFn zP)).getD u false = false := by
        have hevalP := wire_gate_eval C (List.ofFn zP) j hj_lt (fun i hi => by
          simpa using hAO.2.1 j hj_lt i hi)
        simp only [List.length_ofFn] at hevalP
        rw [← hw_eq, hfalse, hj_op] at hevalP
        have hany : (List.map (fun i => (C.wires (List.ofFn zP)).getD i false)
            (gateAt C j).inputs).any id = false := by
          simpa [GateOp.eval] using hevalP.symm
        rw [List.any_eq_false] at hany
        have hmem := hany ((C.wires (List.ofFn zP)).getD u false) (List.mem_map_of_mem hu)
        cases hc : (C.wires (List.ofFn zP)).getD u false
        · rfl
        · exfalso; exact hmem (by simpa using hc)
      exact ih u hu_w (by omega) hu_or hu_cone hu_false

end PEqualNP.Outside.R_meta_2846_1_aux

theorem PEqualNP.Outside.R_meta_2846_1
    (h1 : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (Np + Nl) C →
      (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) →
      (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) →
      ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD (Np + Nl + i) false = true →
      ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)
    (h2 : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (Np + Nl) C →
      (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) →
      (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) →
      ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ j < C.gates.length, PEqualNP.EdgeOwnership.InCone (Np + Nl) C j i →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) ∧ ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  intro Np Nl I _ C hC4 hAO hfun hmin hTop
  have hbelow := h1 Np Nl I C hC4 hAO hfun hmin hTop
  have hcone := h2 Np Nl I C hC4 hAO hfun hmin hTop
  refine ⟨PEqualNP.Outside.R_meta_2846_1_aux.buildP Np Nl C,
    PEqualNP.Outside.R_meta_2846_1_aux.buildL Np Nl C, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.R_meta_2846_1_aux.buildP_spec Np Nl C
  · exact PEqualNP.Outside.R_meta_2846_1_aux.buildL_spec Np Nl C
  · intro i hi hop
    have hlen : (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs.length = 2 := by
      apply hAO.2.2
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hi,
        List.getElem_mem]
    obtain ⟨a, b, hab⟩ : ∃ a b, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] := by
      cases h : (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs with
      | nil => simp [h] at hlen
      | cons a rest =>
        cases rest with
        | nil => simp [h] at hlen
        | cons b rest2 =>
          cases rest2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons _ _ => simp [h] at hlen
    refine ⟨a, b, hab, ?_⟩
    have ha_lt : a < Np + Nl + i := hAO.2.1 i hi a (by rw [hab]; simp)
    have hb_lt : b < Np + Nl + i := hAO.2.1 i hi b (by rw [hab]; simp)
    have ha_or : ∀ j < C.gates.length, a = Np + Nl + j →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro j hj haj
      apply hcone i hi hop j hj
      apply PEqualNP.Outside.R_meta_2846_1_aux.inCone_of_mem_inputs (Np + Nl) C hAO.2.1 i j hi
      rw [← haj, hab]; simp
    have ha_cone : ∀ j < C.gates.length, a = Np + Nl + j → ∀ k < C.gates.length,
        PEqualNP.EdgeOwnership.InCone (Np + Nl) C k j →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro j hj haj k hk hkj
      apply hcone i hi hop k hk
      apply PEqualNP.Outside.R_meta_2846_1_aux.inCone_trans (Np + Nl) C k j i hi hkj
      apply PEqualNP.Outside.R_meta_2846_1_aux.inCone_of_mem_inputs (Np + Nl) C hAO.2.1 i j hi
      rw [← haj, hab]; simp
    have hb_or : ∀ j < C.gates.length, b = Np + Nl + j →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro j hj hbj
      apply hcone i hi hop j hj
      apply PEqualNP.Outside.R_meta_2846_1_aux.inCone_of_mem_inputs (Np + Nl) C hAO.2.1 i j hi
      rw [← hbj, hab]; simp
    have hb_cone : ∀ j < C.gates.length, b = Np + Nl + j → ∀ k < C.gates.length,
        PEqualNP.EdgeOwnership.InCone (Np + Nl) C k j →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro j hj hbj k hk hkj
      apply hcone i hi hop k hk
      apply PEqualNP.Outside.R_meta_2846_1_aux.inCone_trans (Np + Nl) C k j i hi hkj
      apply PEqualNP.Outside.R_meta_2846_1_aux.inCone_of_mem_inputs (Np + Nl) C hAO.2.1 i j hi
      rw [← hbj, hab]; simp
    set zP : Fin (Np + Nl) → Bool := fun k => decide (k.val < Np)
    set zL : Fin (Np + Nl) → Bool := fun k => decide (Np ≤ k.val)
    have hnotP : ¬ ((C.wires (List.ofFn zP)).getD a false = true ∧
        (C.wires (List.ofFn zP)).getD b false = true) := by
      rintro ⟨haP, hbP⟩
      have heval := PEqualNP.Outside.R_meta_2846_1_aux.wire_gate_eval C (List.ofFn zP) i hi
        (fun u hu => by simpa using hAO.2.1 i hi u hu)
      simp only [List.length_ofFn] at heval
      have hiP : (C.wires (List.ofFn zP)).getD (Np + Nl + i) false = true := by
        rw [heval, hop, hab]
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true, haP, hbP]
      obtain ⟨p, l, _, _, hl⟩ := hbelow i hi hop zP hiP
      simp only [zP, decide_eq_true_eq, Fin.val_natAdd] at hl
      omega
    have hnotL : ¬ ((C.wires (List.ofFn zL)).getD a false = true ∧
        (C.wires (List.ofFn zL)).getD b false = true) := by
      rintro ⟨haL, hbL⟩
      have heval := PEqualNP.Outside.R_meta_2846_1_aux.wire_gate_eval C (List.ofFn zL) i hi
        (fun u hu => by simpa using hAO.2.1 i hi u hu)
      simp only [List.length_ofFn] at heval
      have hiL : (C.wires (List.ofFn zL)).getD (Np + Nl + i) false = true := by
        rw [heval, hop, hab]
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true, haL, hbL]
      obtain ⟨p, l, _, hp, _⟩ := hbelow i hi hop zL hiL
      simp only [zL, decide_eq_true_eq, Fin.val_castAdd] at hp
      omega
    have ha_ne := PEqualNP.Outside.R_meta_2846_1_aux.pureOr_nonempty Np Nl C hAO a
      (by omega) ha_or ha_cone
    have hb_ne := PEqualNP.Outside.R_meta_2846_1_aux.pureOr_nonempty Np Nl C hAO b
      (by omega) hb_or hb_cone
    rcases ha_ne with haP | haL <;> rcases hb_ne with hbP | hbL
    · exact absurd ⟨haP, hbP⟩ hnotP
    · refine Or.inl ⟨?_, ?_⟩
      · have haLf : (C.wires (List.ofFn zL)).getD a false = false := by
          cases h : (C.wires (List.ofFn zL)).getD a false
          · rfl
          · exact absurd ⟨h, hbL⟩ hnotL
        exact PEqualNP.Outside.R_meta_2846_1_aux.pureOr_false_zL_mem_buildP Np Nl C hAO a
          (by omega) ha_or ha_cone haLf
      · have hbPf : (C.wires (List.ofFn zP)).getD b false = false := by
          cases h : (C.wires (List.ofFn zP)).getD b false
          · rfl
          · exact absurd ⟨haP, h⟩ hnotP
        exact PEqualNP.Outside.R_meta_2846_1_aux.pureOr_false_zP_mem_buildL Np Nl C hAO b
          (by omega) hb_or hb_cone hbPf
    · refine Or.inr ⟨?_, ?_⟩
      · have haPf : (C.wires (List.ofFn zP)).getD a false = false := by
          cases h : (C.wires (List.ofFn zP)).getD a false
          · rfl
          · exact absurd ⟨h, hbP⟩ hnotP
        exact PEqualNP.Outside.R_meta_2846_1_aux.pureOr_false_zP_mem_buildL Np Nl C hAO a
          (by omega) ha_or ha_cone haPf
      · have hbLf : (C.wires (List.ofFn zL)).getD b false = false := by
          cases h : (C.wires (List.ofFn zL)).getD b false
          · rfl
          · exact absurd ⟨haL, h⟩ hnotL
        exact PEqualNP.Outside.R_meta_2846_1_aux.pureOr_false_zL_mem_buildP Np Nl C hAO b
          (by omega) hb_or hb_cone hbLf
    · exact absurd ⟨haL, hbL⟩ hnotL
