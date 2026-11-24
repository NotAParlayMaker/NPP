import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3706_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core

lemma foldl_append_len {α : Type} (f : List α → Gate → α) :
    ∀ (gs : List Gate) (init : List α),
      (gs.foldl (fun a g => a ++ [f a g]) init).length = init.length + gs.length
  | [], init => by simp
  | g :: gs, init => by
      simp only [List.foldl_cons, foldl_append_len, List.length_append, List.length_cons,
        List.length_nil]
      omega

lemma foldl_append_prefix {α : Type} (f : List α → Gate → α) :
    ∀ (gs : List Gate) (init : List α) (i : ℕ), i < init.length → ∀ (d : α),
      (gs.foldl (fun a g => a ++ [f a g]) init).getD i d = init.getD i d
  | [], init, i, _, d => rfl
  | g :: gs, init, i, hi, d => by
      simp only [List.foldl_cons]
      have hlen : i < (init ++ [f init g]).length := by simp; omega
      rw [foldl_append_prefix f gs (init ++ [f init g]) i hlen d]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_append_at {α : Type} (f : List α → Gate → α) :
    ∀ (gs : List Gate) (init : List α) (j : ℕ) (hj : j < gs.length) (d : α),
      (gs.foldl (fun a g => a ++ [f a g]) init).getD (init.length + j) d =
        f ((gs.take j).foldl (fun a g => a ++ [f a g]) init) gs[j]
  | [], _, _, hj, _ => by simp at hj
  | g :: gs, init, 0, _, d => by
      simp only [List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil,
        List.getElem_cons_zero]
      have hlen : init.length < (init ++ [f init g]).length := by simp
      rw [foldl_append_prefix f gs (init ++ [f init g]) init.length hlen d]
      simp [List.getD_eq_getElem?_getD]
  | g :: gs, init, j + 1, hj, d => by
      simp only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ]
      have hj' : j < gs.length := Nat.lt_of_succ_lt_succ hj
      have heq : init.length + (j + 1) = (init ++ [f init g]).length + j := by simp; omega
      rw [heq, foldl_append_at f gs (init ++ [f init g]) j hj' d]

lemma wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_append_len (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates x

lemma wireVal_input (n : ℕ) (C : Circuit) (y : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i y = y ⟨i, hi⟩ := by
  unfold wireVal Circuit.wires
  have hlen : i < (List.ofFn y).length := by simpa using hi
  rw [foldl_append_prefix _ C.gates (List.ofFn y) i hlen false]
  simp [List.getD_eq_getElem?_getD, hi]

lemma wireVal_ge (n : ℕ) (C : Circuit) (y : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) :
    wireVal n C w y = false := by
  unfold wireVal
  have hlen : (C.wires (List.ofFn y)).length ≤ w := by
    rw [wires_len, List.length_ofFn]; exact hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
  rfl

lemma wireVal_gate (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (y : Fin n → Bool) :
    wireVal n C (n + j) y =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => if i < n + j then wireVal n C i y else false) := by
  unfold wireVal Circuit.wires
  have hn : n = (List.ofFn y).length := by simp
  have hstep := foldl_append_at (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn y) j hj false
  rw [← hn] at hstep
  rw [hstep]
  have hgj : C.gates[j] = gateAt C j := by
    unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
  rw [hgj]
  congr 1
  apply List.map_congr_left
  intro i _
  set pref := (C.gates.take j).foldl
    (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn y)
  have hplen : pref.length = n + j := by
    rw [foldl_append_len, List.length_ofFn, List.length_take]; omega
  by_cases hi : i < n + j
  · simp only [hi, ↓reduceIte]
    have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_rhs => rw [hsplit, List.foldl_append]
    exact (foldl_append_prefix _ (C.gates.drop j) pref i (by omega) false).symm
  · simp only [hi, ↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

lemma gateAt_two_inputs (n : ℕ) (C : Circuit) (hAO2 : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  have hlen := hAO2.2.2 _ hmem
  cases h : (gateAt C j).inputs with
  | nil => rw [h] at hlen; simp at hlen
  | cons a t =>
    cases t with
    | nil => rw [h] at hlen; simp at hlen
    | cons b t' =>
      cases t' with
      | nil =>
        unfold opnd
        rw [h]
        rfl
      | cons c t'' => rw [h] at hlen; simp at hlen

lemma gateAt_ao (n : ℕ) (C : Circuit) (hAO2 : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  exact hAO2.1 _ hmem

lemma orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  simpa using foldl_append_len
    (fun cs g => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) []) else [])) C.gates []

lemma orReaches_iff (n : ℕ) (C : Circuit) (j g : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) g ↔
      g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w g) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold OrReaches orSets orStep
  simp only [Nat.le_add_right, Nat.add_sub_cancel_left, true_and]
  have hstep := foldl_append_at
    (fun cs g => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) []) else [])) C.gates [] j hj []
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [hstep]
  have hgj : C.gates[j] = gateAt C j := by
    unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
  rw [hgj]
  set pref := (C.gates.take j).foldl
    (fun cs g => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) []) else [])]) []
  have hplen : pref.length = j := by
    rw [foldl_append_len, List.length_nil, Nat.zero_add, List.length_take]; omega
  rw [hplen, List.mem_cons]
  constructor
  · rintro (rfl | h)
    · left; rfl
    · right
      by_cases hop : (gateAt C j).op = GateOp.or
      · simp only [hop, ↓reduceIte, List.mem_flatMap] at h
        rcases h with ⟨w, hw, hg⟩
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        refine ⟨hop, w, hw.1, hw.2.1, hw.2.2, hw.2.1, ?_⟩
        have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
        rw [hsplit, List.foldl_append]
        rw [foldl_append_prefix _ (C.gates.drop j) pref (w - n) (by omega) []]
        exact hg
      · simp only [hop, ↓reduceIte, List.not_mem_nil] at h
  · rintro (rfl | ⟨hop, w, hw, hnw, hlt, _, hg⟩)
    · left; rfl
    · right
      simp only [hop, ↓reduceIte, List.mem_flatMap]
      refine ⟨w, ?_, ?_⟩
      · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hw, hnw, hlt⟩
      · have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
        rw [hsplit, List.foldl_append] at hg
        rw [foldl_append_prefix _ (C.gates.drop j) pref (w - n) (by omega) []] at hg
        exact hg

lemma orReaches_lt (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    w < n + C.gates.length := by
  by_contra hge
  have h1 : (orSets n C).length ≤ w - n := by rw [orSets_len]; omega
  have h2 : (orSets n C).getD (w - n) [] = [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]; rfl
  rcases h with ⟨_, hmem⟩
  rw [h2] at hmem
  simp at hmem

lemma orReaches_refl (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  rw [orReaches_iff n C j j hj]; left; rfl

lemma orReaches_step (n : ℕ) (C : Circuit) (g g' : ℕ) (hg : g < C.gates.length)
    (hop : (gateAt C g).op = GateOp.or) (hmem : n + g' ∈ (gateAt C g).inputs) (hgg' : g' < g) :
    ∀ k, k < C.gates.length → OrReaches n C (n + k) g → OrReaches n C (n + k) g' := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk hor
    rw [orReaches_iff n C k g hk] at hor
    rw [orReaches_iff n C k g' hk]
    rcases hor with rfl | ⟨hopk, w, hw, hnw, hlt, hor'⟩
    · right
      exact ⟨hop, n + g', hmem, by omega, by omega, orReaches_refl n C g' (by omega)⟩
    · right
      refine ⟨hopk, w, hw, hnw, hlt, ?_⟩
      have heq : n + (w - n) = w := by omega
      rw [← heq] at hor' ⊢
      exact ih (w - n) (by omega) (by omega) hor'

lemma orReaches_wireVal (n : ℕ) (C : Circuit) (y : Fin n → Bool) :
    ∀ j, j < C.gates.length → ∀ g, OrReaches n C (n + j) g →
      wireVal n C (n + g) y = true → wireVal n C (n + j) y = true := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj g hor hval
    rw [orReaches_iff n C j g hj] at hor
    rcases hor with rfl | ⟨hop, w, hw, hnw, hlt, hor'⟩
    · exact hval
    · have hwval : wireVal n C w y = true := by
        have heq : n + (w - n) = w := by omega
        rw [← heq] at hor' ⊢
        exact ih (w - n) (by omega) (by omega) g hor' hval
      rw [wireVal_gate n C j hj y, hop]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      exact ⟨w, hw, by simp only [hlt, ↓reduceIte]; exact hwval⟩

lemma orReaches_wireVal_any (n : ℕ) (C : Circuit) (w g : ℕ) (y : Fin n → Bool)
    (hor : OrReaches n C w g) (hval : wireVal n C (n + g) y = true) :
    wireVal n C w y = true := by
  have hlt := orReaches_lt n C w g hor
  have hnw : n ≤ w := hor.1
  have heq : n + (w - n) = w := by omega
  rw [← heq] at hor ⊢
  exact orReaches_wireVal n C y (w - n) (by omega) g hor hval

lemma orIn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  ext i
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨k, _, hor, _, _⟩)
    · exact Fin.ext h
    · exfalso; have := hor.1; omega
  · intro h; left; exact congrArg Fin.val h

lemma orIn_and (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext i
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (h | ⟨k, _, hor, hopk, _⟩)
  · have := i.isLt; omega
  · rw [orReaches_iff n C j k hj] at hor
    rcases hor with rfl | ⟨hor2, _⟩
    · rw [hop] at hopk; cases hopk
    · rw [hop] at hor2; cases hor2

lemma orIn_or (n : ℕ) (C : Circuit) (hAO2 : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  have hins := gateAt_two_inputs n C hAO2 j hj
  have h0 : opnd C j 0 < n + j := hAO2.2.1 j hj _ (by rw [hins]; simp)
  have h1 : opnd C j 1 < n + j := hAO2.2.1 j hj _ (by rw [hins]; simp)
  ext i
  simp only [orIn, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hor, hopk, hmem⟩)
    · exfalso; have := i.isLt; omega
    · rw [orReaches_iff n C j k hj] at hor
      rcases hor with rfl | ⟨_, w, hw, hnw, hwlt, hor'⟩
      · rw [hins] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with hmem | hmem
        · left; left; exact hmem
        · right; left; exact hmem
      · rw [hins] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · left; right; exact ⟨k, hk, hor', hopk, hmem⟩
        · right; right; exact ⟨k, hk, hor', hopk, hmem⟩
  · rintro ((h | ⟨k, hk, hor', hopk, hmem⟩) | (h | ⟨k, hk, hor', hopk, hmem⟩))
    · right
      refine ⟨j, hj, orReaches_refl n C j hj, hop, ?_⟩
      rw [hins, h]; simp
    · right
      refine ⟨k, hk, ?_, hopk, hmem⟩
      rw [orReaches_iff n C j k hj]
      right
      exact ⟨hop, opnd C j 0, by rw [hins]; simp, hor'.1, h0, hor'⟩
    · right
      refine ⟨j, hj, orReaches_refl n C j hj, hop, ?_⟩
      rw [hins, h]; simp
    · right
      refine ⟨k, hk, ?_, hopk, hmem⟩
      rw [orReaches_iff n C j k hj]
      right
      exact ⟨hop, opnd C j 1, by rw [hins]; simp, hor'.1, h1, hor'⟩

lemma orIn_wireVal (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) (y : Fin n → Bool)
    (hi : i ∈ orIn n C w) (hyi : y i = true) :
    wireVal n C w y = true := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with heq | ⟨k, hk, hor, hopk, hmem⟩
  · have hw : w < n := by have := i.isLt; omega
    rw [wireVal_input n C y w hw]
    have hfin : (⟨w, hw⟩ : Fin n) = i := Fin.ext heq.symm
    rwa [hfin]
  · apply orReaches_wireVal_any n C w k y hor
    rw [wireVal_gate n C k hk y, hopk]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    refine ⟨(i : ℕ), hmem, ?_⟩
    have hilt : (i : ℕ) < n + k := by have := i.isLt; omega
    simp only [hilt, ↓reduceIte]
    rw [wireVal_input n C y i.val i.isLt]
    exact hyi

lemma mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  by_cases hv : v ∈ A
  · simp only [hv, ↓reduceIte]
    exact ⟨fun h => Or.inl h, fun h => h.elim id (fun he => he ▸ hv)⟩
  · simp only [hv, ↓reduceIte, List.mem_append, List.mem_singleton]

lemma mem_foldl_insertNew : ∀ (X acc : List (List ℕ)) (x : List ℕ),
    x ∈ X.foldl insertNew acc ↔ x ∈ acc ∨ x ∈ X
  | [], acc, x => by simp
  | v :: X, acc, x => by
      simp only [List.foldl_cons, mem_foldl_insertNew, mem_insertNew, List.mem_cons]
      tauto

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) :
    v ∈ andStep k A B ↔ ∃ a ∈ A, ∃ b ∈ B, v = capAdd k a b := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

lemma readVectors_at_input (C : Circuit) (n : ℕ) (S : List ℕ) (k i : ℕ) (hi : i < n) :
    (readVectors C n S k).getD i [] = leafVectors S k i := by
  unfold readVectors
  have hlen : i < ((List.range n).map (leafVectors S k)).length := by simpa using hi
  rw [foldl_append_prefix _ C.gates _ i hlen []]
  simp [List.getD_eq_getElem?_getD, hi]

lemma readVectors_at_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k j : ℕ) (hj : j < C.gates.length)
    (hAO2 : IsAO2 n C) :
    let R := readVectors C n S k
    let a := opnd C j 0
    let b := opnd C j 1
    ((gateAt C j).op = GateOp.or →
      ∀ v, v ∈ R.getD (n + j) [] ↔ v ∈ R.getD a [] ∨ v ∈ R.getD b []) ∧
    ((gateAt C j).op = GateOp.and →
      ∀ v, v ∈ R.getD (n + j) [] ↔
        ∃ va ∈ R.getD a [], ∃ vb ∈ R.getD b [],
          v = capAdd k (capAdd k (S.map fun _ => 0) va) vb) := by
  intro R a b
  have hinit : ((List.range n).map (leafVectors S k)).length = n := by simp
  have hstep := foldl_append_at
    (fun (acc : List (List (List ℕ))) (g : Gate) =>
      let ins := g.inputs.map fun i => acc.getD i []
      match g.op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
      | _ => [])
    C.gates ((List.range n).map (leafVectors S k)) j hj []
  rw [hinit] at hstep
  have hgj : C.gates[j] = gateAt C j := by
    unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
  rw [hgj] at hstep
  set pref := (C.gates.take j).foldl
    (fun (acc : List (List (List ℕ))) (g : Gate) =>
      let ins := g.inputs.map fun i => acc.getD i []
      acc ++ [match g.op with
        | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
        | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
        | _ => []])
    ((List.range n).map (leafVectors S k))
  have hplen : pref.length = n + j := by
    rw [foldl_append_len, hinit, List.length_take]; omega
  have hpref_eq : ∀ i < n + j, pref.getD i [] = R.getD i [] := by
    intro i hi
    have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    show pref.getD i [] = (readVectors C n S k).getD i []
    unfold readVectors
    conv_rhs => rw [hsplit, List.foldl_append]
    exact (foldl_append_prefix _ (C.gates.drop j) pref i (by omega) []).symm
  have hins := gateAt_two_inputs n C hAO2 j hj
  have ha_lt : a < n + j := hAO2.2.1 j hj a (by rw [hins]; simp [a])
  have hb_lt : b < n + j := hAO2.2.1 j hj b (by rw [hins]; simp [b])
  have hpa : pref.getD (opnd C j 0) [] = R.getD a [] := hpref_eq a ha_lt
  have hpb : pref.getD (opnd C j 1) [] = R.getD b [] := hpref_eq b hb_lt
  constructor
  · intro hop v
    change v ∈ (C.gates.foldl
      (fun (acc : List (List (List ℕ))) (g : Gate) =>
        acc ++ [let ins := g.inputs.map fun i => acc.getD i []
          match g.op with
          | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
          | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
          | _ => []])
      ((List.range n).map (leafVectors S k))).getD (n + j) [] ↔ _
    rw [hstep, hop, hins]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      mem_foldl_insertNew, List.not_mem_nil, false_or, hpa, hpb]
  · intro hop v
    change v ∈ (C.gates.foldl
      (fun (acc : List (List (List ℕ))) (g : Gate) =>
        acc ++ [let ins := g.inputs.map fun i => acc.getD i []
          match g.op with
          | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
          | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
          | _ => []])
      ((List.range n).map (leafVectors S k))).getD (n + j) [] ↔ _
    rw [hstep, hop, hins]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      mem_andStep, List.mem_singleton, hpa, hpb]
    constructor
    · rintro ⟨w, ⟨z, rfl, va, hva, rfl⟩, vb, hvb, rfl⟩
      exact ⟨va, hva, vb, hvb, rfl⟩
    · rintro ⟨va, hva, vb, hvb, rfl⟩
      exact ⟨capAdd k (S.map fun _ => 0) va, ⟨S.map fun _ => 0, rfl, va, hva, rfl⟩, vb, hvb, rfl⟩

lemma capAdd_two (a1 b1 a2 b2 : ℕ) :
    capAdd 1 [a1, b1] [a2, b2] = [min (a1 + a2) 2, min (b1 + b2) 2] := rfl

lemma graphFun_single_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    graphFun G ∅ (fun i => decide (i = u)) = false := by
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_false_iff_not, not_exists, not_and]
  intro a b hadj ha hb
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hadj

lemma pair_merge_card {α : Type} [DecidableEq α] (V : Finset α) :
    ∀ E : List (α × α), ∃ col : α → α,
      V.card ≤ (V.image col).card + E.length ∧ ∀ p ∈ E, col p.1 = col p.2
  | [] => ⟨id, by simp, by simp⟩
  | (x, y) :: E' => by
      obtain ⟨col', hcard, hmem⟩ := pair_merge_card V E'
      let col : α → α := fun v => if col' v = col' x then col' y else col' v
      refine ⟨col, ?_, ?_⟩
      · have hsub : V.image col' ⊆ insert (col' x) (V.image col) := by
          intro z hz
          rw [Finset.mem_image] at hz
          rcases hz with ⟨v, hv, rfl⟩
          by_cases hvx : col' v = col' x
          · rw [hvx]; exact Finset.mem_insert_self _ _
          · apply Finset.mem_insert_of_mem
            rw [Finset.mem_image]
            exact ⟨v, hv, by simp [col, hvx]⟩
        have hc1 : (V.image col').card ≤ (insert (col' x) (V.image col)).card :=
          Finset.card_le_card hsub
        have hc2 : (insert (col' x) (V.image col)).card ≤ (V.image col).card + 1 :=
          Finset.card_insert_le _ _
        simp only [List.length_cons]
        omega
      · intro p hp
        rw [List.mem_cons] at hp
        rcases hp with rfl | hp'
        · simp [col]
        · have heq := hmem p hp'
          simp only [col, heq]

lemma exists_pair_list {α β : Type} (S : Finset β) (A B : β → Finset α) :
    ∃ E : List (α × α), E.length ≤ S.card ∧
      ∀ g ∈ S, (A g).Nonempty → (B g).Nonempty → ∃ x ∈ A g, ∃ y ∈ B g, (x, y) ∈ E := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp⟩
  | insert g S hg ih =>
    rcases ih with ⟨E, hlen, hmem⟩
    by_cases hne : (A g).Nonempty ∧ (B g).Nonempty
    · rcases hne with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      refine ⟨(x, y) :: E, ?_, ?_⟩
      · simp [Finset.card_insert_of_notMem hg]; omega
      · intro g' hg' hA hB
        rw [Finset.mem_insert] at hg'
        rcases hg' with rfl | hg'
        · exact ⟨x, hx, y, hy, List.mem_cons_self ..⟩
        · rcases hmem g' hg' hA hB with ⟨x', hx', y', hy', hxy⟩
          exact ⟨x', hx', y', hy', List.mem_cons_of_mem _ hxy⟩
    · refine ⟨E, ?_, ?_⟩
      · simp [Finset.card_insert_of_notMem hg]; omega
      · intro g' hg' hA hB
        rw [Finset.mem_insert] at hg'
        rcases hg' with rfl | hg'
        · exact False.elim (hne ⟨hA, hB⟩)
        · exact hmem g' hg' hA hB

lemma read_once_to_top_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO2 : IsAO2 n C)
    (hFun : circuitFun n C = graphFun G ∅)
    (u v : Fin n) (hAdj : G.Adj u v)
    (hOnce : ¬ ReadTwiceAt n C (C.output - n) u v) :
    n ≤ C.output ∧ C.output < n + C.gates.length ∧
      ∃ a < C.gates.length, OrReaches n C C.output a ∧ (gateAt C a).op = GateOp.and ∧
        ((u ∈ side C a 0 ∧ v ∈ side C a 1) ∨ (v ∈ side C a 0 ∧ u ∈ side C a 1)) := by
  have huv : u ≠ v := G.ne_of_adj hAdj
  have huv_val : u.val ≠ v.val := fun h => huv (Fin.ext h)
  have hPairGraph : graphFun G ∅ (pairInput u v) = true := by
    unfold graphFun
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    right
    exact ⟨u, v, hAdj, by simp [pairInput], by simp [pairInput]⟩
  have hOutVal : wireVal n C C.output (pairInput u v) = true := by
    have h := congrFun hFun (pairInput u v)
    rw [hPairGraph] at h
    exact h
  have hOutGe : n ≤ C.output := by
    by_contra hlt
    push Not at hlt
    have h1 := congrFun hFun (fun i => decide (i = ⟨C.output, hlt⟩))
    have h2 : circuitFun n C (fun i => decide (i = ⟨C.output, hlt⟩)) = true := by
      show wireVal n C C.output (fun i => decide (i = ⟨C.output, hlt⟩)) = true
      rw [wireVal_input n C _ C.output hlt]; simp
    rw [h2, graphFun_single_false G ⟨C.output, hlt⟩] at h1
    cases h1
  have hOutLt : C.output < n + C.gates.length := by
    by_contra hge
    push Not at hge
    rw [wireVal_ge n C (pairInput u v) C.output hge] at hOutVal
    cases hOutVal
  refine ⟨hOutGe, hOutLt, ?_⟩
  let S : List ℕ := [u.val, v.val]
  have hVecPos : ∀ w, w < n + C.gates.length →
      ∀ vec ∈ (readVectors C n S 1).getD w [], ∃ a b, vec = [a, b] ∧ 1 ≤ a + b := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw vec hvec
      by_cases hlt : w < n
      · rw [readVectors_at_input C n S 1 w hlt] at hvec
        unfold leafVectors at hvec
        by_cases hmem : w ∈ S
        · simp only [hmem, ↓reduceIte, List.mem_singleton] at hvec
          subst hvec
          simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · refine ⟨1, 0, ?_, by omega⟩
            simp [S, Ne.symm huv_val]
          · refine ⟨0, 1, ?_, by omega⟩
            simp [S, huv_val]
        · simp only [hmem, ↓reduceIte, List.not_mem_nil] at hvec
      · have hk : w - n < C.gates.length := by omega
        have heq : n + (w - n) = w := by omega
        rw [← heq] at hvec
        have hins := gateAt_two_inputs n C hAO2 (w - n) hk
        have ha : opnd C (w - n) 0 < n + (w - n) := hAO2.2.1 (w - n) hk _ (by rw [hins]; simp)
        have hb : opnd C (w - n) 1 < n + (w - n) := hAO2.2.1 (w - n) hk _ (by rw [hins]; simp)
        rcases gateAt_ao n C hAO2 (w - n) hk with hop | hop
        · rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).2 hop] at hvec
          rcases hvec with ⟨va, hva, vb, hvb, rfl⟩
          obtain ⟨a1, b1, rfl, hp1⟩ := ih (opnd C (w - n) 0) (by omega) (by omega) va hva
          obtain ⟨a2, b2, rfl, hp2⟩ := ih (opnd C (w - n) 1) (by omega) (by omega) vb hvb
          refine ⟨min (min (0 + a1) 2 + a2) 2, min (min (0 + b1) 2 + b2) 2, rfl, by omega⟩
        · rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).1 hop] at hvec
          rcases hvec with hva | hvb
          · exact ih (opnd C (w - n) 0) (by omega) (by omega) vec hva
          · exact ih (opnd C (w - n) 1) (by omega) (by omega) vec hvb
  have hZeroCheck : ∀ w, w < n + C.gates.length →
      (∀ a, [a, 0] ∈ (readVectors C n S 1).getD w [] → wireVal n C w (fun i => decide (i = u)) = true) ∧
      (∀ b, [0, b] ∈ (readVectors C n S 1).getD w [] → wireVal n C w (fun i => decide (i = v)) = true) := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw
      by_cases hlt : w < n
      · rw [readVectors_at_input C n S 1 w hlt]
        constructor
        · intro a hvec
          unfold leafVectors at hvec
          by_cases hmem : w ∈ S
          · simp only [hmem, ↓reduceIte, List.mem_singleton] at hvec
            have hwu : w = u.val := by
              by_contra hne
              have hwv : w = v.val := by
                simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hmem
                exact hmem.resolve_left hne
              subst hwv
              simp only [S, List.map_cons, List.map_nil, huv_val, ↓reduceIte, List.cons.injEq] at hvec
              omega
            rw [wireVal_input n C _ w hlt]
            have hfin : (⟨w, hlt⟩ : Fin n) = u := Fin.ext hwu
            simp [hfin]
          · simp only [hmem, ↓reduceIte, List.not_mem_nil] at hvec
        · intro b hvec
          unfold leafVectors at hvec
          by_cases hmem : w ∈ S
          · simp only [hmem, ↓reduceIte, List.mem_singleton] at hvec
            have hwv : w = v.val := by
              by_contra hne
              have hwu : w = u.val := by
                simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hmem
                exact hmem.resolve_right hne
              subst hwu
              simp only [S, List.map_cons, List.map_nil, Ne.symm huv_val, ↓reduceIte, List.cons.injEq] at hvec
              omega
            rw [wireVal_input n C _ w hlt]
            have hfin : (⟨w, hlt⟩ : Fin n) = v := Fin.ext hwv
            simp [hfin]
          · simp only [hmem, ↓reduceIte, List.not_mem_nil] at hvec
      · have hk : w - n < C.gates.length := by omega
        have heq : n + (w - n) = w := by omega
        rw [← heq]
        have hins := gateAt_two_inputs n C hAO2 (w - n) hk
        have ha : opnd C (w - n) 0 < n + (w - n) := hAO2.2.1 (w - n) hk _ (by rw [hins]; simp)
        have hb : opnd C (w - n) 1 < n + (w - n) := hAO2.2.1 (w - n) hk _ (by rw [hins]; simp)
        have iha := ih (opnd C (w - n) 0) (by omega) (by omega)
        have ihb := ih (opnd C (w - n) 1) (by omega) (by omega)
        rcases gateAt_ao n C hAO2 (w - n) hk with hop | hop
        · constructor
          · intro a hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).2 hop] at hvec
            rcases hvec with ⟨va, hva, vb, hvb, hcap⟩
            obtain ⟨a1, b1, rfl, _⟩ := hVecPos (opnd C (w - n) 0) (by omega) va hva
            obtain ⟨a2, b2, rfl, _⟩ := hVecPos (opnd C (w - n) 1) (by omega) vb hvb
            have hb0 : b1 = 0 ∧ b2 = 0 := by
              simp only [S, List.map_cons, List.map_nil, capAdd_two, List.cons.injEq] at hcap
              omega
            rcases hb0 with ⟨rfl, rfl⟩
            rw [wireVal_gate n C (w - n) hk, hop, hins]
            simp [GateOp.eval, ha, hb, iha.1 a1 hva, ihb.1 a2 hvb]
          · intro b hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).2 hop] at hvec
            rcases hvec with ⟨va, hva, vb, hvb, hcap⟩
            obtain ⟨a1, b1, rfl, _⟩ := hVecPos (opnd C (w - n) 0) (by omega) va hva
            obtain ⟨a2, b2, rfl, _⟩ := hVecPos (opnd C (w - n) 1) (by omega) vb hvb
            have ha0 : a1 = 0 ∧ a2 = 0 := by
              simp only [S, List.map_cons, List.map_nil, capAdd_two, List.cons.injEq] at hcap
              omega
            rcases ha0 with ⟨rfl, rfl⟩
            rw [wireVal_gate n C (w - n) hk, hop, hins]
            simp [GateOp.eval, ha, hb, iha.2 b1 hva, ihb.2 b2 hvb]
        · constructor
          · intro a hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).1 hop] at hvec
            rw [wireVal_gate n C (w - n) hk, hop, hins]
            rcases hvec with hva | hvb
            · simp [GateOp.eval, ha, hb, iha.1 a hva]
            · simp [GateOp.eval, ha, hb, ihb.1 a hvb]
          · intro b hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).1 hop] at hvec
            rw [wireVal_gate n C (w - n) hk, hop, hins]
            rcases hvec with hva | hvb
            · simp [GateOp.eval, ha, hb, iha.2 b hva]
            · simp [GateOp.eval, ha, hb, ihb.2 b hvb]
  have hUnitOrIn : ∀ w, w < n + C.gates.length →
      ([1, 0] ∈ (readVectors C n S 1).getD w [] → u ∈ orIn n C w) ∧
      ([0, 1] ∈ (readVectors C n S 1).getD w [] → v ∈ orIn n C w) := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw
      by_cases hlt : w < n
      · rw [readVectors_at_input C n S 1 w hlt, orIn_input n C w hlt]
        constructor
        · intro hvec
          unfold leafVectors at hvec
          by_cases hmem : w ∈ S
          · simp only [hmem, ↓reduceIte, List.mem_singleton] at hvec
            have hwu : w = u.val := by
              by_contra hne
              have hwv : w = v.val := by
                simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hmem
                exact hmem.resolve_left hne
              subst hwv
              simp only [S, List.map_cons, List.map_nil, huv_val, ↓reduceIte, List.cons.injEq] at hvec
              omega
            rw [Finset.mem_singleton]
            exact Fin.ext hwu.symm
          · simp only [hmem, ↓reduceIte, List.not_mem_nil] at hvec
        · intro hvec
          unfold leafVectors at hvec
          by_cases hmem : w ∈ S
          · simp only [hmem, ↓reduceIte, List.mem_singleton] at hvec
            have hwv : w = v.val := by
              by_contra hne
              have hwu : w = u.val := by
                simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hmem
                exact hmem.resolve_right hne
              subst hwu
              simp only [S, List.map_cons, List.map_nil, Ne.symm huv_val, ↓reduceIte, List.cons.injEq] at hvec
              omega
            rw [Finset.mem_singleton]
            exact Fin.ext hwv.symm
          · simp only [hmem, ↓reduceIte, List.not_mem_nil] at hvec
      · have hk : w - n < C.gates.length := by omega
        have heq : n + (w - n) = w := by omega
        rw [← heq]
        have hins := gateAt_two_inputs n C hAO2 (w - n) hk
        have ha : opnd C (w - n) 0 < n + (w - n) := hAO2.2.1 (w - n) hk _ (by rw [hins]; simp)
        have hb : opnd C (w - n) 1 < n + (w - n) := hAO2.2.1 (w - n) hk _ (by rw [hins]; simp)
        have iha := ih (opnd C (w - n) 0) (by omega) (by omega)
        have ihb := ih (opnd C (w - n) 1) (by omega) (by omega)
        rcases gateAt_ao n C hAO2 (w - n) hk with hop | hop
        · constructor
          · intro hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).2 hop] at hvec
            rcases hvec with ⟨va, hva, vb, hvb, hcap⟩
            obtain ⟨a1, b1, rfl, hp1⟩ := hVecPos (opnd C (w - n) 0) (by omega) va hva
            obtain ⟨a2, b2, rfl, hp2⟩ := hVecPos (opnd C (w - n) 1) (by omega) vb hvb
            simp only [S, List.map_cons, List.map_nil, capAdd_two, List.cons.injEq] at hcap
            omega
          · intro hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).2 hop] at hvec
            rcases hvec with ⟨va, hva, vb, hvb, hcap⟩
            obtain ⟨a1, b1, rfl, hp1⟩ := hVecPos (opnd C (w - n) 0) (by omega) va hva
            obtain ⟨a2, b2, rfl, hp2⟩ := hVecPos (opnd C (w - n) 1) (by omega) vb hvb
            simp only [S, List.map_cons, List.map_nil, capAdd_two, List.cons.injEq] at hcap
            omega
        · rw [orIn_or n C hAO2 (w - n) hk hop]
          constructor
          · intro hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).1 hop] at hvec
            rcases hvec with hva | hvb
            · exact Finset.mem_union_left _ (iha.1 hva)
            · exact Finset.mem_union_right _ (ihb.1 hvb)
          · intro hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).1 hop] at hvec
            rcases hvec with hva | hvb
            · exact Finset.mem_union_left _ (iha.2 hva)
            · exact Finset.mem_union_right _ (ihb.2 hvb)
  have hNoOneOneInput : ∀ w < n, [1, 1] ∉ (readVectors C n S 1).getD w [] := by
    intro w hw hvec
    rw [readVectors_at_input C n S 1 w hw] at hvec
    unfold leafVectors at hvec
    by_cases hmem : w ∈ S
    · simp only [hmem, ↓reduceIte, List.mem_singleton] at hvec
      simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · simp only [S, List.map_cons, List.map_nil, Ne.symm huv_val, ↓reduceIte,
          List.cons.injEq] at hvec
        omega
      · simp only [S, List.map_cons, List.map_nil, huv_val, ↓reduceIte,
          List.cons.injEq] at hvec
        omega
    · simp only [hmem, ↓reduceIte, List.not_mem_nil] at hvec
  have hOneOneAnd : ∀ g, g < C.gates.length →
      [1, 1] ∈ (readVectors C n S 1).getD (n + g) [] →
      ∃ a < C.gates.length, OrReaches n C (n + g) a ∧ (gateAt C a).op = GateOp.and ∧
        ((u ∈ side C a 0 ∧ v ∈ side C a 1) ∨ (v ∈ side C a 0 ∧ u ∈ side C a 1)) := by
    intro g
    induction g using Nat.strongRecOn with
    | ind g ih =>
      intro hg hvec
      have hins := gateAt_two_inputs n C hAO2 g hg
      have ha : opnd C g 0 < n + g := hAO2.2.1 g hg _ (by rw [hins]; simp)
      have hb : opnd C g 1 < n + g := hAO2.2.1 g hg _ (by rw [hins]; simp)
      rcases gateAt_ao n C hAO2 g hg with hop | hop
      · rw [(readVectors_at_gate C n S 1 g hg hAO2).2 hop] at hvec
        rcases hvec with ⟨va, hva, vb, hvb, hcap⟩
        obtain ⟨a1, b1, rfl, hp1⟩ := hVecPos (opnd C g 0) (by omega) va hva
        obtain ⟨a2, b2, rfl, hp2⟩ := hVecPos (opnd C g 1) (by omega) vb hvb
        have hcases : (a1 = 1 ∧ b1 = 0 ∧ a2 = 0 ∧ b2 = 1) ∨
            (a1 = 0 ∧ b1 = 1 ∧ a2 = 1 ∧ b2 = 0) := by
          simp only [S, List.map_cons, List.map_nil, capAdd_two, List.cons.injEq] at hcap
          omega
        refine ⟨g, hg, orReaches_refl n C g hg, hop, ?_⟩
        rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · left
          exact ⟨(hUnitOrIn (opnd C g 0) (by omega)).1 hva,
                 (hUnitOrIn (opnd C g 1) (by omega)).2 hvb⟩
        · right
          exact ⟨(hUnitOrIn (opnd C g 0) (by omega)).2 hva,
                 (hUnitOrIn (opnd C g 1) (by omega)).1 hvb⟩
      · rw [(readVectors_at_gate C n S 1 g hg hAO2).1 hop] at hvec
        rcases hvec with hva | hvb
        · have hge : n ≤ opnd C g 0 := by
            by_contra hlt; push Not at hlt; exact hNoOneOneInput (opnd C g 0) hlt hva
          have heq : n + (opnd C g 0 - n) = opnd C g 0 := by omega
          rw [← heq] at hva
          obtain ⟨a, ha_lt, hor, hopa, hsides⟩ := ih (opnd C g 0 - n) (by omega) (by omega) hva
          refine ⟨a, ha_lt, ?_, hopa, hsides⟩
          rw [orReaches_iff n C g a hg]
          right
          exact ⟨hop, opnd C g 0, by rw [hins]; simp, hge, ha, by rwa [← heq]⟩
        · have hge : n ≤ opnd C g 1 := by
            by_contra hlt; push Not at hlt; exact hNoOneOneInput (opnd C g 1) hlt hvb
          have heq : n + (opnd C g 1 - n) = opnd C g 1 := by omega
          rw [← heq] at hvb
          obtain ⟨a, ha_lt, hor, hopa, hsides⟩ := ih (opnd C g 1 - n) (by omega) (by omega) hvb
          refine ⟨a, ha_lt, ?_, hopa, hsides⟩
          rw [orReaches_iff n C g a hg]
          right
          exact ⟨hop, opnd C g 1, by rw [hins]; simp, hge, hb, by rwa [← heq]⟩
  have hTrue : readsAtMost (atGate n C (C.output - n)) n S 1 = true := by
    unfold ReadTwiceAt at hOnce
    exact Bool.eq_true_of_not_eq_false hOnce
  unfold readsAtMost atGate at hTrue
  rw [List.any_eq_true] at hTrue
  rcases hTrue with ⟨vec, hvec, hle⟩
  have hout_eq : n + (C.output - n) = C.output := by omega
  change vec ∈ (readVectors C n S 1).getD (n + (C.output - n)) [] at hvec
  rw [hout_eq] at hvec
  obtain ⟨a, b, rfl, _⟩ := hVecPos C.output hOutLt vec hvec
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hle
  have hbne0 : b ≠ 0 := by
    intro hb0; subst hb0
    have hsing := (hZeroCheck C.output hOutLt).1 a hvec
    have h1 := congrFun hFun (fun i => decide (i = u))
    have hc : circuitFun n C (fun i => decide (i = u)) = true := hsing
    rw [hc, graphFun_single_false G u] at h1
    cases h1
  have hane0 : a ≠ 0 := by
    intro ha0; subst ha0
    have hsing := (hZeroCheck C.output hOutLt).2 b hvec
    have h1 := congrFun hFun (fun i => decide (i = v))
    have hc : circuitFun n C (fun i => decide (i = v)) = true := hsing
    rw [hc, graphFun_single_false G v] at h1
    cases h1
  have ha1 : a = 1 := by omega
  have hb1 : b = 1 := by omega
  subst ha1; subst hb1
  rw [← hout_eq] at hvec ⊢
  exact hOneOneAnd (C.output - n) (by omega) hvec

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (T : Finset (Fin n)),
  PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ((G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)) : Set (Sym2 (Fin n)))) T →
  G.edgeFinset.card + T.card ≤ C.size + (G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)).card + 1 := by
  classical
  intro n G _ C T hC4 hAO2 hFun hMinCov
  let D : Finset (Sym2 (Fin n)) :=
    G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ ReadTwiceAt n C (C.output - n) u v)
  let R_edges : Finset (Sym2 (Fin n)) := G.edgeFinset \ D
  have hDsub : D ⊆ G.edgeFinset := Finset.filter_subset _ _
  have hEsplit : R_edges.card + D.card = G.edgeFinset.card :=
    Finset.card_sdiff_add_card_eq_card hDsub
  by_cases hRempty : R_edges = ∅
  · have hcov0 : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover ((∅ : Finset (Fin n)) : Set (Fin n)) := by
      intro u v huv
      rw [SimpleGraph.deleteEdges_adj] at huv
      exfalso
      have hmem : s(u, v) ∈ R_edges := by
        rw [Finset.mem_sdiff]
        exact ⟨SimpleGraph.mem_edgeFinset.mpr huv.1, huv.2⟩
      rw [hRempty] at hmem
      simp at hmem
    have hT0 : T.card ≤ (∅ : Finset (Fin n)).card := hMinCov.2 ∅ hcov0
    simp only [Finset.card_empty] at hT0
    rw [hRempty, Finset.card_empty, Nat.zero_add] at hEsplit
    change G.edgeFinset.card + T.card ≤ C.size + D.card + 1
    omega
  obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hRempty
  obtain ⟨u0, v0, he0_eq⟩ : ∃ u0 v0 : Fin n, e0 = s(u0, v0) :=
    Sym2.ind (fun a b => ⟨a, b, rfl⟩) e0
  have he0_mem := Finset.mem_sdiff.mp he0
  have hAdj0 : G.Adj u0 v0 := by
    have : s(u0, v0) ∈ G.edgeFinset := he0_eq ▸ he0_mem.1
    exact SimpleGraph.mem_edgeFinset.mp this
  have hOnce0 : ¬ ReadTwiceAt n C (C.output - n) u0 v0 := by
    intro hrt
    apply he0_mem.2
    rw [Finset.mem_filter]
    exact ⟨he0_mem.1, u0, v0, he0_eq, hrt⟩
  obtain ⟨hOutGe, hOutLt, _⟩ := read_once_to_top_and G C hAO2 hFun u0 v0 hAdj0 hOnce0
  let gout := C.output - n
  have hgout_lt : gout < C.gates.length := by omega
  have hgout_eq : n + gout = C.output := by omega
  have hBelowOfOr : ∀ g < C.gates.length, OrReaches n C C.output g → BelowF G C g := by
    intro g _ hor x hx
    have h1 := congrFun hFun x
    have hval : wireVal n C C.output x = true := orReaches_wireVal_any n C C.output g x hor hx
    have hc : circuitFun n C x = true := hval
    rw [← h1, hc]
  let Prod : Finset ℕ := (Finset.range C.gates.length).filter (fun a =>
    (gateAt C a).op = GateOp.and ∧ OrReaches n C C.output a ∧
      (side (n := n) C a 0).Nonempty ∧ (side (n := n) C a 1).Nonempty)
  have hProdCrossAdj : ∀ a ∈ Prod, ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side (n := n) C a 1, G.Adj x y := by
    intro a ha x hx y hy
    simp only [Prod, Finset.mem_filter, Finset.mem_range] at ha
    rcases ha with ⟨ha_lt, ha_and, ha_or, _, _⟩
    have hbel := hBelowOfOr a ha_lt ha_or
    have hxy_val : gateVal n C a (pairInput x y) = true := by
      show wireVal n C (n + a) (pairInput x y) = true
      have hins := gateAt_two_inputs n C hAO2 a ha_lt
      have h0 : opnd C a 0 < n + a := hAO2.2.1 a ha_lt _ (by rw [hins]; simp)
      have h1 : opnd C a 1 < n + a := hAO2.2.1 a ha_lt _ (by rw [hins]; simp)
      have hv0 : wireVal n C (opnd C a 0) (pairInput x y) = true :=
        orIn_wireVal n C (opnd C a 0) x (pairInput x y) hx (by simp [pairInput])
      have hv1 : wireVal n C (opnd C a 1) (pairInput x y) = true :=
        orIn_wireVal n C (opnd C a 1) y (pairInput x y) hy (by simp [pairInput])
      rw [wireVal_gate n C a ha_lt, ha_and, hins]
      simp [GateOp.eval, h0, h1, hv0, hv1]
    have hgf := hbel (pairInput x y) hxy_val
    unfold graphFun at hgf
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq] at hgf
    rcases hgf with ⟨p, q, hpq, hp, hq⟩
    simp only [pairInput, decide_eq_true_eq] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exfalso; exact G.loopless.irrefl _ hpq
    · exact hpq
    · exact hpq.symm
    · exfalso; exact G.loopless.irrefl _ hpq
  have hProdCardOne : ∀ a ∈ Prod, (side (n := n) C a 0).card = 1 ∨ (side (n := n) C a 1).card = 1 := by
    intro a ha
    have ha' := ha
    simp only [Prod, Finset.mem_filter, Finset.mem_range] at ha'
    by_contra hboth
    push Not at hboth
    have h0ge : 2 ≤ (side (n := n) C a 0).card := by
      have hpos := Finset.card_pos.mpr ha'.2.2.2.1
      omega
    have h1ge : 2 ≤ (side (n := n) C a 1).card := by
      have hpos := Finset.card_pos.mpr ha'.2.2.2.2
      omega
    obtain ⟨x1, hx1, x2, hx2, hxne⟩ := Finset.one_lt_card.mp (by omega : 1 < (side (n := n) C a 0).card)
    obtain ⟨y1, hy1, y2, hy2, hyne⟩ := Finset.one_lt_card.mp (by omega : 1 < (side (n := n) C a 1).card)
    have hsub : ({y1, y2} : Finset (Fin n)) ⊆ Finset.univ.filter (fun w => G.Adj x1 w ∧ G.Adj x2 w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with hwy | hwy
      · rw [hwy]; exact ⟨hProdCrossAdj a ha x1 hx1 y1 hy1, hProdCrossAdj a ha x2 hx2 y1 hy1⟩
      · rw [hwy]; exact ⟨hProdCrossAdj a ha x1 hx1 y2 hy2, hProdCrossAdj a ha x2 hx2 y2 hy2⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 : ({y1, y2} : Finset (Fin n)).card = 2 := Finset.card_pair hyne
    have hc3 := hC4 x1 x2 hxne
    omega
  let centre : ℕ → Fin n := fun a =>
    if h0 : (side (n := n) C a 0).card = 1 then (Finset.card_eq_one.mp h0).choose
    else if h1 : (side (n := n) C a 1).card = 1 then (Finset.card_eq_one.mp h1).choose
    else u0
  let leafB : ℕ → Fin 2 := fun a => if (side (n := n) C a 0).card = 1 then 1 else 0
  let L : ℕ → Finset (Fin n) := fun a => side (n := n) C a (leafB a)
  have hCentreProps : ∀ a ∈ Prod,
      (L a).Nonempty ∧ (∀ v ∈ L a, G.Adj (centre a) v) ∧
      (∀ x ∈ side (n := n) C a 0, ∀ y ∈ side (n := n) C a 1,
        (x = centre a ∧ y ∈ L a) ∨ (y = centre a ∧ x ∈ L a)) := by
    intro a ha
    have ha' := ha
    simp only [Prod, Finset.mem_filter, Finset.mem_range] at ha'
    by_cases h0 : (side (n := n) C a 0).card = 1
    · have hspec : side (n := n) C a 0 = {(Finset.card_eq_one.mp h0).choose} :=
        (Finset.card_eq_one.mp h0).choose_spec
      have hc_eq : centre a = (Finset.card_eq_one.mp h0).choose := by simp [centre, h0]
      have hL_eq : L a = side (n := n) C a 1 := by simp [L, leafB, h0]
      have hc_mem : centre a ∈ side (n := n) C a 0 := by
        rw [hc_eq]
        exact Eq.mpr (congrArg (fun S => (Finset.card_eq_one.mp h0).choose ∈ S) hspec)
          (Finset.mem_singleton_self _)
      refine ⟨hL_eq ▸ ha'.2.2.2.2, ?_, ?_⟩
      · intro v hv
        rw [hL_eq] at hv
        exact hProdCrossAdj a ha (centre a) hc_mem v hv
      · intro x hx y hy
        left
        rw [hspec, Finset.mem_singleton] at hx
        exact ⟨hx.trans hc_eq.symm, hL_eq ▸ hy⟩
    · have h1 : (side (n := n) C a 1).card = 1 := (hProdCardOne a ha).resolve_left h0
      have hspec : side (n := n) C a 1 = {(Finset.card_eq_one.mp h1).choose} :=
        (Finset.card_eq_one.mp h1).choose_spec
      have hc_eq : centre a = (Finset.card_eq_one.mp h1).choose := by simp [centre, h0, h1]
      have hL_eq : L a = side (n := n) C a 0 := by simp [L, leafB, h0]
      have hc_mem : centre a ∈ side (n := n) C a 1 := by
        rw [hc_eq]
        exact Eq.mpr (congrArg (fun S => (Finset.card_eq_one.mp h1).choose ∈ S) hspec)
          (Finset.mem_singleton_self _)
      refine ⟨hL_eq ▸ ha'.2.2.2.1, ?_, ?_⟩
      · intro v hv
        rw [hL_eq] at hv
        exact (hProdCrossAdj a ha v hv (centre a) hc_mem).symm
      · intro x hx y hy
        right
        rw [hspec, Finset.mem_singleton] at hy
        exact ⟨hy.trans hc_eq.symm, hL_eq ▸ hx⟩
  have hEdgeCovered : ∀ u v : Fin n, G.Adj u v → s(u, v) ∉ D →
      ∃ a ∈ Prod, (u = centre a ∧ v ∈ L a) ∨ (v = centre a ∧ u ∈ L a) := by
    intro u v hadj hnotD
    have hOnce : ¬ ReadTwiceAt n C (C.output - n) u v := by
      intro hrt
      apply hnotD
      rw [Finset.mem_filter]
      exact ⟨SimpleGraph.mem_edgeFinset.mpr hadj, u, v, rfl, hrt⟩
    obtain ⟨_, _, a, ha_lt, ha_or, ha_and, hsides⟩ := read_once_to_top_and G C hAO2 hFun u v hadj hOnce
    have ha_prod : a ∈ Prod := by
      simp only [Prod, Finset.mem_filter, Finset.mem_range]
      refine ⟨ha_lt, ha_and, ha_or, ?_, ?_⟩
      · rcases hsides with ⟨hu, _⟩ | ⟨hv, _⟩
        · exact ⟨u, hu⟩
        · exact ⟨v, hv⟩
      · rcases hsides with ⟨_, hv⟩ | ⟨_, hu⟩
        · exact ⟨v, hv⟩
        · exact ⟨u, hu⟩
    have hcp := (hCentreProps a ha_prod).2.2
    rcases hsides with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact ⟨a, ha_prod, hcp u hu v hv⟩
    · rcases hcp v hv u hu with h | h
      · exact ⟨a, ha_prod, Or.inr h⟩
      · exact ⟨a, ha_prod, Or.inl h⟩
  have hProdNE : Prod.Nonempty := by
    obtain ⟨a, ha, _⟩ := hEdgeCovered u0 v0 hAdj0 (by simpa [he0_eq] using he0_mem.2)
    exact ⟨a, ha⟩
  let C_set : Finset (Fin n) := Prod.image centre
  have hCset_cov : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover (C_set : Set (Fin n)) := by
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    obtain ⟨a, ha, hcase⟩ := hEdgeCovered u v huv.1 huv.2
    have hcmem : centre a ∈ C_set := Finset.mem_image_of_mem centre ha
    rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · left; exact hcmem
    · right; exact hcmem
  have hT_le_Prod : T.card ≤ Prod.card :=
    (hMinCov.2 C_set hCset_cov).trans Finset.card_image_le
  let Prod_c : Fin n → Finset ℕ := fun c => Prod.filter (fun a => centre a = c)
  let U_c : Fin n → Finset (Fin n) := fun c => (Prod_c c).biUnion L
  have hR_le_sumU : R_edges.card ≤ ∑ c ∈ C_set, (U_c c).card := by
    have hsub : R_edges ⊆ C_set.biUnion (fun c => (U_c c).image (fun v => s(c, v))) := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have hmem := Finset.mem_sdiff.mp he
        have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp hmem.1
        obtain ⟨a, ha, hcase⟩ := hEdgeCovered u v hadj hmem.2
        rw [Finset.mem_biUnion]
        refine ⟨centre a, Finset.mem_image_of_mem centre ha, ?_⟩
        rw [Finset.mem_image]
        have ha_pc : a ∈ Prod_c (centre a) := Finset.mem_filter.mpr ⟨ha, rfl⟩
        rcases hcase with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
        · exact ⟨v, Finset.mem_biUnion.mpr ⟨a, ha_pc, hv⟩, rfl⟩
        · exact ⟨u, Finset.mem_biUnion.mpr ⟨a, ha_pc, hu⟩, Sym2.eq_swap⟩
    calc R_edges.card
        ≤ (C_set.biUnion (fun c => (U_c c).image (fun v => s(c, v)))).card := Finset.card_le_card hsub
      _ ≤ ∑ c ∈ C_set, ((U_c c).image (fun v => s(c, v))).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ C_set, (U_c c).card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
  let TopOR : Finset ℕ := (Finset.range C.gates.length).filter (fun g =>
    (gateAt C g).op = GateOp.or ∧ OrReaches n C C.output g)
  let LeafOR : Fin n → Finset ℕ := fun c => (Finset.range C.gates.length).filter (fun h =>
    (gateAt C h).op = GateOp.or ∧ 2 ≤ (orIn n C (n + h)).card ∧ ∀ v ∈ orIn n C (n + h), G.Adj c v)
  have hTopOR_bound : Prod.card ≤ TopOR.card + 1 := by
    let reached : ℕ → Finset ℕ := fun w => Prod.filter (fun a => OrReaches n C w a)
    obtain ⟨Etop, hElen, hEmem⟩ := exists_pair_list TopOR
      (fun g => reached (opnd C g 0)) (fun g => reached (opnd C g 1))
    obtain ⟨col, hcol_card, hcol_eq⟩ := pair_merge_card Prod Etop
    have hConst : ∀ w, w < n + C.gates.length →
        (n ≤ w → OrReaches n C C.output (w - n)) →
        ∀ a1 ∈ reached w, ∀ a2 ∈ reached w, col a1 = col a2 := by
      intro w
      induction w using Nat.strongRecOn with
      | ind w ih =>
        intro hw hreach a1 ha1 a2 ha2
        have ha1' := Finset.mem_filter.mp ha1
        have ha2' := Finset.mem_filter.mp ha2
        have hwn : n ≤ w := ha1'.2.1
        have hg_lt : w - n < C.gates.length := by omega
        have hwg : n + (w - n) = w := by omega
        rcases gateAt_ao n C hAO2 (w - n) hg_lt with hop | hop
        · have h1 : a1 = w - n := by
            have h := ha1'.2
            rw [← hwg, orReaches_iff n C (w - n) a1 hg_lt] at h
            rcases h with rfl | ⟨hor, _⟩
            · rfl
            · rw [hop] at hor; cases hor
          have h2 : a2 = w - n := by
            have h := ha2'.2
            rw [← hwg, orReaches_iff n C (w - n) a2 hg_lt] at h
            rcases h with rfl | ⟨hor, _⟩
            · rfl
            · rw [hop] at hor; cases hor
          rw [h1, h2]
        · have htop_mem : w - n ∈ TopOR := by
            simp only [TopOR, Finset.mem_filter, Finset.mem_range]
            exact ⟨hg_lt, hop, hreach hwn⟩
          have hins := gateAt_two_inputs n C hAO2 (w - n) hg_lt
          have h0 : opnd C (w - n) 0 < w := by
            have := hAO2.2.1 (w - n) hg_lt (opnd C (w - n) 0) (by rw [hins]; simp); omega
          have h1 : opnd C (w - n) 1 < w := by
            have := hAO2.2.1 (w - n) hg_lt (opnd C (w - n) 1) (by rw [hins]; simp); omega
          have hsplit_a : ∀ a ∈ reached w,
              a ∈ reached (opnd C (w - n) 0) ∨ a ∈ reached (opnd C (w - n) 1) := by
            intro a ha
            have ha' := Finset.mem_filter.mp ha
            have ha_and : (gateAt C a).op = GateOp.and := (Finset.mem_filter.mp ha'.1).2.1
            have hor := ha'.2
            rw [← hwg, orReaches_iff n C (w - n) a hg_lt] at hor
            rcases hor with rfl | ⟨_, u', hu', _, _, hor'⟩
            · rw [hop] at ha_and; cases ha_and
            · rw [hins] at hu'
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
              rcases hu' with rfl | rfl
              · left; exact Finset.mem_filter.mpr ⟨ha'.1, hor'⟩
              · right; exact Finset.mem_filter.mpr ⟨ha'.1, hor'⟩
          have hreach_b : ∀ b : Fin 2, n ≤ opnd C (w - n) b →
              OrReaches n C C.output (opnd C (w - n) b - n) := by
            intro b hge
            have hltb : opnd C (w - n) b < n + (w - n) := by fin_cases b <;> dsimp <;> omega
            have hmem_b : n + (opnd C (w - n) b - n) ∈ (gateAt C (w - n)).inputs := by
              have : n + (opnd C (w - n) b - n) = opnd C (w - n) b := by omega
              rw [this, hins]; fin_cases b <;> simp
            rw [← hgout_eq]
            exact orReaches_step n C (w - n) (opnd C (w - n) b - n) hg_lt hop hmem_b (by omega)
              gout hgout_lt (by rw [hgout_eq]; exact hreach hwn)
          have hih0 := ih (opnd C (w - n) 0) h0 (by omega) (hreach_b 0)
          have hih1 := ih (opnd C (w - n) 1) h1 (by omega) (hreach_b 1)
          rcases hsplit_a a1 ha1 with h10 | h11 <;> rcases hsplit_a a2 ha2 with h20 | h21
          · exact hih0 a1 h10 a2 h20
          · obtain ⟨x, hx, y, hy, hxy⟩ := hEmem (w - n) htop_mem ⟨a1, h10⟩ ⟨a2, h21⟩
            exact (hih0 a1 h10 x hx).trans ((hcol_eq (x, y) hxy).trans (hih1 y hy a2 h21))
          · obtain ⟨x, hx, y, hy, hxy⟩ := hEmem (w - n) htop_mem ⟨a2, h20⟩ ⟨a1, h11⟩
            exact (hih1 a1 h11 y hy).trans ((hcol_eq (x, y) hxy).symm.trans (hih0 x hx a2 h20))
          · exact hih1 a1 h11 a2 h21
    have hreachOut : reached C.output = Prod := by
      ext a
      simp only [reached, Finset.mem_filter, and_iff_left_iff_imp]
      intro ha
      exact (Finset.mem_filter.mp ha).2.2.1
    obtain ⟨a0, ha0⟩ := hProdNE
    have hImgSub : Prod.image col ⊆ {col a0} := by
      intro z hz
      rw [Finset.mem_image] at hz
      rcases hz with ⟨a, ha, rfl⟩
      rw [Finset.mem_singleton]
      have hout_or : OrReaches n C C.output (C.output - n) := by
        conv_lhs => rw [← hgout_eq]
        exact orReaches_refl n C gout hgout_lt
      exact hConst C.output hOutLt (fun _ => hout_or)
        a (hreachOut ▸ ha) a0 (hreachOut ▸ ha0)
    have hImgCard : (Prod.image col).card ≤ 1 := by
      calc (Prod.image col).card ≤ ({col a0} : Finset ℕ).card := Finset.card_le_card hImgSub
        _ = 1 := Finset.card_singleton _
    omega
  have hLeafOR_bound : ∀ c ∈ C_set, (U_c c).card ≤ (Prod_c c).card + (LeafOR c).card := by
    intro c _
    obtain ⟨Ec, hElen, hEmem⟩ := exists_pair_list (LeafOR c)
      (fun h => orIn n C (opnd C h 0)) (fun h => orIn n C (opnd C h 1))
    obtain ⟨col, hcol_card, hcol_eq⟩ := pair_merge_card (U_c c) Ec
    have hConst : ∀ w, w < n + C.gates.length → (∀ v ∈ orIn n C w, G.Adj c v) →
        ∀ v1 ∈ orIn n C w, ∀ v2 ∈ orIn n C w, col v1 = col v2 := by
      intro w
      induction w using Nat.strongRecOn with
      | ind w ih =>
        intro hw hadj_w v1 hv1 v2 hv2
        by_cases hle1 : (orIn n C w).card ≤ 1
        · have heq : v1 = v2 := Finset.card_le_one.mp hle1 v1 hv1 v2 hv2
          rw [heq]
        · have hge2 : 2 ≤ (orIn n C w).card := by omega
          have hwn : n ≤ w := by
            by_contra hlt
            push Not at hlt
            rw [orIn_input n C w hlt, Finset.card_singleton] at hge2
            omega
          have hh_lt : w - n < C.gates.length := by omega
          have hwh : n + (w - n) = w := by omega
          have hop : (gateAt C (w - n)).op = GateOp.or := by
            rcases gateAt_ao n C hAO2 (w - n) hh_lt with hand | hor
            · exfalso
              rw [← hwh, orIn_and n C (w - n) hh_lt hand, Finset.card_empty] at hge2
              omega
            · exact hor
          have hleaf_mem : w - n ∈ LeafOR c := by
            simp only [LeafOR, Finset.mem_filter, Finset.mem_range]
            exact ⟨hh_lt, hop, by rwa [hwh], by intro v hv; exact hadj_w v (hwh ▸ hv)⟩
          have hins := gateAt_two_inputs n C hAO2 (w - n) hh_lt
          have h0 : opnd C (w - n) 0 < w := by
            have := hAO2.2.1 (w - n) hh_lt (opnd C (w - n) 0) (by rw [hins]; simp); omega
          have h1 : opnd C (w - n) 1 < w := by
            have := hAO2.2.1 (w - n) hh_lt (opnd C (w - n) 1) (by rw [hins]; simp); omega
          have hunion : orIn n C w = orIn n C (opnd C (w - n) 0) ∪ orIn n C (opnd C (w - n) 1) := by
            conv_lhs => rw [← hwh]
            exact orIn_or n C hAO2 (w - n) hh_lt hop
          have hadj0 : ∀ v ∈ orIn n C (opnd C (w - n) 0), G.Adj c v :=
            fun v hv => hadj_w v (hunion ▸ Finset.mem_union_left _ hv)
          have hadj1 : ∀ v ∈ orIn n C (opnd C (w - n) 1), G.Adj c v :=
            fun v hv => hadj_w v (hunion ▸ Finset.mem_union_right _ hv)
          have hih0 := ih (opnd C (w - n) 0) h0 (by omega) hadj0
          have hih1 := ih (opnd C (w - n) 1) h1 (by omega) hadj1
          rw [hunion, Finset.mem_union] at hv1 hv2
          rcases hv1 with h10 | h11 <;> rcases hv2 with h20 | h21
          · exact hih0 v1 h10 v2 h20
          · obtain ⟨x, hx, y, hy, hxy⟩ := hEmem (w - n) hleaf_mem ⟨v1, h10⟩ ⟨v2, h21⟩
            exact (hih0 v1 h10 x hx).trans ((hcol_eq (x, y) hxy).trans (hih1 y hy v2 h21))
          · obtain ⟨x, hx, y, hy, hxy⟩ := hEmem (w - n) hleaf_mem ⟨v2, h20⟩ ⟨v1, h11⟩
            exact (hih1 v1 h11 y hy).trans ((hcol_eq (x, y) hxy).symm.trans (hih0 x hx v2 h20))
          · exact hih1 v1 h11 v2 h21
    let rep : ℕ → Fin n := fun a =>
      if hne : (L a).Nonempty then hne.choose else u0
    have hImgSub : (U_c c).image col ⊆ (Prod_c c).image (fun a => col (rep a)) := by
      intro z hz
      rw [Finset.mem_image] at hz
      rcases hz with ⟨v, hv, rfl⟩
      rw [Finset.mem_biUnion] at hv
      rcases hv with ⟨a, ha_pc, hvL⟩
      have ha_prod : a ∈ Prod := (Finset.mem_filter.mp ha_pc).1
      have ha_cen : centre a = c := (Finset.mem_filter.mp ha_pc).2
      have ha_lt : a < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp ha_prod).1
      have hcp := hCentreProps a ha_prod
      have hne : (L a).Nonempty := hcp.1
      have hrep_mem : rep a ∈ L a := by
        simp only [rep, hne, ↓reduceDIte]
        exact hne.choose_spec
      have hwlt : opnd C a (leafB a) < n + C.gates.length := by
        have hins := gateAt_two_inputs n C hAO2 a ha_lt
        have hlt : opnd C a (leafB a) < n + a := by
          apply hAO2.2.1 a ha_lt
          rw [hins]
          generalize leafB a = b
          fin_cases b <;> simp
        omega
      have hadjL : ∀ w ∈ orIn n C (opnd C a (leafB a)), G.Adj c w := by
        intro w hw
        rw [← ha_cen]
        exact hcp.2.1 w hw
      have hce : col v = col (rep a) :=
        hConst (opnd C a (leafB a)) hwlt hadjL v hvL (rep a) hrep_mem
      rw [hce]
      exact Finset.mem_image_of_mem (fun a => col (rep a)) ha_pc
    have hImgCard : ((U_c c).image col).card ≤ (Prod_c c).card :=
      (Finset.card_le_card hImgSub).trans Finset.card_image_le
    omega
  have hLeafPairwiseDisj : ∀ c1 ∈ C_set, ∀ c2 ∈ C_set, c1 ≠ c2 → Disjoint (LeafOR c1) (LeafOR c2) := by
    intro c1 _ c2 _ hne
    rw [Finset.disjoint_left]
    intro h h1 h2
    simp only [LeafOR, Finset.mem_filter] at h1 h2
    have hsub : orIn n C (n + h) ⊆ Finset.univ.filter (fun w => G.Adj c1 w ∧ G.Adj c2 w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h1.2.2.2 w hw, h2.2.2.2 w hw⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := hC4 c1 c2 hne
    omega
  let AllLeafOR : Finset ℕ := C_set.biUnion LeafOR
  have hAllLeafCard : AllLeafOR.card = ∑ c ∈ C_set, (LeafOR c).card :=
    Finset.card_biUnion hLeafPairwiseDisj
  have hDisj_Prod_Top : Disjoint Prod TopOR := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have h1 := (Finset.mem_filter.mp hg1).2.1
    have h2 := (Finset.mem_filter.mp hg2).2.1
    rw [h1] at h2; cases h2
  have hDisj_Prod_Leaf : Disjoint Prod AllLeafOR := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    rw [Finset.mem_biUnion] at hg2
    rcases hg2 with ⟨c, _, hc⟩
    have h1 := (Finset.mem_filter.mp hg1).2.1
    have h2 := (Finset.mem_filter.mp hc).2.1
    rw [h1] at h2; cases h2
  have hDisj_Top_Leaf : Disjoint TopOR AllLeafOR := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    rw [Finset.mem_biUnion] at hg2
    rcases hg2 with ⟨c, _, hc⟩
    simp only [TopOR, Finset.mem_filter, Finset.mem_range] at hg1
    simp only [LeafOR, Finset.mem_filter, Finset.mem_range] at hc
    have hbel := hBelowOfOr g hg1.1 hg1.2.2
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (orIn n C (n + g)).card)
    have hval : gateVal n C g (fun i => decide (i = v)) = true :=
      orIn_wireVal n C (n + g) v (fun i => decide (i = v)) hv (by simp)
    have hgf := hbel (fun i => decide (i = v)) hval
    rw [graphFun_single_false G v] at hgf
    cases hgf
  have hSumSize : Prod.card + TopOR.card + AllLeafOR.card ≤ C.size := by
    have hsub : Prod ∪ TopOR ∪ AllLeafOR ⊆ Finset.range C.gates.length := by
      intro g hg
      simp only [Finset.mem_union] at hg
      rcases hg with (hg | hg) | hg
      · exact (Finset.mem_filter.mp hg).1
      · exact (Finset.mem_filter.mp hg).1
      · rw [Finset.mem_biUnion] at hg
        rcases hg with ⟨c, _, hc⟩
        exact (Finset.mem_filter.mp hc).1
    have hdisj12 : Disjoint (Prod ∪ TopOR) AllLeafOR :=
      Finset.disjoint_union_left.mpr ⟨hDisj_Prod_Leaf, hDisj_Top_Leaf⟩
    have hcard_union : (Prod ∪ TopOR ∪ AllLeafOR).card = Prod.card + TopOR.card + AllLeafOR.card := by
      rw [Finset.card_union_of_disjoint hdisj12, Finset.card_union_of_disjoint hDisj_Prod_Top]
    calc Prod.card + TopOR.card + AllLeafOR.card
        = (Prod ∪ TopOR ∪ AllLeafOR).card := hcard_union.symm
      _ ≤ (Finset.range C.gates.length).card := Finset.card_le_card hsub
      _ = C.size := by simp [Circuit.size]
  have hProdFiber : Prod.card = ∑ c ∈ C_set, (Prod_c c).card :=
    Finset.card_eq_sum_card_fiberwise (f := centre) (s := Prod) (t := C_set)
      (fun a ha => Finset.mem_image_of_mem centre ha)
  have hSumU : ∑ c ∈ C_set, (U_c c).card ≤ Prod.card + AllLeafOR.card := by
    calc ∑ c ∈ C_set, (U_c c).card
        ≤ ∑ c ∈ C_set, ((Prod_c c).card + (LeafOR c).card) := Finset.sum_le_sum hLeafOR_bound
      _ = (∑ c ∈ C_set, (Prod_c c).card) + (∑ c ∈ C_set, (LeafOR c).card) := Finset.sum_add_distrib
      _ = Prod.card + AllLeafOR.card := by rw [← hProdFiber, ← hAllLeafCard]
  change G.edgeFinset.card + T.card ≤ C.size + D.card + 1
  omega

end PEqualNP.Outside.L_meta_3706_aux

theorem PEqualNP.Outside.L_meta_3706 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (T : Finset (Fin n)),
  PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ((G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)) : Set (Sym2 (Fin n)))) T →
  G.edgeFinset.card + T.card ≤ C.size + (G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)).card + 1 := PEqualNP.Outside.L_meta_3706_aux.main
