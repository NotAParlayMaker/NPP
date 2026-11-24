import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3652_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.ReadTwo PEqualNP.Core

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

lemma wireVal_all_true (n : ℕ) (C : Circuit) (hAO2 : IsAO2 n C) :
    ∀ w, w < n + C.gates.length → wireVal n C w (fun _ => true) = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wireVal_input n C _ w hlt]
    · have hj : w - n < C.gates.length := by omega
      have heq : n + (w - n) = w := by omega
      rw [← heq, wireVal_gate n C (w - n) hj]
      have hins := gateAt_two_inputs n C hAO2 (w - n) hj
      have h0 : opnd C (w - n) 0 < n + (w - n) := hAO2.2.1 (w - n) hj _ (by rw [hins]; simp)
      have h1 : opnd C (w - n) 1 < n + (w - n) := hAO2.2.1 (w - n) hj _ (by rw [hins]; simp)
      have hv0 := ih (opnd C (w - n) 0) (by omega) (by omega)
      have hv1 := ih (opnd C (w - n) 1) (by omega) (by omega)
      rw [hins]
      rcases gateAt_ao n C hAO2 (w - n) hj with hop | hop
      · rw [hop]; simp [GateOp.eval, h0, h1, hv0, hv1]
      · rw [hop]; simp [GateOp.eval, h0, h1, hv0, hv1]

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones coneStep
  have hstep := foldl_append_at
    (fun cs g => (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])) C.gates [] j hj []
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [hstep]
  have hgj : C.gates[j] = gateAt C j := by
    unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
  rw [hgj]
  set pref := (C.gates.take j).foldl
    (fun cs g => cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])]) []
  have hplen : pref.length = j := by
    rw [foldl_append_len, List.length_nil, Nat.zero_add, List.length_take]; omega
  rw [hplen, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    refine ⟨w, hw.1, hw.2.1, hw.2.2, ?_⟩
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · left; rfl
    · right
      have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
      rw [hsplit, List.foldl_append]
      rw [foldl_append_prefix _ (C.gates.drop j) pref (w - n) (by omega) []]
      exact hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hw, hnw, hlt⟩
    · simp only [List.mem_cons]
      rcases hi with rfl | hi
      · left; rfl
      · right
        have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
        rw [hsplit, List.foldl_append] at hi
        rw [foldl_append_prefix _ (C.gates.drop j) pref (w - n) (by omega) []] at hi
        exact hi

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

lemma linearParts_at_input (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) (i : ℕ)
    (hi : i < x.length) :
    (linearParts C isLine x).getD i (false, false) =
      if isLine i then (false, x[i]) else (x[i], false) := by
  unfold linearParts
  have hlen : i < ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)).length := by
    simpa using hi
  rw [foldl_append_prefix _ C.gates _ i hlen (false, false)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma linearParts_at_gate (C : Circuit) (n : ℕ) (isLine : ℕ → Bool) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) (hAO2 : IsAO2 n C) :
    let L := linearParts C isLine x
    let a := opnd C j 0
    let b := opnd C j 1
    ((gateAt C j).op = GateOp.or →
      L.getD (n + j) (false, false) =
        ((L.getD a (false, false)).1 || (L.getD b (false, false)).1,
         (L.getD a (false, false)).2 || (L.getD b (false, false)).2)) ∧
    ((gateAt C j).op = GateOp.and →
      L.getD (n + j) (false, false) =
        ((L.getD a (false, false)).1 && (L.getD b (false, false)).1,
         ((L.getD a (false, false)).1 && (L.getD b (false, false)).2) ||
         ((L.getD a (false, false)).2 && (L.getD b (false, false)).1))) := by
  intro L a b
  have hinit : ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)).length = n := by
    simp [hx]
  have hstep := foldl_append_at
    (fun (w : List (Bool × Bool)) (g : Gate) =>
      let ins := g.inputs.map fun i => w.getD i (false, false)
      match g.op with
      | GateOp.or => (ins.any (·.1), ins.any (·.2))
      | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
          (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
      | _ => (false, false))
    C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) j hj (false, false)
  rw [hinit] at hstep
  have hgj : C.gates[j] = gateAt C j := by
    unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
  rw [hgj] at hstep
  set pref := (C.gates.take j).foldl
    (fun (w : List (Bool × Bool)) (g : Gate) =>
      let ins := g.inputs.map fun i => w.getD i (false, false)
      w ++ [match g.op with
        | GateOp.or => (ins.any (·.1), ins.any (·.2))
        | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
            (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
        | _ => (false, false)])
    ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false))
  have hplen : pref.length = n + j := by
    rw [foldl_append_len, hinit, List.length_take]; omega
  have hpref_eq : ∀ i < n + j, pref.getD i (false, false) = L.getD i (false, false) := by
    intro i hi
    have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    show pref.getD i (false, false) = (linearParts C isLine x).getD i (false, false)
    unfold linearParts
    conv_rhs => rw [hsplit, List.foldl_append]
    exact (foldl_append_prefix _ (C.gates.drop j) pref i (by omega) (false, false)).symm
  have hins := gateAt_two_inputs n C hAO2 j hj
  have ha_lt : a < n + j := hAO2.2.1 j hj a (by rw [hins]; simp [a])
  have hb_lt : b < n + j := hAO2.2.1 j hj b (by rw [hins]; simp [b])
  have hpa : pref.getD (opnd C j 0) (false, false) = L.getD a (false, false) := hpref_eq a ha_lt
  have hpb : pref.getD (opnd C j 1) (false, false) = L.getD b (false, false) := hpref_eq b hb_lt
  constructor
  · intro hop
    change (C.gates.foldl
      (fun (w : List (Bool × Bool)) (g : Gate) =>
        w ++ [let ins := g.inputs.map fun i => w.getD i (false, false)
          match g.op with
          | GateOp.or => (ins.any (·.1), ins.any (·.2))
          | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
              (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
          | _ => (false, false)])
      ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false))).getD (n + j) (false, false) = _
    rw [hstep, hop, hins]
    simp only [List.map_cons, List.map_nil, hpa, hpb, List.any_cons, List.any_nil, Bool.or_false]
  · intro hop
    change (C.gates.foldl
      (fun (w : List (Bool × Bool)) (g : Gate) =>
        w ++ [let ins := g.inputs.map fun i => w.getD i (false, false)
          match g.op with
          | GateOp.or => (ins.any (·.1), ins.any (·.2))
          | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
              (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
          | _ => (false, false)])
      ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false))).getD (n + j) (false, false) = _
    rw [hstep, hop, hins]
    simp only [List.map_cons, List.map_nil, hpa, hpb, List.foldl_cons, List.foldl_nil,
      Bool.true_and, Bool.false_and, Bool.or_false]

lemma capAdd_two (a1 b1 a2 b2 : ℕ) :
    capAdd 1 [a1, b1] [a2, b2] = [min (a1 + a2) 2, min (b1 + b2) 2] := rfl

lemma orReaches_readVectors (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (hAO2 : IsAO2 n C) :
    ∀ g, g < C.gates.length → ∀ j v, OrReaches n C (n + g) j →
      v ∈ (readVectors C n S k).getD (n + j) [] → v ∈ (readVectors C n S k).getD (n + g) [] := by
  intro g
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro hg j v hor hv
    rw [orReaches_iff n C g j hg] at hor
    rcases hor with rfl | ⟨hop, w, hw, hnw, hlt, hor'⟩
    · exact hv
    · have hvw : v ∈ (readVectors C n S k).getD w [] := by
        have heq : n + (w - n) = w := by omega
        rw [← heq] at hor' ⊢
        exact ih (w - n) (by omega) (by omega) j v hor' hv
      have hins := gateAt_two_inputs n C hAO2 g hg
      rw [hins] at hw
      have hrv := (readVectors_at_gate C n S k g hg hAO2).1 hop v
      rw [hrv]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · left; exact hvw
      · right; exact hvw

lemma graphFun_single_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    graphFun G ∅ (fun i => decide (i = u)) = false := by
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_false_iff_not, not_exists, not_and]
  intro a b hadj ha hb
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hadj

theorem main : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone (N + N) C k) → (∀ k2 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → ∀ p1 l1 : Fin N, (p1.val, N + l1.val) ∈ (PEqualNP.ReadK.doubleReread C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))) → ∃ j ∈ PEqualNP.Core.maximalCores G C, s(Fin.castAdd N p1, Fin.natAdd N l1) ∈ PEqualNP.TopForm.gammaE G C j := by
  intro N I _ G _ C hG _ hAO2 hFun hLFP hLive hNoAndBelow p1 l1 hDR
  let n := N + N
  let u : Fin (N + N) := Fin.castAdd N p1
  let v : Fin (N + N) := Fin.natAdd N l1
  have hu_lt : u.val < N := p1.isLt
  have hv_ge : N ≤ v.val := Nat.le_add_right N l1.val
  have huv_ne : u.val ≠ v.val := by omega
  unfold doubleReread at hDR
  rw [List.mem_filter] at hDR
  rcases hDR with ⟨hE, hNotSingle⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hNotSingle
  rcases hNotSingle with ⟨hNoLineSingle, _⟩
  have hIpl : I p1 l1 := by
    rw [List.mem_flatMap] at hE
    rcases hE with ⟨p5, _, hE2⟩
    rw [List.mem_map] at hE2
    rcases hE2 with ⟨l6, hl6, hpair⟩
    rw [List.mem_filter] at hl6
    have hp_eq : p5 = p1 := Fin.ext (by injection hpair)
    have hl_eq : l6 = l1 := Fin.ext (by
      have h2 : N + l6.val = N + l1.val := by injection hpair
      omega)
    rw [← hp_eq, ← hl_eq]
    exact of_decide_eq_true hl6.2
  have hAdj : G.Adj u v := (hG u v).mpr ⟨p1, l1, hIpl, Or.inl ⟨rfl, rfl⟩⟩
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
      rw [wireVal_input n C _ C.output hlt]
      simp
    rw [h2, graphFun_single_false G ⟨C.output, hlt⟩] at h1
    cases h1
  have hOutLt : C.output < n + C.gates.length := by
    by_contra hge
    push Not at hge
    rw [wireVal_ge n C (pairInput u v) C.output hge] at hOutVal
    cases hOutVal
  set gout := C.output - n
  have hgout_lt : gout < C.gates.length := by omega
  have hgout_eq : n + gout = C.output := by omega
  have hgout_below : BelowF G C gout := by
    intro x hx
    have h := congrFun hFun x
    have hc : circuitFun n C x = true := by
      show wireVal n C C.output x = true
      rw [← hgout_eq]; exact hx
    rw [← h, hc]
  have hgout_val : gateVal n C gout (pairInput u v) = true := by
    show wireVal n C (n + gout) (pairInput u v) = true
    rw [hgout_eq]; exact hOutVal
  have hgout_or : OrReaches n C C.output gout := by
    rw [← hgout_eq]; exact orReaches_refl n C gout hgout_lt
  have hDescend : ∀ g, g < C.gates.length → BelowF G C g → OrReaches n C C.output g →
      gateVal n C g (pairInput u v) = true →
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ BelowF G C j ∧
        OrReaches n C C.output j ∧ gateVal n C j (pairInput u v) = true := by
    intro g
    induction g using Nat.strongRecOn with
    | ind g ih =>
      intro hg hbel hor hval
      rcases gateAt_ao n C hAO2 g hg with hop | hop
      · exact ⟨g, hg, hop, hbel, hor, hval⟩
      · have hins := gateAt_two_inputs n C hAO2 g hg
        have h0 : opnd C g 0 < n + g := hAO2.2.1 g hg _ (by rw [hins]; simp)
        have h1 : opnd C g 1 < n + g := hAO2.2.1 g hg _ (by rw [hins]; simp)
        have hv : wireVal n C (opnd C g 0) (pairInput u v) = true ∨
            wireVal n C (opnd C g 1) (pairInput u v) = true := by
          change wireVal n C (n + g) (pairInput u v) = true at hval
          rw [wireVal_gate n C g hg, hop, hins] at hval
          simp only [GateOp.eval, List.map_cons, List.map_nil, h0, h1, ↓reduceIte,
            List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true] at hval
          exact hval
        have hStepWire : ∀ w ∈ (gateAt C g).inputs, w < n + g →
            wireVal n C w (pairInput u v) = true →
            ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ BelowF G C j ∧
              OrReaches n C C.output j ∧ gateVal n C j (pairInput u v) = true := by
          intro w hw hwlt hwval
          have hwbel : ∀ x, wireVal n C w x = true → graphFun G ∅ x = true := by
            intro x hwx
            apply hbel x
            show wireVal n C (n + g) x = true
            rw [wireVal_gate n C g hg, hop]
            simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
            exact ⟨w, hw, by simp only [hwlt, ↓reduceIte]; exact hwx⟩
          have hwn : n ≤ w := by
            by_contra hlt
            push Not at hlt
            have hgf := hwbel (fun i => decide (i = ⟨w, hlt⟩)) (by rw [wireVal_input n C _ w hlt]; simp)
            rw [graphFun_single_false G ⟨w, hlt⟩] at hgf
            cases hgf
          have hg'lt : w - n < g := by omega
          have hmem' : n + (w - n) ∈ (gateAt C g).inputs := by
            have : n + (w - n) = w := by omega
            rwa [this]
          have hor' : OrReaches n C C.output (w - n) := by
            rw [← hgout_eq] at hor ⊢
            exact orReaches_step n C g (w - n) hg hop hmem' hg'lt gout hgout_lt hor
          have hbel' : BelowF G C (w - n) := by
            intro x hx
            apply hwbel x
            have : n + (w - n) = w := by omega
            rwa [← this]
          have hval' : gateVal n C (w - n) (pairInput u v) = true := by
            show wireVal n C (n + (w - n)) (pairInput u v) = true
            have : n + (w - n) = w := by omega
            rwa [this]
          exact ih (w - n) hg'lt (by omega) hbel' hor' hval'
        rcases hv with hv0 | hv1
        · exact hStepWire (opnd C g 0) (by rw [hins]; simp) h0 hv0
        · exact hStepWire (opnd C g 1) (by rw [hins]; simp) h1 hv1
  obtain ⟨j, hj, hjAnd, hjBel, hjOr, hjVal⟩ := hDescend gout hgout_lt hgout_below hgout_or hgout_val
  set S : List ℕ := [u.val, v.val]
  set isLine : ℕ → Bool := fun w => decide (N ≤ w)
  set xL : List Bool := (List.range n).map fun i => i == u.val || i == v.val
  have hxL_len : xL.length = n := by simp [xL]
  have hVecTwo : ∀ w, w < n + C.gates.length →
      ∀ vec ∈ (readVectors C n S 1).getD w [], ∃ a b, vec = [a, b] := by
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
          exact ⟨_, _, rfl⟩
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
          obtain ⟨a1, b1, rfl⟩ := ih (opnd C (w - n) 0) (by omega) (by omega) va hva
          obtain ⟨a2, b2, rfl⟩ := ih (opnd C (w - n) 1) (by omega) (by omega) vb hvb
          exact ⟨_, _, rfl⟩
        · rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).1 hop] at hvec
          rcases hvec with hva | hvb
          · exact ih (opnd C (w - n) 0) (by omega) (by omega) vec hva
          · exact ih (opnd C (w - n) 1) (by omega) (by omega) vec hvb
  have hZeroSecond : ∀ w, w < n + C.gates.length →
      ∀ a, [a, 0] ∈ (readVectors C n S 1).getD w [] →
        wireVal n C w (fun i => decide (i = u)) = true := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw a hvec
      by_cases hlt : w < n
      · rw [readVectors_at_input C n S 1 w hlt] at hvec
        unfold leafVectors at hvec
        by_cases hmem : w ∈ S
        · simp only [hmem, ↓reduceIte, List.mem_singleton] at hvec
          have hwu : w = u.val := by
            by_contra hne
            have hwv : w = v.val := by
              simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hmem
              exact hmem.resolve_left hne
            subst hwv
            simp only [S, List.map_cons, List.map_nil, huv_ne, ↓reduceIte, List.cons.injEq] at hvec
            omega
          rw [wireVal_input n C _ w hlt]
          have hfin : (⟨w, hlt⟩ : Fin (N + N)) = u := Fin.ext hwu
          simp [hfin]
        · simp only [hmem, ↓reduceIte, List.not_mem_nil] at hvec
      · have hk : w - n < C.gates.length := by omega
        have heq : n + (w - n) = w := by omega
        rw [← heq] at hvec ⊢
        have hins := gateAt_two_inputs n C hAO2 (w - n) hk
        have ha : opnd C (w - n) 0 < n + (w - n) := hAO2.2.1 (w - n) hk _ (by rw [hins]; simp)
        have hb : opnd C (w - n) 1 < n + (w - n) := hAO2.2.1 (w - n) hk _ (by rw [hins]; simp)
        rcases gateAt_ao n C hAO2 (w - n) hk with hop | hop
        · rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).2 hop] at hvec
          rcases hvec with ⟨va, hva, vb, hvb, hcap⟩
          obtain ⟨a1, b1, rfl⟩ := hVecTwo (opnd C (w - n) 0) (by omega) va hva
          obtain ⟨a2, b2, rfl⟩ := hVecTwo (opnd C (w - n) 1) (by omega) vb hvb
          have hb0 : b1 = 0 ∧ b2 = 0 := by
            simp only [S, List.map_cons, List.map_nil, capAdd_two, List.cons.injEq] at hcap
            omega
          rcases hb0 with ⟨rfl, rfl⟩
          have hv0 := ih (opnd C (w - n) 0) (by omega) (by omega) a1 hva
          have hv1 := ih (opnd C (w - n) 1) (by omega) (by omega) a2 hvb
          rw [wireVal_gate n C (w - n) hk, hop, hins]
          simp [GateOp.eval, ha, hb, hv0, hv1]
        · rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).1 hop] at hvec
          rw [wireVal_gate n C (w - n) hk, hop, hins]
          rcases hvec with hva | hvb
          · have hv0 := ih (opnd C (w - n) 0) (by omega) (by omega) a hva
            simp [GateOp.eval, ha, hb, hv0]
          · have hv1 := ih (opnd C (w - n) 1) (by omega) (by omega) a hvb
            simp [GateOp.eval, ha, hb, hv1]
  have hVecLin : ∀ w, w < n + C.gates.length →
      (∀ a, [a, 0] ∈ (readVectors C n S 1).getD w [] →
        ((linearParts C isLine xL).getD w (false, false)).1 = true) ∧
      (∀ a, [a, 1] ∈ (readVectors C n S 1).getD w [] →
        ((linearParts C isLine xL).getD w (false, false)).2 = true) := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw
      by_cases hlt : w < n
      · rw [readVectors_at_input C n S 1 w hlt, linearParts_at_input C isLine xL w (by omega)]
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
              simp only [S, List.map_cons, List.map_nil, huv_ne, ↓reduceIte, List.cons.injEq] at hvec
              omega
            subst hwu
            have his : isLine u.val = false := decide_eq_false (by omega)
            simp [his, xL]
          · simp only [hmem, ↓reduceIte, List.not_mem_nil] at hvec
        · intro a hvec
          unfold leafVectors at hvec
          by_cases hmem : w ∈ S
          · simp only [hmem, ↓reduceIte, List.mem_singleton] at hvec
            have hwv : w = v.val := by
              by_contra hne
              have hwu : w = u.val := by
                simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hmem
                exact hmem.resolve_right hne
              subst hwu
              simp only [S, List.map_cons, List.map_nil, Ne.symm huv_ne, ↓reduceIte, List.cons.injEq] at hvec
              omega
            subst hwv
            have his : isLine v.val = true := decide_eq_true hv_ge
            simp [his, xL]
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
        · rw [(linearParts_at_gate C n isLine xL hxL_len (w - n) hk hAO2).2 hop]
          constructor
          · intro a hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).2 hop] at hvec
            rcases hvec with ⟨va, hva, vb, hvb, hcap⟩
            obtain ⟨a1, b1, rfl⟩ := hVecTwo (opnd C (w - n) 0) (by omega) va hva
            obtain ⟨a2, b2, rfl⟩ := hVecTwo (opnd C (w - n) 1) (by omega) vb hvb
            have hb0 : b1 = 0 ∧ b2 = 0 := by
              simp only [S, List.map_cons, List.map_nil, capAdd_two, List.cons.injEq] at hcap
              omega
            rcases hb0 with ⟨rfl, rfl⟩
            rw [iha.1 a1 hva, ihb.1 a2 hvb]; rfl
          · intro a hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).2 hop] at hvec
            rcases hvec with ⟨va, hva, vb, hvb, hcap⟩
            obtain ⟨a1, b1, rfl⟩ := hVecTwo (opnd C (w - n) 0) (by omega) va hva
            obtain ⟨a2, b2, rfl⟩ := hVecTwo (opnd C (w - n) 1) (by omega) vb hvb
            have hb1 : (b1 = 0 ∧ b2 = 1) ∨ (b1 = 1 ∧ b2 = 0) := by
              simp only [S, List.map_cons, List.map_nil, capAdd_two, List.cons.injEq] at hcap
              omega
            rcases hb1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rw [iha.1 a1 hva, ihb.2 a2 hvb]; rfl
            · rw [iha.2 a1 hva, ihb.1 a2 hvb]; simp only [Bool.and_true, Bool.or_true]
        · rw [(linearParts_at_gate C n isLine xL hxL_len (w - n) hk hAO2).1 hop]
          constructor
          · intro a hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).1 hop] at hvec
            rcases hvec with hva | hvb
            · rw [iha.1 a hva]; rfl
            · rw [ihb.1 a hvb]; exact Bool.or_true _
          · intro a hvec
            rw [(readVectors_at_gate C n S 1 (w - n) hk hAO2).1 hop] at hvec
            rcases hvec with hva | hvb
            · rw [iha.2 a hva]; rfl
            · rw [ihb.2 a hvb]; exact Bool.or_true _
  have hReadTwice : ReadTwiceAt n C j u v := by
    unfold ReadTwiceAt readsAtMost atGate
    apply Bool.eq_false_iff.mpr
    intro htrue
    rw [List.any_eq_true] at htrue
    rcases htrue with ⟨vec, hvec, hle⟩
    obtain ⟨a, b, rfl⟩ := hVecTwo (n + j) (by omega) vec hvec
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hle
    have hbne0 : b ≠ 0 := by
      intro hb0
      subst hb0
      have hsing := hZeroSecond (n + j) (by omega) a hvec
      have hgf := hjBel (fun i => decide (i = u)) hsing
      rw [graphFun_single_false G u] at hgf
      cases hgf
    have hb1 : b = 1 := by omega
    subst hb1
    have hvecOut : [a, 1] ∈ (readVectors C n S 1).getD C.output [] := by
      rw [← hgout_eq] at hjOr ⊢
      exact orReaches_readVectors C n S 1 hAO2 gout hgout_lt j [a, 1] hjOr hvec
    have hlin := (hVecLin C.output hOutLt).2 a hvecOut
    have hls : lineSingle C n isLine u.val v.val = true := hlin
    change lineSingle C n isLine u.val v.val = false at hNoLineSingle
    rw [hls] at hNoLineSingle
    cases hNoLineSingle
  have hCoreJ : IsCore G C j := by
    refine ⟨hj, ⟨hjBel, pairInput u v, hjVal⟩, ?_, u, v, hAdj, hjVal, hReadTwice⟩
    rintro ⟨⟨hn0, hbel0, _⟩, _⟩
    have hins := gateAt_two_inputs n C hAO2 j hj
    have hmem0 : opnd C j 0 ∈ (gateAt C j).inputs := by rw [hins]; simp
    apply hNoAndBelow j hj hjAnd (opnd C j 0) hmem0
    intro x hx
    apply hbel0 x
    show wireVal n C (n + (opnd C j 0 - n)) x = true
    have : n + (opnd C j 0 - n) = opnd C j 0 := by omega
    rw [this]
    exact hx
  have hCoreAnd : ∀ i < C.gates.length, IsCore G C i → (gateAt C i).op = GateOp.and := by
    intro i hi hci
    rcases gateAt_ao n C hAO2 i hi with hop | hop
    · exact hop
    · exfalso
      have hins := gateAt_two_inputs n C hAO2 i hi
      have h0 : opnd C i 0 < n + i := hAO2.2.1 i hi _ (by rw [hins]; simp)
      have h1 : opnd C i 1 < n + i := hAO2.2.1 i hi _ (by rw [hins]; simp)
      have hImpOp : ∀ b : Fin 2, IsImpOperand G C (opnd C i b) := by
        intro b
        have hltb : opnd C i b < n + i := by fin_cases b <;> assumption
        have hmemb : opnd C i b ∈ (gateAt C i).inputs := by
          rw [hins]; fin_cases b <;> simp
        have hbelw : ∀ x, wireVal n C (opnd C i b) x = true → graphFun G ∅ x = true := by
          intro x hx
          apply hci.2.1.1 x
          show wireVal n C (n + i) x = true
          rw [wireVal_gate n C i hi, hop]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          exact ⟨opnd C i b, hmemb, by simp only [hltb, ↓reduceIte]; exact hx⟩
        have hge : n ≤ opnd C i b := by
          by_contra hlt
          push Not at hlt
          have hgf := hbelw (fun x => decide (x = ⟨opnd C i b, hlt⟩))
            (by rw [wireVal_input n C _ (opnd C i b) hlt]; simp)
          rw [graphFun_single_false G ⟨opnd C i b, hlt⟩] at hgf
          cases hgf
        refine ⟨hge, ?_, fun _ => true, ?_⟩
        · intro x hx
          apply hbelw x
          have : n + (opnd C i b - n) = opnd C i b := by omega
          rwa [← this]
        · show wireVal n C (n + (opnd C i b - n)) (fun _ => true) = true
          exact wireVal_all_true n C hAO2 _ (by omega)
      exact hci.2.2.1 ⟨hImpOp 0, hImpOp 1⟩
  have hAboveBelow : ∀ k, k < C.gates.length → InCone n C j k →
      BelowF G C k ∧ (gateAt C k).op = GateOp.or := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk hic
      rw [inCone_iff n C j k hk] at hic
      rcases hic with ⟨w, hw, hnw, hwlt, hji | hic'⟩
      · have hbelw : ∀ x, wireVal n C w x = true → graphFun G ∅ x = true := by
          intro x hx
          apply hjBel x
          show wireVal n C (n + j) x = true
          have : n + j = w := by omega
          rwa [this]
        have hopk : (gateAt C k).op = GateOp.or := by
          rcases gateAt_ao n C hAO2 k hk with hand | hor
          · exfalso; exact hNoAndBelow k hk hand w hw hbelw
          · exact hor
        have hbelk : BelowF G C k := by
          by_contra hnbel
          have hins := gateAt_two_inputs n C hAO2 k hk
          rw [hins] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          have hbex : ∃ b : Fin 2, opnd C k b = w := by
            rcases hw with rfl | rfl
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
          rcases hbex with ⟨b, hbw⟩
          apply hLFP
          refine ⟨k, hk, b, hLive k hk, hopk, hnbel, ?_, fun _ => true, ?_⟩
          · intro x hx; rw [hbw] at hx; exact hbelw x hx
          · rw [hbw]; exact wireVal_all_true n C hAO2 w (by omega)
        exact ⟨hbelk, hopk⟩
      · have hprev := (ih (w - n) (by omega) (by omega) hic').1
        have hbelw : ∀ x, wireVal n C w x = true → graphFun G ∅ x = true := by
          intro x hx
          apply hprev x
          show wireVal n C (n + (w - n)) x = true
          have : n + (w - n) = w := by omega
          rwa [this]
        have hopk : (gateAt C k).op = GateOp.or := by
          rcases gateAt_ao n C hAO2 k hk with hand | hor
          · exfalso; exact hNoAndBelow k hk hand w hw hbelw
          · exact hor
        have hbelk : BelowF G C k := by
          by_contra hnbel
          have hins := gateAt_two_inputs n C hAO2 k hk
          rw [hins] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          have hbex : ∃ b : Fin 2, opnd C k b = w := by
            rcases hw with rfl | rfl
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
          rcases hbex with ⟨b, hbw⟩
          apply hLFP
          refine ⟨k, hk, b, hLive k hk, hopk, hnbel, ?_, fun _ => true, ?_⟩
          · intro x hx; rw [hbw] at hx; exact hbelw x hx
          · rw [hbw]; exact wireVal_all_true n C hAO2 w (by omega)
        exact ⟨hbelk, hopk⟩
  refine ⟨j, ?_, ?_⟩
  · unfold maximalCores gatesWhere
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr hj, hCoreJ, ?_⟩
    intro i hi hci hic
    have hor := (hAboveBelow i hi hic).2
    have hand := hCoreAnd i hi hci
    rw [hand] at hor; cases hor
  · unfold gammaE
    rw [Finset.mem_filter]
    exact ⟨SimpleGraph.mem_edgeFinset.mpr hAdj, u, v, rfl, hjVal⟩

end PEqualNP.Outside.L_meta_3652_aux

theorem PEqualNP.Outside.L_meta_3652 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone (N + N) C k) → (∀ k2 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → ∀ p1 l1 : Fin N, (p1.val, N + l1.val) ∈ (PEqualNP.ReadK.doubleReread C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))) → ∃ j ∈ PEqualNP.Core.maximalCores G C, s(Fin.castAdd N p1, Fin.natAdd N l1) ∈ PEqualNP.TopForm.gammaE G C j := PEqualNP.Outside.L_meta_3652_aux.main
