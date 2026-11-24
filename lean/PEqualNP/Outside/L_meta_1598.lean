import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1598

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem orSets_spec (n : ℕ) (gs : List Gate) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length ∧
    ∀ k < gs.length, ∀ g, g ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] ↔
      g = k ∨ ((gs.getD k ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + k ∧
          g ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g0 ih =>
    obtain ⟨hl, hs⟩ := ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize gs.foldl (PEqualNP.CleanedNonEdge.orStep n) [] = S at hl hs
    have hpre : ∀ i < gs.length,
        (PEqualNP.CleanedNonEdge.orStep n S g0).getD i [] = S.getD i [] := by
      intro i hi
      unfold PEqualNP.CleanedNonEdge.orStep
      exact List.getD_append _ _ _ _ (by omega)
    have hlast : ∀ g, g ∈ (PEqualNP.CleanedNonEdge.orStep n S g0).getD gs.length [] ↔
        g = gs.length ∨ (g0.op = GateOp.or ∧ ∃ w ∈ g0.inputs, n ≤ w ∧ w < n + gs.length ∧
          g ∈ S.getD (w - n) []) := by
      intro g
      unfold PEqualNP.CleanedNonEdge.orStep
      rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
      by_cases hop : g0.op = GateOp.or
      · simp [hop, and_assoc]
      · simp [hop]
    refine ⟨by simp [PEqualNP.CleanedNonEdge.orStep, hl], ?_⟩
    intro k hk g
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
    · rw [hpre k hk', List.getD_append _ _ _ _ hk', hs k hk' g]
      constructor
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)]⟩
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)] at h3⟩
    · rw [hlast g, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      simp only [List.getD_cons_zero]
      constructor
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)]⟩
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)] at h3⟩

theorem orReaches_def (n : ℕ) (C : Circuit) (w g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C w g ↔
      n ≤ w ∧ g ∈ (C.gates.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [] :=
  Iff.rfl

theorem orReaches_iff (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        PEqualNP.CleanedNonEdge.OrReaches n C w g) := by
  rw [orReaches_def, Nat.add_sub_cancel_left, (orSets_spec n C.gates).2 k hk g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, hw, h1, h2, h3⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, h1, h2, (orReaches_def n C w g).2 ⟨h1, h3⟩⟩
  · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
    · exact ⟨by omega, Or.inl h⟩
    · exact ⟨by omega, Or.inr ⟨hop, w, hw, h1, h2, ((orReaches_def n C w g).1 h3).2⟩⟩

lemma single (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (U : Finset (Fin n)) :
    ∀ w, val C (List.ofFn (fun k : Fin n => decide (k ∈ U))) w = true →
      (∀ g, PEqualNP.CleanedNonEdge.OrReaches n C w g →
        (gateAt C g).op = GateOp.and →
        PEqualNP.EdgeOwnership.gateVal n C g (fun k : Fin n => decide (k ∈ U)) = false) →
      ∃ i ∈ U, val C (List.ofFn (fun r : Fin n => decide (r = i))) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hz
    by_cases hw : w < n
    · let i : Fin n := ⟨w, hw⟩
      have hmem : i ∈ U := by
        change val C (List.ofFn (fun k : Fin n => decide (k ∈ U))) i.val = true at hv
        rw [val_ofFn] at hv
        exact of_decide_eq_true hv
      refine ⟨i, hmem, ?_⟩
      change val C (List.ofFn (fun r : Fin n => decide (r = i))) i.val = true
      rw [val_ofFn]
      simp
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hAO (gateAt C k) (gateAt_mem hk) with ha | ho
        · have hf := hz k ((orReaches_iff n C k hk k).2 (Or.inl rfl)) ha
          change val C (List.ofFn (fun l : Fin n => decide (l ∈ U))) (n + k) = false at hf
          rw [hf] at hv
          cases hv
        · obtain ⟨a, ha, halt, hav⟩ := (val_or (n := n) (by simp) hk ho).1 hv
          have hsub : ∀ g, PEqualNP.CleanedNonEdge.OrReaches n C a g →
              PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g := by
            intro g hg
            exact (orReaches_iff n C k hk g).2 (Or.inr ⟨ho, a, ha, hg.1, halt, hg⟩)
          obtain ⟨i, hi, hvi⟩ := ih a halt hav (fun g hg hop => hz g (hsub g hg) hop)
          exact ⟨i, hi, (val_or (n := n) (by simp) hk ho).2 ⟨a, ha, halt, hvi⟩⟩


end PEqualNP.Outside.L_meta_1598

theorem PEqualNP.Outside.L_meta_1598 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → ∀ (U : Finset (Fin n)) (w : ℕ), PEqualNP.CleanedNonEdge.wireVal n C w (fun k : Fin n => decide (k ∈ U)) = true → (∀ g : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.gateVal n C g (fun l : Fin n => decide (l ∈ U)) = false) → ∃ i ∈ U, PEqualNP.CleanedNonEdge.wireVal n C w (fun r : Fin n => decide (r = i)) = true := by
  intro n C hAO U w hv hz
  exact PEqualNP.Outside.L_meta_1598.single n C hAO U w hv hz
