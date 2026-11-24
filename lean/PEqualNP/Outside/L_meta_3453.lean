import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3453

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.FactorSubst
open PEqualNP.EdgeOwnership

/-- One evaluation step. -/
abbrev step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem length_fold (gs : List Gate) (w0 : List Bool) :
    (gs.foldl step w0).length = w0.length + gs.length := by
  induction gs generalizing w0 with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem fold_input (gs : List Gate) (w0 : List Bool) (i : ℕ) (hi : i < w0.length) :
    (gs.foldl step w0).getD i false = w0.getD i false := by
  induction gs generalizing w0 with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega), List.getD_append _ _ _ _ hi]

theorem fold_gate (gs : List Gate) (w0 : List Bool)
    (hb : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w0.length + j)
    (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w0).getD (w0.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i => (gs.foldl step w0).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton gs g ih =>
    have hlen := length_fold gs w0
    have hfold : (gs ++ [g]).foldl step w0 = gs.foldl step w0 ++
        [g.op.eval (g.inputs.map fun i => (gs.foldl step w0).getD i false)] := by
      rw [List.foldl_append]; rfl
    have hb' := hb j hj
    simp only [List.length_append, List.length_singleton] at hj
    have hread : ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs.map
          (fun i => ((gs ++ [g]).foldl step w0).getD i false) =
        ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs.map
          (fun i => (gs.foldl step w0).getD i false) := by
      apply List.map_congr_left
      intro i hi
      have := hb' i hi
      rw [hfold, List.getD_append _ _ _ _ (by omega)]
    rw [hread]
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getD_append gs [g] _ j h, hfold, List.getD_append _ _ _ _ (by omega)]
      apply ih _ h
      intro k hk i hi
      apply hb k (by simp; omega) i
      rw [List.getD_append _ _ _ _ hk]
      exact hi
    · have hje : j = gs.length := by omega
      subst hje
      rw [hfold, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ le_rfl,
        hlen]
      simp

theorem gateAt_subst (C : Circuit) (n u : ℕ) (sigma : ℕ → ℕ) (r : ℕ) :
    gateAt (substReads C n u sigma) r =
      ⟨(gateAt C r).op, (gateAt C r).inputs.map fun i => if i = n + u then sigma r else i⟩ := by
  unfold gateAt substReads
  simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases C.gates[r]? <;> simp

theorem length_subst (C : Circuit) (n u : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n u sigma).gates.length = C.gates.length := by
  simp [substReads]

theorem readsBack_subst (C : Circuit) (n u : ℕ) (sigma : ℕ → ℕ) (h : ReadsBack n C)
    (hs : ∀ r, sigma r < n + u) : ReadsBack n (substReads C n u sigma) := by
  intro j hj i hi
  rw [length_subst] at hj
  rw [gateAt_subst] at hi
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hi
  have h1 := h j hj k hk
  have h2 := hs j
  split_ifs <;> omega

theorem wires_gate (n : ℕ) (C : Circuit) (h : ReadsBack n C) (x : Fin n → Bool)
    (r : ℕ) (hr : r < C.gates.length) :
    (C.wires (List.ofFn x)).getD (n + r) false =
      (gateAt C r).op.eval
        ((gateAt C r).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  have := fold_gate C.gates (List.ofFn x) (by rw [List.length_ofFn]; exact h) r hr
  rw [List.length_ofFn] at this
  exact this

theorem wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  have := length_fold C.gates (List.ofFn x)
  rw [List.length_ofFn] at this
  exact this

theorem wires_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = (List.ofFn x).getD i false :=
  fold_input C.gates (List.ofFn x) i (by simpa using hi)

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = true → g i = true)
    (hf : op.eval (l.map f) = true) : op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hf ⊢
    exact fun i hi => h i hi (hf i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hf ⊢
    obtain ⟨i, hi, hfi⟩ := hf
    exact ⟨i, hi, h i hi hfi⟩

theorem op_gateAt (C : Circuit) (h : AndOrOnly C) (r : ℕ) (hr : r < C.gates.length) :
    (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or := by
  apply h
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hr]
  exact List.getElem_mem hr

theorem subst_gate (n : ℕ) (C : Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool)
    (h : ReadsBack n C) (hs : ∀ r, sigma r < n + u) (r : ℕ) (hr : r < C.gates.length) :
    ((substReads C n u sigma).wires (List.ofFn x)).getD (n + r) false =
      (gateAt C r).op.eval ((gateAt C r).inputs.map fun i =>
        ((substReads C n u sigma).wires (List.ofFn x)).getD
          (if i = n + u then sigma r else i) false) := by
  rw [wires_gate n _ (readsBack_subst C n u sigma h hs) x r (by rw [length_subst]; exact hr),
    gateAt_subst]
  dsimp only
  rw [List.map_map]
  rfl

theorem part_a (n : ℕ) (C : Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hs : ∀ r, sigma r < n + u)
    (H : ∀ r < C.gates.length, n + u ∈ (gateAt C r).inputs →
      (C.wires (List.ofFn x)).getD (sigma r) false = true →
      (C.wires (List.ofFn x)).getD (n + u) false = true) (i : ℕ) :
    ((substReads C n u sigma).wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn x)).getD i false = true := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.lt_or_ge i n with hi | hi
    · rw [wires_input n _ x i hi, wires_input n _ x i hi]
      exact id
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hi
    rcases Nat.lt_or_ge r C.gates.length with hr | hr
    · rw [subst_gate n C u sigma x hC.2.1 hs r hr, wires_gate n C hC.2.1 x r hr]
      apply eval_mono _ (op_gateAt C hC.1 r hr)
      intro k hk hkt
      have hlt := hC.2.1 r hr k hk
      by_cases hku : k = n + u
      · rw [ite_eq_left hku] at hkt
        subst hku
        have := hs r
        exact H r hr hk (ih _ (by omega) hkt)
      · rw [ite_eq_right hku] at hkt
        exact ih k hlt hkt
    · rw [List.getD_eq_default _ _ (by rw [wires_length, length_subst]; omega)]
      intro h; cases h

theorem part_b (n : ℕ) (C : Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hs : ∀ r, sigma r < n + u)
    (H : ∀ r < C.gates.length, n + u ∈ (gateAt C r).inputs →
      (C.wires (List.ofFn x)).getD (sigma r) false =
      (C.wires (List.ofFn x)).getD (n + u) false) (i : ℕ) :
    ((substReads C n u sigma).wires (List.ofFn x)).getD i false =
      (C.wires (List.ofFn x)).getD i false := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.lt_or_ge i n with hi | hi
    · rw [wires_input n _ x i hi, wires_input n _ x i hi]
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hi
    rcases Nat.lt_or_ge r C.gates.length with hr | hr
    · rw [subst_gate n C u sigma x hC.2.1 hs r hr, wires_gate n C hC.2.1 x r hr]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hlt := hC.2.1 r hr k hk
      by_cases hku : k = n + u
      · rw [ite_eq_left hku]
        subst hku
        have := hs r
        rw [ih _ (by omega)]
        exact H r hr hk
      · rw [ite_eq_right hku]
        exact ih k hlt
    · rw [List.getD_eq_default _ _ (by rw [wires_length, length_subst]; omega),
        List.getD_eq_default _ _ (by rw [wires_length]; omega)]

end PEqualNP.Outside.L_meta_3453

theorem PEqualNP.Outside.L_meta_3453 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool), PEqualNP.TopForm.IsAO2 n C → u < C.gates.length → (∀ r : ℕ, sigma r < n + u) → ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = true → (C.wires (List.ofFn x)).getD (n + u) false = true) → ∀ i : ℕ, ((PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn x)).getD i false = true) ∧ ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = (C.wires (List.ofFn x)).getD (n + u) false) → (PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x) = C.wires (List.ofFn x)) := by
  intro n C u sigma x hC _ hs
  refine ⟨fun H i => PEqualNP.Outside.L_meta_3453.part_a n C u sigma x hC hs H i, fun H => ?_⟩
  apply List.ext_getElem
  · rw [PEqualNP.Outside.L_meta_3453.wires_length, PEqualNP.Outside.L_meta_3453.wires_length,
      PEqualNP.Outside.L_meta_3453.length_subst]
  · intro i h1 h2
    have := PEqualNP.Outside.L_meta_3453.part_b n C u sigma x hC hs H i
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
