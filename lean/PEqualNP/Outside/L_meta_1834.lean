import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1834

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

def gstep {α : Type} (f : List α → Gate → α) (W : List α) (g : Gate) : List α := W ++ [f W g]

def fv (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def fd (d : List ℕ) (g : Gate) : ℕ := g.lineDegree d

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl (gstep fv) x := rfl

theorem ld_eq (C : Circuit) (n : ℕ) (M : Finset ℕ) :
    C.lineDegrees n M =
      C.gates.foldl (gstep fd) ((List.range n).map fun i => if i ∈ M then 1 else 0) := rfl

theorem getD_snoc {α : Type} (W : List α) (v d : α) (i : ℕ) :
    (W ++ [v]).getD i d = if i = W.length then v else W.getD i d := by
  split_ifs with h
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rcases lt_or_gt_of_ne h with h1 | h1
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem gstep_len {α : Type} (f : List α → Gate → α) (W : List α) (g : Gate) :
    (gstep f W g).length = W.length + 1 := by
  simp [gstep]

theorem gstep_lt {α : Type} (f : List α → Gate → α) (d : α) (W : List α) (g : Gate) (i : ℕ)
    (hi : i < W.length) : (gstep f W g).getD i d = W.getD i d := by
  have hne : i ≠ W.length := by omega
  unfold gstep
  rw [getD_snoc]
  split_ifs with h
  · exact absurd h hne
  · rfl

theorem gstep_eq {α : Type} (f : List α → Gate → α) (d : α) (W : List α) (g : Gate) :
    (gstep f W g).getD W.length d = f W g := by
  unfold gstep
  rw [getD_snoc]
  simp

theorem gfold_len {α : Type} (f : List α → Gate → α) : ∀ (gs : List Gate) (W : List α),
    (gs.foldl (gstep f) W).length = W.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro W; simp
  | cons g gs ih =>
    intro W
    rw [List.foldl_cons, ih, gstep_len, List.length_cons]
    omega

theorem gfold_lt {α : Type} (f : List α → Gate → α) (d : α) :
    ∀ (gs : List Gate) (W : List α) (i : ℕ), i < W.length →
      (gs.foldl (gstep f) W).getD i d = W.getD i d := by
  intro gs
  induction gs with
  | nil => intro W i _; rfl
  | cons g gs ih =>
    intro W i hi
    have h1 : i < (gstep f W g).length := by rw [gstep_len]; omega
    rw [List.foldl_cons, ih (gstep f W g) i h1, gstep_lt f d W g i hi]

theorem gfold_ge {α : Type} (f : List α → Gate → α) (d : α) (gs : List Gate) (W : List α)
    (i : ℕ) (h : W.length + gs.length ≤ i) : (gs.foldl (gstep f) W).getD i d = d := by
  have h1 : (gs.foldl (gstep f) W).length ≤ i := by rw [gfold_len]; exact h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]
  rfl

theorem gfold_gate {α : Type} (f : List α → Gate → α) (d : α)
    (hf : ∀ (g : Gate) (W W' : List α), (∀ i ∈ g.inputs, W.getD i d = W'.getD i d) →
      f W g = f W' g) :
    ∀ (gs : List Gate) (W : List α) (j : ℕ) (hj : j < gs.length),
      (∀ i ∈ (gs[j]).inputs, i < W.length + j) →
      (gs.foldl (gstep f) W).getD (W.length + j) d = f (gs.foldl (gstep f) W) gs[j] := by
  intro gs
  induction gs with
  | nil => intro W j hj; simp at hj
  | cons g gs ih =>
    intro W j hj hb
    rw [List.foldl_cons]
    have hlen : (gstep f W g).length = W.length + 1 := gstep_len f W g
    cases j with
    | zero =>
      have h0 : W.length < (gstep f W g).length := by omega
      have h1 : (gs.foldl (gstep f) (gstep f W g)).getD (W.length + 0) d =
          (gstep f W g).getD W.length d := by
        rw [Nat.add_zero]
        exact gfold_lt f d gs (gstep f W g) W.length h0
      rw [h1, gstep_eq]
      show f W g = f (gs.foldl (gstep f) (gstep f W g)) g
      apply hf
      intro i hi
      have hi' : i < W.length := by
        have := hb i hi
        omega
      have hi2 : i < (gstep f W g).length := by omega
      rw [gfold_lt f d gs (gstep f W g) i hi2, gstep_lt f d W g i hi']
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have hb' : ∀ i ∈ (gs[j]).inputs, i < (gstep f W g).length + j := by
        intro i hi
        have := hb i hi
        omega
      have := ih (gstep f W g) j hj' hb'
      rw [hlen] at this
      have e : W.length + (j + 1) = W.length + 1 + j := by omega
      rw [e]
      exact this

theorem hfv : ∀ (g : Gate) (W W' : List Bool),
    (∀ i ∈ g.inputs, W.getD i false = W'.getD i false) → fv W g = fv W' g := by
  intro g W W' h
  unfold fv
  congr 1
  exact List.map_congr_left h

theorem hfd : ∀ (g : Gate) (W W' : List ℕ),
    (∀ i ∈ g.inputs, W.getD i 0 = W'.getD i 0) → fd W g = fd W' g := by
  intro g W W' h
  unfold fd Gate.lineDegree
  rw [List.map_congr_left h]

theorem gateAt_lt (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem val_gate (n : ℕ) (C : Circuit) (hR : ReadsBack n C) (x : List Bool) (hx : x.length = n)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have h := gfold_gate fv false hfv C.gates x j hj (by
    rw [hx, ← gateAt_lt C j hj]
    exact hR j hj)
  rw [hx, ← gateAt_lt C j hj] at h
  exact h

theorem val_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  gfold_lt fv false C.gates x i hi

theorem val_ge (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    (C.wires x).getD i false = false :=
  gfold_ge fv false C.gates x i hi

theorem init_len (n : ℕ) (M : Finset ℕ) :
    ((List.range n).map fun i => if i ∈ M then 1 else 0).length = n := by simp

theorem deg_gate (n : ℕ) (C : Circuit) (hR : ReadsBack n C) (M : Finset ℕ)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.lineDegrees n M).getD (n + j) 0 = (gateAt C j).lineDegree (C.lineDegrees n M) := by
  have h := gfold_gate fd 0 hfd C.gates ((List.range n).map fun i => if i ∈ M then 1 else 0) j hj
    (by
      rw [init_len, ← gateAt_lt C j hj]
      exact hR j hj)
  rw [init_len, ← gateAt_lt C j hj] at h
  exact h

theorem deg_input (n : ℕ) (C : Circuit) (M : Finset ℕ) (i : ℕ) (hi : i < n) :
    (C.lineDegrees n M).getD i 0 = if i ∈ M then 1 else 0 := by
  have h := gfold_lt fd 0 C.gates ((List.range n).map fun i => if i ∈ M then 1 else 0) i
    (by rw [init_len]; exact hi)
  rw [ld_eq, h, List.getD_eq_getElem?_getD]
  simp [hi]

theorem deg_ge (n : ℕ) (C : Circuit) (M : Finset ℕ) (i : ℕ) (hi : n + C.gates.length ≤ i) :
    (C.lineDegrees n M).getD i 0 = 0 :=
  gfold_ge fd 0 C.gates _ i (by rw [init_len]; exact hi)

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) : (l.map f).sum = 0 ↔ ∀ i ∈ l, f i = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.forall_mem_cons]
    rw [← ih]
    omega

theorem max_zero (f : ℕ → ℕ) (l : List ℕ) : (l.map f).foldr max 0 = 0 ↔ ∀ i ∈ l, f i = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, List.forall_mem_cons]
    rw [← ih]
    omega

theorem ld_zero (g : Gate) (d : List ℕ) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    g.lineDegree d = 0 ↔ ∀ i ∈ g.inputs, d.getD i 0 = 0 := by
  unfold Gate.lineDegree
  rcases hop with h | h
  · split_ifs
    exact sum_zero _ _
  · split_ifs with h'
    · exact absurd (h.symm.trans h') (fun hh => by cases hh)
    · exact max_zero _ _

theorem mem_le_sum (l : List ℕ) (f : ℕ → ℕ) (c : ℕ) (hc : c ∈ l) : f c ≤ (l.map f).sum := by
  induction l with
  | nil => cases hc
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hc with rfl | h
    · exact Nat.le_add_right _ _
    · exact le_trans (ih h) (Nat.le_add_left _ _)

theorem mem_le_max (l : List ℕ) (f : ℕ → ℕ) (c : ℕ) (hc : c ∈ l) :
    f c ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => cases hc
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 hc with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem le_ldeg (g : Gate) (d : List ℕ) (c : ℕ) (hc : c ∈ g.inputs) :
    d.getD c 0 ≤ g.lineDegree d := by
  unfold Gate.lineDegree
  split_ifs
  · exact mem_le_sum g.inputs (fun i => d.getD i 0) c hc
  · exact mem_le_max g.inputs (fun i => d.getD i 0) c hc

theorem sum_mono (l : List ℕ) (f f' : ℕ → ℕ) (H : ∀ i ∈ l, f i ≤ f' i) :
    (l.map f).sum ≤ (l.map f').sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (H a (by simp)) (ih (fun i hi => H i (by simp [hi])))

theorem max_mono (l : List ℕ) (f f' : ℕ → ℕ) (H : ∀ i ∈ l, f i ≤ f' i) :
    (l.map f).foldr max 0 ≤ (l.map f').foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le_max (H a (by simp)) (ih (fun i hi => H i (by simp [hi])))

theorem ldeg_mono (g : Gate) (d d' : List ℕ) (H : ∀ i ∈ g.inputs, d.getD i 0 ≤ d'.getD i 0) :
    g.lineDegree d ≤ g.lineDegree d' := by
  unfold Gate.lineDegree
  split_ifs
  · exact sum_mono _ _ _ H
  · exact max_mono _ _ _ H

theorem or_cc (f : ℕ → Bool) (c : ℕ) :
    (Gate.mk GateOp.or [c, c]).op.eval ((Gate.mk GateOp.or [c, c]).inputs.map f) = f c := by
  simp [GateOp.eval]

theorem and_ab (g : Gate) (f : ℕ → Bool) (a b : ℕ) (hop : g.op = GateOp.and)
    (hab : g.inputs = [a, b]) : g.op.eval (g.inputs.map f) = (f a && f b) := by
  rw [hop, hab]
  simp [GateOp.eval]

theorem or_ab (g : Gate) (f : ℕ → Bool) (a b : ℕ) (hop : g.op = GateOp.or)
    (hab : g.inputs = [a, b]) : g.op.eval (g.inputs.map f) = (f a || f b) := by
  rw [hop, hab]
  simp [GateOp.eval]

def Fan2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_lt C j hj]
  exact List.getElem_mem hj

theorem sel_mem (g : Gate) (h2 : g.inputs.length = 2) (s : Fin 2) :
    g.inputs.getD s.val 0 ∈ g.inputs := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
  rw [hab]
  fin_cases s <;> simp

def Mixed (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧
    ¬ ((∃ i ∈ (gateAt C j).inputs,
        (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨
      (∀ h ∈ (gateAt C j).inputs, (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0))

noncomputable def vg (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (j : ℕ) : Gate :=
  @ite Gate (Mixed N C j) (Classical.propDecidable _)
    (Gate.mk GateOp.or [(gateAt C j).inputs.getD (sg j).val 0,
      (gateAt C j).inputs.getD (sg j).val 0])
    (gateAt C j)

noncomputable def View (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) : Circuit :=
  Circuit.mk (List.ofFn (fun j : Fin C.gates.length => vg N C sg j.val)) C.output

theorem view_len (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) :
    (View N C sg).gates.length = C.gates.length := by
  simp [View]

theorem view_gateAt (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (View N C sg) j = vg N C sg j := by
  simp [gateAt, View, List.getD_eq_getElem?_getD, hj]

theorem vg_mixed (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (j : ℕ) (hm : Mixed N C j) :
    vg N C sg j = Gate.mk GateOp.or [(gateAt C j).inputs.getD (sg j).val 0,
      (gateAt C j).inputs.getD (sg j).val 0] := by
  unfold vg
  split_ifs
  rfl

theorem vg_plain (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (j : ℕ) (hm : ¬ Mixed N C j) :
    vg N C sg j = gateAt C j := by
  unfold vg
  split_ifs
  rfl

theorem view_fan2 (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (hF : Fan2 C) : Fan2 (View N C sg) := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < C.gates.length := by rw [← view_len N C sg]; exact hk
  rw [← gateAt_lt (View N C sg) k hk, view_gateAt N C sg k hk']
  by_cases hm : Mixed N C k
  · rw [vg_mixed N C sg k hm]
    exact ⟨Or.inr rfl, rfl⟩
  · rw [vg_plain N C sg k hm]
    exact hF _ (gateAt_mem C k hk')

theorem view_rb (N n : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (hF : Fan2 C) (hR : ReadsBack n C) :
    ReadsBack n (View N C sg) := by
  intro j hj i hi
  rw [view_len] at hj
  rw [view_gateAt N C sg j hj] at hi
  by_cases hm : Mixed N C j
  · rw [vg_mixed N C sg j hm] at hi
    have hic : i = (gateAt C j).inputs.getD (sg j).val 0 := by simpa using hi
    rw [hic]
    exact hR j hj _ (sel_mem _ (hF _ (gateAt_mem C j hj)).2 _)
  · rw [vg_plain N C sg j hm] at hi
    exact hR j hj i hi

theorem view_deg_le (N : ℕ) (C : Circuit) (hF : Fan2 C) (hR : ReadsBack (N + N) C)
    (sg : ℕ → Fin 2) (M : Finset ℕ) :
    ∀ w, ((View N C sg).lineDegrees (N + N) M).getD w 0 ≤ (C.lineDegrees (N + N) M).getD w 0 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w (N + N) with h | h
    · rw [deg_input _ _ _ _ h, deg_input _ _ _ _ h]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      rcases Nat.lt_or_ge j C.gates.length with hj | hj
      · have hjV : j < (View N C sg).gates.length := by rw [view_len]; exact hj
        rw [deg_gate _ _ (view_rb N _ C sg hF hR) M j hjV, deg_gate _ _ hR M j hj,
          view_gateAt N C sg j hj]
        by_cases hm : Mixed N C j
        · rw [vg_mixed N C sg j hm]
          have hc := sel_mem (gateAt C j) (hF _ (gateAt_mem C j hj)).2 (sg j)
          have hlt := hR j hj _ hc
          have e1 : Gate.lineDegree ⟨GateOp.or, [(gateAt C j).inputs.getD (sg j).val 0,
              (gateAt C j).inputs.getD (sg j).val 0]⟩ ((View N C sg).lineDegrees (N + N) M) =
              ((View N C sg).lineDegrees (N + N) M).getD
                ((gateAt C j).inputs.getD (sg j).val 0) 0 := by
            simp [Gate.lineDegree]
          rw [e1]
          exact le_trans (ih _ hlt) (le_ldeg _ _ _ hc)
        · rw [vg_plain N C sg j hm]
          exact ldeg_mono _ _ _ (fun i hi => ih i (hR j hj i hi))
      · rw [deg_ge _ _ _ _ (by rw [view_len]; omega), deg_ge _ _ _ _ (by omega)]

theorem pos_deg (N : ℕ) (D : Circuit) (hF : Fan2 D) (hR : ReadsBack (N + N) D) :
    ∀ w, w < N + N + D.gates.length →
      0 < (D.lineDegrees (N + N) (Finset.range N)).getD w 0 +
        (D.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    rcases Nat.lt_or_ge w (N + N) with h | h
    · rw [deg_input _ _ _ _ h, deg_input _ _ _ _ h]
      by_cases hN : w < N
      · have h1 : w ∈ Finset.range N := Finset.mem_range.mpr hN
        simp [h1]
      · have h1 : w ∈ Finset.Ico N (N + N) := Finset.mem_Ico.mpr ⟨by omega, h⟩
        simp [h1]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      have hj : j < D.gates.length := by omega
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hF _ (gateAt_mem D j hj)).2
      have ha : a ∈ (gateAt D j).inputs := by rw [hab]; simp
      have hlt := hR j hj a ha
      have hpa := ih a hlt (by omega)
      rw [deg_gate _ _ hR _ j hj, deg_gate _ _ hR _ j hj]
      have h1 := le_ldeg (gateAt D j) (D.lineDegrees (N + N) (Finset.range N)) a ha
      have h2 := le_ldeg (gateAt D j) (D.lineDegrees (N + N) (Finset.Ico N (N + N))) a ha
      omega

theorem view_up (N : ℕ) (C : Circuit) (hF : Fan2 C) (hR : ReadsBack (N + N) C)
    (sg : ℕ → Fin 2) (x : List Bool) (hx : x.length = N + N) :
    ∀ w, (C.wires x).getD w false = true → ((View N C sg).wires x).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w (N + N) with h | h
    · rw [val_input _ _ _ (by omega), val_input _ _ _ (by omega)]
      exact id
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      rcases Nat.lt_or_ge j C.gates.length with hj | hj
      · have hjV : j < (View N C sg).gates.length := by rw [view_len]; exact hj
        obtain ⟨hop, h2⟩ := hF _ (gateAt_mem C j hj)
        rw [val_gate _ _ hR x hx j hj, val_gate _ _ (view_rb N _ C sg hF hR) x hx j hjV,
          view_gateAt N C sg j hj]
        by_cases hm : Mixed N C j
        · rw [vg_mixed N C sg j hm, ev_and _ _ hm.1]
          intro hall
          have hc := sel_mem (gateAt C j) h2 (sg j)
          have hv := ih _ (hR j hj _ hc) (hall _ hc)
          rw [or_cc]
          exact hv
        · rw [vg_plain N C sg j hm]
          rcases hop with ha | ho
          · rw [ev_and _ _ ha, ev_and _ _ ha]
            intro hall i hi
            exact ih i (hR j hj i hi) (hall i hi)
          · rw [ev_or _ _ ho, ev_or _ _ ho]
            rintro ⟨i, hi, hv⟩
            exact ⟨i, hi, ih i (hR j hj i hi) hv⟩
      · rw [val_ge _ _ _ (by omega)]
        intro hh
        cases hh

def sg0 (C : Circuit) (x : List Bool) (j : ℕ) : Fin 2 :=
  if (C.wires x).getD ((gateAt C j).inputs.getD 0 0) false = true then 1 else 0

theorem view_eq_sel (N : ℕ) (C : Circuit) (hF : Fan2 C) (hR : ReadsBack (N + N) C)
    (x : List Bool) (hx : x.length = N + N) :
    ∀ w, ((View N C (sg0 C x)).wires x).getD w false = (C.wires x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w (N + N) with h | h
    · rw [val_input _ _ _ (by omega), val_input _ _ _ (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      rcases Nat.lt_or_ge j C.gates.length with hj | hj
      · have hjV : j < (View N C (sg0 C x)).gates.length := by rw [view_len]; exact hj
        obtain ⟨hop, h2⟩ := hF _ (gateAt_mem C j hj)
        rw [val_gate _ _ hR x hx j hj, val_gate _ _ (view_rb N _ C _ hF hR) x hx j hjV,
          view_gateAt N C _ j hj]
        by_cases hm : Mixed N C j
        · rw [vg_mixed N C _ j hm]
          obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
          have ha : a ∈ (gateAt C j).inputs := by rw [hab]; simp
          have hb : b ∈ (gateAt C j).inputs := by rw [hab]; simp
          have iha := ih a (hR j hj a ha)
          have ihb := ih b (hR j hj b hb)
          rw [or_cc, and_ab (gateAt C j) _ a b hm.1 hab]
          by_cases hva : (C.wires x).getD a false = true
          · have hs : sg0 C x j = 1 := by
              unfold sg0
              rw [hab]
              show (if (C.wires x).getD a false = true then (1 : Fin 2) else 0) = 1
              rw [hva]
              rfl
            have hcb : (gateAt C j).inputs.getD (sg0 C x j).val 0 = b := by
              rw [hs, hab]
              rfl
            rw [hcb]
            show ((View N C (sg0 C x)).wires x).getD b false =
              ((C.wires x).getD a false && (C.wires x).getD b false)
            rw [ihb, hva, Bool.true_and]
          · have hva' : (C.wires x).getD a false = false := by simpa using hva
            have hs : sg0 C x j = 0 := by
              unfold sg0
              rw [hab]
              show (if (C.wires x).getD a false = true then (1 : Fin 2) else 0) = 0
              rw [hva']
              rfl
            have hca : (gateAt C j).inputs.getD (sg0 C x j).val 0 = a := by
              rw [hs, hab]
              rfl
            rw [hca]
            show ((View N C (sg0 C x)).wires x).getD a false =
              ((C.wires x).getD a false && (C.wires x).getD b false)
            rw [iha, hva', Bool.false_and]
        · rw [vg_plain N C _ j hm]
          congr 1
          exact List.map_congr_left (fun i hi => ih i (hR j hj i hi))
      · rw [val_ge _ _ _ (by rw [view_len]; omega), val_ge _ _ _ (by omega)]

theorem view_agree (N : ℕ) (C : Circuit) (hF : Fan2 C) (hR : ReadsBack (N + N) C)
    (sg : ℕ → Fin 2) (x : List Bool) (hx : x.length = N + N) :
    ∀ w, (C.lineDegrees (N + N) (Finset.range N)).getD w 0 = 0 →
      ((View N C sg).wires x).getD w false = (C.wires x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h0
    rcases Nat.lt_or_ge w (N + N) with h | h
    · rw [val_input _ _ _ (by omega), val_input _ _ _ (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      rcases Nat.lt_or_ge j C.gates.length with hj | hj
      · have hjV : j < (View N C sg).gates.length := by rw [view_len]; exact hj
        obtain ⟨hop, h2⟩ := hF _ (gateAt_mem C j hj)
        have hd := h0
        rw [deg_gate _ _ hR _ j hj] at hd
        have hz := (ld_zero _ _ hop).mp hd
        have hnm : ¬ Mixed N C j := fun hm => hm.2 (Or.inr hz)
        rw [val_gate _ _ hR x hx j hj, val_gate _ _ (view_rb N _ C sg hF hR) x hx j hjV,
          view_gateAt N C sg j hj, vg_plain N C sg j hnm]
        congr 1
        exact List.map_congr_left (fun i hi => ih i (hR j hj i hi) (hz i hi))
      · rw [val_ge _ _ _ (by rw [view_len]; omega), val_ge _ _ _ (by omega)]

theorem partA (N : ℕ) (C : Circuit) (hF : Fan2 C) (hR : ReadsBack (N + N) C) :
    ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∀ sg : ℕ → Fin 2, PEqualNP.MetaComplexity.circuitFun (N + N) (View N C sg) z = true := by
  intro z
  have hx : (List.ofFn z).length = N + N := by simp
  constructor
  · intro h sg
    exact view_up N C hF hR sg (List.ofFn z) hx C.output h
  · intro h
    have h1 := h (sg0 C (List.ofFn z))
    have h2 := view_eq_sel N C hF hR (List.ofFn z) hx C.output
    have h3 : ((View N C (sg0 C (List.ofFn z))).wires (List.ofFn z)).getD C.output false =
        true := h1
    rw [h2] at h3
    exact h3

theorem partB (N : ℕ) (C : Circuit) (hF : Fan2 C) (hR : ReadsBack (N + N) C) :
    ∀ sg : ℕ → Fin 2,
      ((∀ g ∈ (View N C sg).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        ReadsBack (N + N) (View N C sg)) ∧
      (∀ j < (View N C sg).gates.length, (gateAt (View N C sg) j).op = GateOp.and →
        ((∃ i ∈ (gateAt (View N C sg) j).inputs,
          ((View N C sg).lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨
        (∀ h ∈ (gateAt (View N C sg) j).inputs,
          ((View N C sg).lineDegrees (N + N) (Finset.range N)).getD h 0 = 0))) ∧
      (View N C sg).size = C.size ∧
      ∀ (z : Fin (N + N) → Bool) (w : ℕ), (C.wires (List.ofFn z)).getD w false = true →
        ((View N C sg).wires (List.ofFn z)).getD w false = true := by
  intro sg
  refine ⟨⟨view_fan2 N C sg hF, view_rb N _ C sg hF hR⟩, ?_, view_len N C sg, ?_⟩
  · intro j hj hop
    rw [view_len] at hj
    rw [view_gateAt N C sg j hj] at hop ⊢
    have hnm : ¬ Mixed N C j := by
      intro hm
      rw [vg_mixed N C sg j hm] at hop
      cases hop
    rw [vg_plain N C sg j hnm] at hop ⊢
    have hXY : (∃ i ∈ (gateAt C j).inputs,
        (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨
        (∀ h ∈ (gateAt C j).inputs, (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0) := by
      by_contra hn
      exact hnm ⟨hop, hn⟩
    rcases hXY with ⟨i, hi, h0⟩ | hY
    · refine Or.inl ⟨i, hi, ?_⟩
      have := view_deg_le N C hF hR sg (Finset.Ico N (N + N)) i
      omega
    · refine Or.inr fun h hh => ?_
      have := view_deg_le N C hF hR sg (Finset.range N) h
      have := hY h hh
      omega
  · intro z w
    exact view_up N C hF hR sg (List.ofFn z) (by simp) w

theorem partC (N : ℕ) (C : Circuit) (hF : Fan2 C) (hR : ReadsBack (N + N) C) :
    ∀ (sg : ℕ → Fin 2) (g : ℕ),
      ((View N C sg).lineDegrees (N + N) (Finset.range N)).getD g 0 = 0 →
      0 < ((View N C sg).lineDegrees (N + N) (Finset.Ico N (N + N))).getD g 0 →
      ∃ E : Finset ℕ, (∀ h ∈ E, (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0 ∧
        (Relation.ReflTransGen (fun a b : ℕ => ∃ j < (View N C sg).gates.length, b = N + N + j ∧
          a ∈ (gateAt (View N C sg) j).inputs ∧ (gateAt (View N C sg) j).op = GateOp.or ∧
          0 < (C.lineDegrees (N + N) (Finset.range N)).getD b 0 ∧
          0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD b 0) h g)) ∧
        ∀ y : Fin N → Bool,
          ((View N C sg).wires (List.ofFn (Fin.append (fun _ : Fin N => false) y))).getD g false =
            decide (∃ h ∈ E, (C.wires (List.ofFn (Fin.append (fun _ : Fin N => false) y))).getD h
              false = true) := by
  intro sg g
  have hFV := view_fan2 N C sg hF
  have hRV := view_rb N (N + N) C sg hF hR
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hP hL
    by_cases hC0 : (C.lineDegrees (N + N) (Finset.range N)).getD g 0 = 0
    · refine ⟨{g}, ?_, ?_⟩
      · intro h hh
        rw [Finset.mem_singleton] at hh
        subst hh
        exact ⟨hC0, Relation.ReflTransGen.refl⟩
      · intro y
        rw [view_agree N C hF hR sg _ (by simp) g hC0]
        simp
    · have hg1 : N + N ≤ g := by
        by_contra hlt
        have hlt' : g < N + N := by omega
        rw [deg_input _ _ _ _ hlt'] at hP hC0
        exact hC0 hP
      obtain ⟨j, rfl⟩ : ∃ j, g = N + N + j := ⟨g - (N + N), by omega⟩
      have hj : j < C.gates.length := by
        by_contra hge
        rw [deg_ge _ _ _ _ (by rw [view_len]; omega)] at hL
        exact lt_irrefl 0 hL
      have hjV : j < (View N C sg).gates.length := by rw [view_len]; exact hj
      obtain ⟨hopV, h2V⟩ := hFV _ (gateAt_mem (View N C sg) j hjV)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2V
      have ha : a ∈ (gateAt (View N C sg) j).inputs := by rw [hab]; simp
      have hb : b ∈ (gateAt (View N C sg) j).inputs := by rw [hab]; simp
      have hPg := hP
      rw [deg_gate _ _ hRV _ j hjV] at hPg
      have hzero := (ld_zero _ _ hopV).mp hPg
      have halt := hRV j hjV a ha
      have hblt := hRV j hjV b hb
      have hposa := pos_deg N (View N C sg) hFV hRV a (by omega)
      have hposb := pos_deg N (View N C sg) hFV hRV b (by omega)
      have hPa := hzero a ha
      have hPb := hzero b hb
      rcases hopV with hand | hor
      · exfalso
        have hvg := view_gateAt N C sg j hj
        have hnm : ¬ Mixed N C j := by
          intro hm
          rw [hvg, vg_mixed N C sg j hm] at hand
          cases hand
        have hsame : gateAt (View N C sg) j = gateAt C j := by
          rw [hvg, vg_plain N C sg j hnm]
        have hopC : (gateAt C j).op = GateOp.and := by rw [← hsame]; exact hand
        have hXY : (∃ i ∈ (gateAt C j).inputs,
            (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨
            (∀ h ∈ (gateAt C j).inputs,
              (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0) := by
          by_contra hn
          exact hnm ⟨hopC, hn⟩
        rcases hXY with ⟨i, hi, hi0⟩ | hY
        · have hiV : i ∈ (gateAt (View N C sg) j).inputs := by rw [hsame]; exact hi
          have h1 := view_deg_le N C hF hR sg (Finset.Ico N (N + N)) i
          have h2 := hzero i hiV
          have h3 := pos_deg N (View N C sg) hFV hRV i (by have := hRV j hjV i hiV; omega)
          omega
        · apply hC0
          rw [deg_gate _ _ hR _ j hj]
          exact (ld_zero _ _ (Or.inl hopC)).mpr hY
      · obtain ⟨Ea, hEa1, hEa2⟩ := ih a halt hPa (by omega)
        obtain ⟨Eb, hEb1, hEb2⟩ := ih b hblt hPb (by omega)
        have hLC : 0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0 :=
          lt_of_lt_of_le hL (view_deg_le N C hF hR sg _ _)
        have hPC : 0 < (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0 :=
          Nat.pos_of_ne_zero hC0
        refine ⟨Ea ∪ Eb, ?_, ?_⟩
        · intro h hh
          rcases Finset.mem_union.mp hh with hh | hh
          · exact ⟨(hEa1 h hh).1, Relation.ReflTransGen.tail (hEa1 h hh).2
              ⟨j, hjV, rfl, ha, hor, hPC, hLC⟩⟩
          · exact ⟨(hEb1 h hh).1, Relation.ReflTransGen.tail (hEb1 h hh).2
              ⟨j, hjV, rfl, hb, hor, hPC, hLC⟩⟩
        · intro y
          have hval := val_gate (N + N) (View N C sg) hRV
            (List.ofFn (Fin.append (fun _ : Fin N => false) y)) (by simp) j hjV
          rw [hval, hor, hab]
          have e : GateOp.or.eval ([a, b].map fun i =>
              ((View N C sg).wires (List.ofFn (Fin.append (fun _ : Fin N => false) y))).getD i
                false) =
              (((View N C sg).wires (List.ofFn (Fin.append (fun _ : Fin N => false) y))).getD a
                false ||
              ((View N C sg).wires (List.ofFn (Fin.append (fun _ : Fin N => false) y))).getD b
                false) := by
            simp [GateOp.eval]
          rw [e, hEa2 y, hEb2 y, Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union]
          constructor
          · rintro (⟨h, hh, hv⟩ | ⟨h, hh, hv⟩)
            · exact ⟨h, Or.inl hh, hv⟩
            · exact ⟨h, Or.inr hh, hv⟩
          · rintro ⟨h, hh | hh, hv⟩
            · exact Or.inl ⟨h, hh, hv⟩
            · exact Or.inr ⟨h, hh, hv⟩

end PEqualNP.Outside.L_meta_1834

theorem PEqualNP.Outside.L_meta_1834 : ∀ (Nlv16 : ℕ) (Clv16 : PEqualNP.CircuitLowerBounds.Circuit) (Vlv16 : (ℕ → Fin 2) → PEqualNP.CircuitLowerBounds.Circuit), ((∀ glv16x2 ∈ Clv16.gates, (glv16x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv16x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv16x2.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv16 + Nlv16) Clv16) → Vlv16 = (fun sglv16x3 : ℕ → Fin 2 => (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv16x2 : Fin Clv16.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv16x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD ilv16x1 0 = 0) ∨ (∀ hlv16x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16x3 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs.getD (sglv16x3 jlv16x2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs.getD (sglv16x3 jlv16x2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val))) Clv16.output)) → (∀ zlv16 : Fin (Nlv16 + Nlv16) → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv16 + Nlv16) Clv16 zlv16 = true ↔ ∀ sglv16 : ℕ → Fin 2, PEqualNP.MetaComplexity.circuitFun (Nlv16 + Nlv16) (Vlv16 sglv16) zlv16 = true) ∧ (∀ sglv16x1 : ℕ → Fin 2, ((∀ glv16x1 ∈ (Vlv16 sglv16x1).gates, (glv16x1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv16x1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv16x1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv16 + Nlv16) (Vlv16 sglv16x1)) ∧ (∀ jlv16 < (Vlv16 sglv16x1).gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((∃ ilv16 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).inputs, ((Vlv16 sglv16x1).lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD ilv16 0 = 0) ∨ (∀ hlv16x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).inputs, ((Vlv16 sglv16x1).lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16x2 0 = 0))) ∧ (Vlv16 sglv16x1).size = Clv16.size ∧ ∀ (zlv16x1 : Fin (Nlv16 + Nlv16) → Bool) (wlv16 : ℕ), (Clv16.wires (List.ofFn zlv16x1)).getD wlv16 false = true → ((Vlv16 sglv16x1).wires (List.ofFn zlv16x1)).getD wlv16 false = true) ∧ (∀ (sglv16x2 : ℕ → Fin 2) (glv16 : ℕ), ((Vlv16 sglv16x2).lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD glv16 0 = 0 → 0 < ((Vlv16 sglv16x2).lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD glv16 0 → ∃ Elv16 : Finset ℕ, (∀ hlv16 ∈ Elv16, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16 0 = 0 ∧ (Relation.ReflTransGen (fun alv16 blv16 : ℕ => ∃ jlv16x1 < (Vlv16 sglv16x2).gates.length, blv16 = Nlv16 + Nlv16 + jlv16x1 ∧ alv16 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x2) jlv16x1).inputs ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x2) jlv16x1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 0 < (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD blv16 0 ∧ 0 < (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD blv16 0) hlv16 glv16)) ∧ ∀ ylv16 : Fin Nlv16 → Bool, ((Vlv16 sglv16x2).wires (List.ofFn (Fin.append (fun ulv16 : Fin Nlv16 => false) ylv16))).getD glv16 false = decide (∃ hlv16x1 ∈ Elv16, (Clv16.wires (List.ofFn (Fin.append (fun ulv16x1 : Fin Nlv16 => false) ylv16))).getD hlv16x1 false = true)) := by
  intro N C V hC hV
  obtain ⟨hF, hR⟩ := hC
  have hV' : V = fun sg => PEqualNP.Outside.L_meta_1834.View N C sg := hV
  subst hV'
  exact ⟨PEqualNP.Outside.L_meta_1834.partA N C hF hR, PEqualNP.Outside.L_meta_1834.partB N C hF hR,
    PEqualNP.Outside.L_meta_1834.partC N C hF hR⟩
