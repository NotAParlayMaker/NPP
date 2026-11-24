import Mathlib
import PEqualNP.Defs

/-!
Substitution in a circuit: a wire map `σ` that fixes the inputs and copies every gate but one
transports truth (and falsity) from the copy back to the original.

The proof is a strong induction on the gate number. Two ingredients: the value of wire `n + j`
is gate `j` applied to the *final* wire values of its operands (once the operands are earlier
wires, which `ReadsBack` gives), and a value written into the wire list is never changed by
appending further gates.
-/

namespace PEqualNP.Outside.L_meta_2854_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

/-- One evaluation step: append the value of the gate to the wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w [g.op.eval (g.inputs.map fun i => w.getD i false)] i hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval
        (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false =
          g0.op.eval (g0.inputs.map fun i => w.getD i false) := getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval
        (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates :=
  List.mem_iff_getElem?.mpr ⟨j, by rw [gateAt_get C j hj, List.getElem?_eq_getElem hj]⟩

/-- The value of wire `n + j` is gate `j` applied to the final values of its inputs, provided the
gate reads only earlier wires. -/
lemma wires_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hrb : ReadsBack n C) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  have hj' : C.gates[j]? = some (gateAt C j) := by
    rw [gateAt_get C j hj, List.getElem?_eq_getElem hj]
  rw [wires_gate_ofFn C x j (gateAt C j) hj']
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [hrb j hj i hi, ↓reduceIte]

/-- Mapping the image of a list composes without introducing a function composition. -/
lemma map_comp_eq (l : List ℕ) (σ : ℕ → ℕ) (f : ℕ → Bool) :
    (l.map σ).map f = l.map fun i => f (σ i) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, ih]

/-- For an AND or OR gate, a pointwise implication between the operands' values gives an
implication between the values. -/
lemma eval_le_of_inputs {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {ins : List ℕ} {A B : ℕ → Bool} (h : ∀ i ∈ ins, A i = true → B i = true) :
    op.eval (ins.map A) = true → op.eval (ins.map B) = true := by
  rcases hop with rfl | rfl
  · intro h1
    rw [GateOp.eval, List.all_eq_true] at h1 ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact h i hi (by simpa using h1 (A i) (List.mem_map_of_mem hi))
  · intro h1
    rw [GateOp.eval, List.any_eq_true] at h1 ⊢
    obtain ⟨a, ha, hat⟩ := h1
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    exact ⟨B i, List.mem_map_of_mem hi, h i hi (by simpa using hat)⟩

end PEqualNP.Outside.L_meta_2854_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2854_aux

theorem PEqualNP.Outside.L_meta_2854 : ∀ (n : ℕ) (C C' : PEqualNP.CircuitLowerBounds.Circuit) (σ : ℕ → ℕ) (m : ℕ) (x : Fin n → Bool), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C' → (∀ i < n, σ i = i) → (∀ j < C.gates.length, n ≤ σ (n + j) ∧ σ (n + j) < n + C'.gates.length) → (∀ j < C.gates.length, j ≠ m → (PEqualNP.MetaComplexity.NestedCover.gateAt C' (σ (n + j) - n)).op = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C' (σ (n + j) - n)).inputs = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map σ) → (((C'.wires (List.ofFn x)).getD (σ (n + m)) false = true → (C.wires (List.ofFn x)).getD (n + m) false = true) → ∀ j < C.gates.length, (C'.wires (List.ofFn x)).getD (σ (n + j)) false = true → (C.wires (List.ofFn x)).getD (n + j) false = true) ∧ ((C'.wires (List.ofFn x)).getD (σ (n + m)) false = (C.wires (List.ofFn x)).getD (n + m) false → ∀ j < C.gates.length, (C'.wires (List.ofFn x)).getD (σ (n + j)) false = (C.wires (List.ofFn x)).getD (n + j) false) := by
  intro n C C' σ m x hmono hrb hrb' hfix hmap hgate
  have hmono' : ∀ j < C.gates.length,
      (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    intro j hj
    have := (hmono (gateAt C j) (gateAt_mem C j hj)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  refine ⟨?_, ?_⟩
  · intro hLe j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hc
      by_cases hjm : j = m
      · subst hjm
        exact hLe hc
      · obtain ⟨hσge, hσlt⟩ := hmap j hj
        obtain ⟨hop, hins⟩ := hgate j hj hjm
        have hk : σ (n + j) - n < C'.gates.length := by omega
        have hC := wires_gate C x j hj hrb
        have hC' := wires_gate C' x (σ (n + j) - n) hk hrb'
        rw [Nat.add_sub_cancel' hσge] at hC'
        rw [hC'] at hc
        rw [hop, hins, map_comp_eq] at hc
        rw [hC]
        refine eval_le_of_inputs (hmono' j hj) (fun i hi hAi => ?_) hc
        have hilt : i < n + j := hrb j hj i hi
        by_cases hin : i < n
        · have hσi : σ i = i := hfix i hin
          have hx : x ⟨i, hin⟩ = true := by
            rw [← wires_input C' x i hin]
            rwa [hσi] at hAi
          rw [wires_input C x i hin]
          exact hx
        · have hge : n ≤ i := Nat.le_of_not_lt hin
          have hjn : i - n < j := by omega
          have hjnlen : i - n < C.gates.length := by omega
          have h1 : (C'.wires (List.ofFn x)).getD (σ (n + (i - n))) false = true := by
            rw [Nat.add_sub_cancel' hge]
            exact hAi
          have h2 := ih (i - n) hjn hjnlen h1
          rw [Nat.add_sub_cancel' hge] at h2
          exact h2
  · intro hEq j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hjm : j = m
      · subst hjm
        exact hEq
      · obtain ⟨hσge, hσlt⟩ := hmap j hj
        obtain ⟨hop, hins⟩ := hgate j hj hjm
        have hk : σ (n + j) - n < C'.gates.length := by omega
        have hC := wires_gate C x j hj hrb
        have hC' := wires_gate C' x (σ (n + j) - n) hk hrb'
        rw [Nat.add_sub_cancel' hσge] at hC'
        rw [hC', hC, hop, hins, map_comp_eq]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hilt : i < n + j := hrb j hj i hi
        by_cases hin : i < n
        · have hσi : σ i = i := hfix i hin
          rw [hσi, wires_input C' x i hin, wires_input C x i hin]
        · have hge : n ≤ i := Nat.le_of_not_lt hin
          have hjn : i - n < j := by omega
          have hjnlen : i - n < C.gates.length := by omega
          have h1 := ih (i - n) hjn hjnlen
          rw [Nat.add_sub_cancel' hge] at h1
          exact h1
