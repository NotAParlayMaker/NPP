import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2854_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ext (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem pre_get (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (∀ i < w.length + j, (gs.foldl step w).getD i false = ((gs.take j).foldl step w).getD i false) ∧
    (gs.foldl step w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step w).getD i false) := by
  have hs : gs = gs.take j ++ gs[j] :: gs.drop (j+1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  obtain ⟨q, hq, hql⟩ := ext (gs.take j) w
  have hQ : ((gs.take j).foldl step w).length = w.length + j := by
    rw [hq]; simp [hql]; omega
  obtain ⟨t, ht, _⟩ := ext (gs.drop (j+1)) (step ((gs.take j).foldl step w) gs[j])
  have hf : gs.foldl step w = step ((gs.take j).foldl step w) gs[j] ++ t := by
    conv_lhs => rw [hs]
    rw [List.foldl_append, List.foldl_cons, ht]
  rw [hf]
  constructor
  · intro i hi
    rw [← hQ] at hi
    have hi2 : i < (step ((gs.take j).foldl step w) gs[j]).length := by simp [step]; omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi2]
    simp only [step]
    rw [List.getElem?_append_left hi]
  · rw [← hQ]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp [step])]
    simp only [step]
    rw [List.getElem?_append_right le_rfl]
    simp

theorem wire_val (n : ℕ) (C : Circuit) (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map
          fun i => (C.wires (List.ofFn x)).getD i false) := by
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
  have hp := pre_get C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at hp
  have hw : C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
  rw [hw, hp.2, hga]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hp.1 i (hRB j hj i (by rw [hga]; exact hi))).symm

theorem in_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = (List.ofFn x).getD i false := by
  obtain ⟨t, ht, _⟩ := ext C.gates (List.ofFn x)
  have hw : C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
  rw [hw, ht]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hi)]

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (f g : ℕ → Bool)
    (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    rintro hx _ ⟨i, hi, rfl⟩
    exact h i hi (hx _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨_, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hi hx⟩

end PEqualNP.Outside.L_meta_2854_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2854_aux in
theorem PEqualNP.Outside.L_meta_2854 : ∀ (n : ℕ) (C C' : PEqualNP.CircuitLowerBounds.Circuit) (σ : ℕ → ℕ) (m : ℕ) (x : Fin n → Bool), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C' → (∀ i < n, σ i = i) → (∀ j < C.gates.length, n ≤ σ (n + j) ∧ σ (n + j) < n + C'.gates.length) → (∀ j < C.gates.length, j ≠ m → (PEqualNP.MetaComplexity.NestedCover.gateAt C' (σ (n + j) - n)).op = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C' (σ (n + j) - n)).inputs = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map σ) → (((C'.wires (List.ofFn x)).getD (σ (n + m)) false = true → (C.wires (List.ofFn x)).getD (n + m) false = true) → ∀ j < C.gates.length, (C'.wires (List.ofFn x)).getD (σ (n + j)) false = true → (C.wires (List.ofFn x)).getD (n + j) false = true) ∧ ((C'.wires (List.ofFn x)).getD (σ (n + m)) false = (C.wires (List.ofFn x)).getD (n + m) false → ∀ j < C.gates.length, (C'.wires (List.ofFn x)).getD (σ (n + j)) false = (C.wires (List.ofFn x)).getD (n + j) false) := by
  intro n C C' σ m x hM hRB hRB' hσ hrange hcopy
  have hval' : ∀ j, j < C.gates.length → j ≠ m →
      (C'.wires (List.ofFn x)).getD (σ (n + j)) false =
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
          ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map
            fun i => (C'.wires (List.ofFn x)).getD (σ i) false) := by
    intro j hj hjm
    obtain ⟨h1, h2⟩ := hrange j hj
    obtain ⟨h3, h4⟩ := hcopy j hj hjm
    have h5 : σ (n + j) = n + (σ (n + j) - n) := by omega
    rw [h5, wire_val n C' hRB' x _ (by omega), h3, h4, List.map_map]
    rfl
  have hop : ∀ j, j < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or := by
    intro j hj
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
    rw [hga]
    simpa using (hM _ (List.getElem_mem hj)).1
  constructor
  · intro hm
    have key : ∀ i, i < n + C.gates.length → (C'.wires (List.ofFn x)).getD (σ i) false = true →
        (C.wires (List.ofFn x)).getD i false = true := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi
        by_cases hin : i < n
        · rw [hσ i hin, in_val n C' x i hin, in_val n C x i hin]; exact id
        · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
          have hj : j < C.gates.length := by omega
          by_cases hjm : j = m
          · subst hjm; exact hm
          · rw [hval' j hj hjm, wire_val n C hRB x j hj]
            apply eval_mono _ (hop j hj)
            intro k hk
            have hk2 := hRB j hj k hk
            exact ih k hk2 (by omega)
    intro j hj
    exact key (n + j) (by omega)
  · intro hm
    have key : ∀ i, i < n + C.gates.length → (C'.wires (List.ofFn x)).getD (σ i) false =
        (C.wires (List.ofFn x)).getD i false := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi
        by_cases hin : i < n
        · rw [hσ i hin, in_val n C' x i hin, in_val n C x i hin]
        · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
          have hj : j < C.gates.length := by omega
          by_cases hjm : j = m
          · subst hjm; exact hm
          · rw [hval' j hj hjm, wire_val n C hRB x j hj]
            congr 1
            apply List.map_congr_left
            intro k hk
            have hk2 := hRB j hj k hk
            exact ih k hk2 (by omega)
    intro j hj
    exact key (n + j) (by omega)
