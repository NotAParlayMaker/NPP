import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18292_aux

open PEqualNP.CircuitLowerBounds

open Classical in
noncomputable def fix (m : ℕ) (g : Gate) : Gate :=
  if g.op = GateOp.or then ⟨GateOp.or, g.inputs.filter (fun i => decide (i < m))⟩
  else if g.inputs.all (fun i => decide (i < m)) then g else ⟨GateOp.or, []⟩

noncomputable def fixL : ℕ → List Gate → List Gate
  | _, [] => []
  | m, g :: gs => fix m g :: fixL (m + 1) gs

theorem fixL_len (m : ℕ) (gs : List Gate) : (fixL m gs).length = gs.length := by
  induction gs generalizing m with
  | nil => rfl
  | cons g gs ih => simp [fixL, ih]

theorem fixL_get (m : ℕ) (gs : List Gate) (j : ℕ) :
    (fixL m gs)[j]? = (gs[j]?).map (fix (m + j)) := by
  induction gs generalizing m j with
  | nil => simp [fixL]
  | cons g gs ih =>
    cases j with
    | zero => simp [fixL]
    | succ j => simp only [fixL, List.getElem?_cons_succ, ih]; congr 2; omega

theorem fix_lt (m : ℕ) (g : Gate) : ∀ i ∈ (fix m g).inputs, i < m := by
  intro i hi
  unfold fix at hi
  split_ifs at hi with h1 h2
  · simp at hi; exact hi.2
  · simp at h2; exact h2 i hi
  · simp at hi

theorem fix_mono (m : ℕ) (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (fix m g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (fix m g).inputs.length ≤ 2 := by
  unfold fix
  split_ifs with h1 h2
  · refine ⟨by simp, le_trans (List.length_filter_le _ _) hg.2⟩
  · exact hg
  · simp

theorem any_filt (f : ℕ → Bool) (m : ℕ) (hf : ∀ i, m ≤ i → f i = false) (l : List ℕ) :
    ((l.filter (fun i => decide (i < m))).map f).any id = (l.map f).any id := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : i < m
    · simp [List.filter_cons, hi, ih]
    · simp [List.filter_cons, hi, ih, hf i (by omega)]

theorem all_bad (f : ℕ → Bool) (m : ℕ) (hf : ∀ i, m ≤ i → f i = false) (l : List ℕ)
    (h : ¬ (l.all (fun i => decide (i < m)) = true)) : (l.map f).all id = false := by
  induction l with
  | nil => simp at h
  | cons i l ih =>
    by_cases hi : i < m
    · simp [hi] at h
      simp [ih (by simpa using h)]
    · simp [hf i (by omega)]

theorem fix_eval (w : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (fix w.length g).op.eval ((fix w.length g).inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hf : ∀ i, w.length ≤ i → w.getD i false = false := fun i h => List.getD_eq_default _ _ h
  unfold fix
  split_ifs with h1 h2
  · rw [h1]
    exact any_filt _ _ hf _
  · rfl
  · rcases hg with hg | hg
    · rw [hg]
      show false = (g.inputs.map fun i => w.getD i false).all id
      rw [all_bad _ _ hf _ h2]
    · exact absurd hg h1

theorem fold_eq (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (w : List Bool) :
    (fixL w.length gs).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
      = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [fixL, List.foldl_cons]
    rw [fix_eval w g (hg g (by simp))]
    have := ih (fun g' h' => hg g' (by simp [h'])) (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [List.length_append, List.length_singleton] at this
    exact this

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

end PEqualNP.Outside.L_meta_18292_aux

open PEqualNP.Outside.L_meta_18292_aux in
theorem PEqualNP.Outside.L_meta_18292 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 x5 : Fin (x1 + x2.size)), ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x6 ∧ x6.size = x2.size + (1 : ℕ) ∧ ∀ (x7 : List Bool), x7.length = x1 → x6.eval x7 = ((x2.wires x7).getD (↑x4) Bool.false || (x2.wires x7).getD (↑x5) Bool.false) := by
  intro n C hC a b
  have hAO : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  have hs : C.size = C.gates.length := rfl
  refine ⟨⟨fixL n C.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a.val, b.val]⟩], n + C.size⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
      rw [fixL_get] at hj
      cases h : C.gates[j]? with
      | none => rw [h] at hj; simp at hj
      | some g0 =>
        rw [h] at hj
        simp at hj
        subst hj
        exact fix_mono _ _ (hC g0 (List.mem_of_getElem? h))
    · simp
  · intro j hj i hi
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    simp only [List.length_append, List.length_singleton, fixL_len] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [List.getD_append _ _ _ _ (by rw [fixL_len]; exact hj)] at hi
      rw [List.getD_eq_getElem?_getD, fixL_get] at hi
      cases h : C.gates[j]? with
      | none => rw [h] at hi; simp at hi
      | some g0 =>
        rw [h] at hi
        simp only [Option.map_some, Option.getD_some] at hi
        exact fix_lt _ _ i hi
    · subst hj
      rw [List.getD_append_right _ _ _ _ (by rw [fixL_len])] at hi
      simp [fixL_len] at hi
      rw [hs] at a b
      rcases hi with rfl | rfl <;> omega
  · show (fixL n C.gates ++ _).length = C.gates.length + 1
    simp [fixL_len]
  · intro x hx
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hfe := fold_eq C.gates hAO x
    rw [hx] at hfe
    rw [hfe]
    have hl := fold_len C.gates x
    rw [List.getD_append_right _ _ _ _ (by rw [hl, hs, hx])]
    simp only [hl, hx, hs, Nat.sub_self]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
