import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6454

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def nrm (n : ℕ) (gs : List Gate) : List Gate :=
  gs.mapIdx (fun idx g => ⟨g.op, g.inputs.map (fun i => min i (n + idx))⟩)

lemma len_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma key (W : List Bool) (L : ℕ) (hL : W.length = L) (l : List ℕ) :
    (l.map (fun i => min i L)).map (fun i => W.getD i false) =
      l.map (fun i => W.getD i false) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  by_cases h : i ≤ L
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]

lemma nrm_fold (n : ℕ) (w : List Bool) (hw : w.length = n) (gs : List Gate) :
    (nrm n gs).foldl step w = gs.foldl step w := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    unfold nrm at ih ⊢
    rw [List.mapIdx_concat, List.foldl_append, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, step]
    rw [key _ _ (by rw [len_fold, hw])]

lemma pad_fold (k : ℕ) (w : List Bool) :
    (List.replicate k (⟨GateOp.or, []⟩ : Gate)).foldl step w = w ++ List.replicate k false := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    simp [step, GateOp.eval, List.replicate_succ]

lemma main (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hs : C.size ≤ m) :
    ∃ C' : Circuit, C'.size = m ∧ Monotone2 C' ∧
      (∀ (idx : Fin C'.gates.length), ∀ i ∈ (C'.gates.get idx).inputs, i ≤ n + idx.val) ∧
      ∀ w : List Bool, w.length = n → ∀ i : ℕ,
        (C'.wires w).getD i false = (C.wires w).getD i false := by
  unfold Circuit.size at hs
  refine ⟨⟨nrm n C.gates ++ List.replicate (m - C.gates.length) ⟨GateOp.or, []⟩, C.output⟩,
    ?_, ?_, ?_, ?_⟩
  · unfold Circuit.size
    simp only [nrm, List.length_append, List.length_mapIdx, List.length_replicate]
    omega
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp h
      have h0 := hM _ (List.getElem_mem hi)
      exact ⟨h0.1, by simpa using h0.2⟩
    · rw [List.eq_of_mem_replicate h]
      exact ⟨by simp, by simp⟩
  · intro idx i hi
    rw [List.get_eq_getElem] at hi
    by_cases h : idx.val < (nrm n C.gates).length
    · rw [List.getElem_append_left h] at hi
      simp only [nrm, List.getElem_mapIdx] at hi
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      exact min_le_right _ _
    · rw [List.getElem_append_right (by omega), List.getElem_replicate] at hi
      simp at hi
  · intro w hw i
    show ((nrm n C.gates ++ List.replicate (m - C.gates.length) (⟨GateOp.or, []⟩ : Gate)).foldl step
      w).getD i false = (C.gates.foldl step w).getD i false
    rw [List.foldl_append, nrm_fold n w hw, pad_fold]
    by_cases h1 : i < (C.gates.foldl step w).length
    · rw [List.getD_append _ _ _ _ h1]
    · rw [List.getD_eq_default (C.gates.foldl step w) _ (by omega)]
      by_cases h2 : i < (C.gates.foldl step w ++ List.replicate (m - C.gates.length) false).length
      · rw [List.getD_eq_getElem _ _ h2, List.getElem_append_right (by omega),
          List.getElem_replicate]
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h2)]

end PEqualNP.Outside.L_meta_6454

theorem PEqualNP.Outside.L_meta_6454 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.size = x2 ∧ PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x6.gates.length), ∀ x8 ∈ (x6.gates.get x7).inputs, x8 ≤ x1 + ↑x7) ∧ ∀ (x7 : List Bool), x7.length = x1 → ∀ (x9 : ℕ), (x6.wires x7).getD x9 Bool.false = (x3.wires x7).getD x9 Bool.false := by
  intro n m C hM hs
  exact PEqualNP.Outside.L_meta_6454.main n m C hM hs
