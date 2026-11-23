import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_589_aux

open PEqualNP.CircuitLowerBounds

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih, List.length_append, List.length_cons]; simp; omega

theorem foldl_pre (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
      = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
    rw [List.foldl_cons, ht, List.append_assoc]

theorem wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := foldl_len _ _

theorem getD_ext (W t : List Bool) (o : ℕ) (ht : t.length ≤ 4) :
    (W ++ t).getD (if o < W.length then o else W.length + 4) false = W.getD o false := by
  split_ifs with h
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

end PEqualNP.Outside.L_meta_589_aux

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_589_aux

theorem L_meta_589 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (i : Fin n), (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o1 false = F (Function.update x i false) ∧ (C.wires (List.ofFn x)).getD o2 false = F (Function.update x i true)) → PEqualNP.MetaComplexity.HasCircuitSize n F (s + 4) := by
  intro n s F i ⟨C, hf, hs, o1, o2, ho⟩
  set L := n + C.gates.length with hL
  let p1 := if o1 < L then o1 else L + 4
  let p2 := if o2 < L then o2 else L + 4
  refine ⟨⟨C.gates ++ [⟨GateOp.not, [i.val]⟩, ⟨GateOp.and, [L, p1]⟩, ⟨GateOp.and, [i.val, p2]⟩,
    ⟨GateOp.or, [L + 1, L + 2]⟩], L + 3⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | hg | hg | hg | hg
    · exact hf g hg
    all_goals subst hg; simp
  · simp [Circuit.size] at hs ⊢; omega
  · intro x
    have e1 := ho x
    have hlen := wires_len C (List.ofFn x)
    simp only [List.length_ofFn] at hlen
    simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil] at e1 ⊢
    set W := C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x) with hW
    have hWL : W.length = L := by rw [hW]; exact hlen
    have hi : i.val < W.length := by omega
    have hxi : W.getD i.val false = x i := by
      obtain ⟨t, ht⟩ := foldl_pre C.gates (List.ofFn x)
      rw [hW, ht, List.getD_append _ _ _ _ (by simp)]
      simp
    have q1 : ∀ t : List Bool, t.length ≤ 4 → (W ++ t).getD p1 false = F (Function.update x i false) := by
      intro t ht; have h := getD_ext W t o1 ht; rw [hWL] at h; rw [h]; exact e1.1
    have q2 : ∀ t : List Bool, t.length ≤ 4 → (W ++ t).getD p2 false = F (Function.update x i true) := by
      intro t ht; have h := getD_ext W t o2 ht; rw [hWL] at h; rw [h]; exact e1.2
    have qi : ∀ t : List Bool, (W ++ t).getD i.val false = x i := by
      intro t; rw [List.getD_append _ _ _ _ hi, hxi]
    have qL : ∀ (t : List Bool) (k : ℕ), (W ++ t).getD (L + k) false = t.getD k false := by
      intro t k; rw [List.getD_append_right _ _ _ _ (by omega)]; congr 1; omega
    simp only [List.append_assoc, List.singleton_append, List.map_cons, List.map_nil]
    have qL0 : ∀ (t : List Bool), (W ++ t).getD L false = t.getD 0 false := by
      intro t; have := qL t 0; simpa using this
    simp (disch := simp) only [q1, q2, qi, qL, qL0]
    simp [GateOp.eval]
    have hx2 : W[i.val]?.getD false = x i := by rw [← hxi]; simp
    have hu : Function.update x i (x i) = x := Function.update_eq_self i x
    cases h : x i <;> rw [h] at hu <;> simp [hx2, h, hu]
end PEqualNP.Outside
