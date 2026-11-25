import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7529_aux

open PEqualNP.CircuitLowerBounds

theorem keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]

theorem main (a b : ℕ) (hab : a ≠ b) (gs : List Gate) : ∀ (w1 w2 : List Bool),
    w1.length = w2.length → (∀ i, i ≠ a → w1.getD i false = w2.getD i false) →
    w1.getD b false = true →
    (∀ g ∈ gs, a ∉ g.inputs ∨ (g.op = GateOp.or ∧ (g.inputs = [a, b] ∨ g.inputs = [b, a]))) →
    ∀ i, i ≠ a →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD i false
    = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ h _ _ i hi; exact h i hi
  | cons g gs ih =>
    intro w1 w2 hl h hb hg i hi
    rw [List.foldl_cons, List.foldl_cons]
    have hb2 : w2.getD b false = true := by rw [← h b (Ne.symm hab)]; exact hb
    have hblt : b < w1.length := by
      by_contra hc
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hb
      simp at hb
    have hv : g.op.eval (g.inputs.map fun i => w1.getD i false)
        = g.op.eval (g.inputs.map fun i => w2.getD i false) := by
      rcases hg g (by simp) with h1 | ⟨h1, h2 | h2⟩
      · congr 1
        apply List.map_congr_left
        intro j hj
        exact h j (fun hc => h1 (hc ▸ hj))
      · rw [h1, h2]; simp only [List.getD_eq_getElem?_getD] at hb hb2; simp [GateOp.eval, hb, hb2]
      · rw [h1, h2]; simp only [List.getD_eq_getElem?_getD] at hb hb2; simp [GateOp.eval, hb, hb2]
    apply ih _ _ (by simp [hl]) _ _ (fun g' hg' => hg g' (by simp [hg'])) i hi
    · intro j hj
      rw [hv]
      have := h j hj
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl] at this ⊢
      split
      · exact this
      · rfl
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append, hblt] at hb ⊢
      exact hb

end PEqualNP.Outside.L_meta_7529_aux

theorem PEqualNP.Outside.L_meta_7529 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1) (x5 : Fin x2.size), x3 ≠ x4 → (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or → (x2.gates.get x5).inputs = [↑x3, ↑x4] ∨ (x2.gates.get x5).inputs = [↑x4, ↑x3] → (∀ (x9 : Fin x2.size), ↑x3 ∈ (x2.gates.get x9).inputs → x9 = x5) → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x10 : Fin x1) => Decidable.decide (x10 = x3)) = Bool.false → ∀ (x11 : Fin x1 → Bool), x11 x4 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x11 x3 Bool.true) = PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x11 x3 Bool.false) := by
  intro x1 x2 x3 x4 x5 hne hop hin huniq hfalse x11 h4
  unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
    PEqualNP.CircuitLowerBounds.Circuit.wires at *
  have hab : (x3 : ℕ) ≠ (x4 : ℕ) := fun h => hne (Fin.ext h)
  have hout : x2.output ≠ (x3 : ℕ) := by
    intro hc
    rw [hc, PEqualNP.Outside.L_meta_7529_aux.keep _ _ _ (by simp)] at hfalse
    simp [List.getD_eq_getElem?_getD] at hfalse
  apply PEqualNP.Outside.L_meta_7529_aux.main x3 x4 hab _ _ _ (by simp) _ _ _ _ hout
  · intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split
    · rename_i hlt
      have : (⟨i, hlt⟩ : Fin x1) ≠ x3 := fun hc => hi (by rw [← hc])
      simp [Function.update_of_ne this]
    · rfl
  · have : x4 ≠ x3 := Ne.symm hne
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Function.update_of_ne this, h4]
  · intro g hg
    obtain ⟨n, rfl⟩ := List.mem_iff_get.mp hg
    by_cases hm : (x3 : ℕ) ∈ (x2.gates.get n).inputs
    · right
      have := huniq n hm
      subst this
      exact ⟨hop, hin⟩
    · left; exact hm
