import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7740_aux

open PEqualNP.CircuitLowerBounds

def rg (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem step (x1 x2 : ℕ) (f : ℕ → ℕ) (hf1 : ∀ i, i < x1 → f i < x2)
    (hf2 : ∀ i, x1 ≤ i → f i = i - x1 + x2) (w w' : List Bool) (k : ℕ) (v : Bool)
    (hw : w.length = x1 + k) (hw' : w'.length = x2 + k)
    (h : ∀ i, w'.getD (f i) false = w.getD i false) (i : ℕ) :
    (w' ++ [v]).getD (f i) false = (w ++ [v]).getD i false := by
  have hi := h i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append] at hi ⊢
  by_cases c : i < x1
  · have := hf1 i c
    have a1 : f i < w'.length := by omega
    have a2 : i < w.length := by omega
    simp only [a1, a2, if_true]
    exact hi
  · have e := hf2 i (by omega)
    by_cases d : i < x1 + k
    · have a1 : f i < w'.length := by omega
      have a2 : i < w.length := by omega
      simp only [a1, a2, if_true]
      exact hi
    · have a1 : ¬ f i < w'.length := by omega
      have a2 : ¬ i < w.length := by omega
      have a3 : f i - w'.length = i - w.length := by omega
      simp only [a1, a2, if_false, a3]

theorem main (x1 x2 : ℕ) (f : ℕ → ℕ) (hf1 : ∀ i, i < x1 → f i < x2)
    (hf2 : ∀ i, x1 ≤ i → f i = i - x1 + x2) (gs : List Gate) :
    ∀ (w w' : List Bool) (k : ℕ), w.length = x1 + k → w'.length = x2 + k →
    (∀ i, w'.getD (f i) false = w.getD i false) → ∀ i,
    ((gs.map (rg f)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (f i) false
    = (gs.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
  induction gs with
  | nil => intro w w' k _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' k hw hw' h i
    simp only [List.map_cons, List.foldl_cons]
    have e : (rg f g).op.eval ((rg f g).inputs.map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h a
    rw [e]
    apply ih _ _ (k + 1)
    · simp [hw]; omega
    · simp [hw']; omega
    · exact step x1 x2 f hf1 hf2 w w' k _ hw hw' h

end PEqualNP.Outside.L_meta_7740_aux

theorem PEqualNP.Outside.L_meta_7740 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ → ℕ), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size = x4.size ∧ (∀ x8 < x1 + x4.size, x7 x8 < x2 + x6.size) ∧ ∀ (x8 : Fin x2 → Bool), ∀ x9 < x1 + x4.size, (x6.wires (List.ofFn x8)).getD (x7 x9) Bool.false = (x4.wires (List.ofFn (x8 ∘ x3))).getD x9 Bool.false := by
  intro x1 x2 x3 x4 hm
  let f : ℕ → ℕ := fun i => if h : i < x1 then (x3 ⟨i, h⟩).val else i - x1 + x2
  have hf1 : ∀ i, i < x1 → f i < x2 := by
    intro i hi
    simp only [f, hi, dif_pos]
    exact (x3 ⟨i, hi⟩).isLt
  have hf2 : ∀ i, x1 ≤ i → f i = i - x1 + x2 := by
    intro i hi
    have : ¬ i < x1 := by omega
    simp only [f, this, dif_neg, not_false_eq_true]
  refine ⟨⟨x4.gates.map (PEqualNP.Outside.L_meta_7740_aux.rg f), x4.output⟩, f, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hm g0 hg0
    simpa [PEqualNP.Outside.L_meta_7740_aux.rg] using this
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro i hi
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_map]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hi
    by_cases c : i < x1
    · have := hf1 i c
      omega
    · have := hf2 i (by omega)
      omega
  · intro x8 x9 _
    refine PEqualNP.Outside.L_meta_7740_aux.main x1 x2 f hf1 hf2 x4.gates _ _ 0 (by simp) (by simp) ?_ x9
    intro i
    by_cases c : i < x1
    · have a := hf1 i c
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, c, a, dif_pos]
      simp [f, c]
    · have e := hf2 i (by omega)
      have a : ¬ f i < x2 := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, c, a, dif_neg, not_false_eq_true]
