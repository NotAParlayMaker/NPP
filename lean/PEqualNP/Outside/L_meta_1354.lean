import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1354

open PEqualNP.CircuitLowerBounds

def phi (n M : ℕ) (i : ℕ) : ℕ := if i < n then i else if i = n then M else i - 1

def tr (n M : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi n M)⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem key (n M : ℕ) : ∀ (rest : List Gate) (w w' : List Bool),
    w'.length + rest.length ≤ M → n ≤ w'.length → w.length = w'.length + 1 →
    (∀ i, w'.getD (phi n M i) false = w.getD i false) →
    ∀ i, (run (rest.map (tr n M)) w').getD (phi n M i) false = (run rest w).getD i false := by
  intro rest
  induction rest with
  | nil => intro w w' _ _ _ h i; exact h i
  | cons g rest ih =>
    intro w w' hM hn hl h
    have hv : (tr n M g).op.eval ((tr n M g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [tr, List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => h i
    simp only [List.length_cons] at hM
    change ∀ i, (run (rest.map (tr n M))
      (w' ++ [(tr n M g).op.eval ((tr n M g).inputs.map fun i => w'.getD i false)])).getD
        (phi n M i) false =
      (run rest (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false
    rw [hv]
    refine ih _ _ (by simp; omega) (by simp; omega) (by simp; omega) ?_
    intro i
    by_cases hi : i < w.length
    · rw [List.getD_append _ _ _ _ hi, ← h i]
      by_cases h1 : i < n
      · simp only [phi, ite_eq_left h1]
        exact List.getD_append _ _ _ _ (by omega)
      · by_cases h2 : i = n
        · simp only [phi, ite_eq_right h1, ite_eq_left h2]
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
        · simp only [phi, ite_eq_right h1, ite_eq_right h2]
          exact List.getD_append _ _ _ _ (by omega)
    · have h1 : ¬ i < n := by omega
      have h2 : ¬ i = n := by omega
      simp only [phi, ite_eq_right h1, ite_eq_right h2]
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      rw [show i - 1 - w'.length = i - w.length by omega]

theorem main (n : ℕ) (gates : List Gate) :
    ∃ gates' : List Gate, gates'.map Gate.op = gates.map Gate.op ∧
      gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧
      ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length →
        Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) =
          Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  refine ⟨gates.map (tr n (n + gates.length)), ?_, ?_, ?_⟩
  · simp [List.map_map, Function.comp_def, tr]
  · simp [List.map_map, Function.comp_def, tr]
  · intro j x _
    have hk := key n (n + gates.length) gates (List.ofFn x ++ [false]) (List.ofFn x)
      (by simp) (by simp) (by simp) (by
        intro i
        by_cases h1 : i < n
        · simp only [phi, ite_eq_left h1]
          exact (List.getD_append _ _ _ _ (by simpa using h1)).symm
        · by_cases h2 : i = n
          · simp only [phi, ite_eq_right h1, ite_eq_left h2]
            rw [List.getD_eq_default _ _ (by simp), List.getD_append_right _ _ _ _ (by simp [h2])]
            simp [h2]
          · simp only [phi, ite_eq_right h1, ite_eq_right h2]
            rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]) (n + 1 + j)
    have hp : phi n (n + gates.length) (n + 1 + j) = n + j := by
      simp only [phi, ite_eq_right (show ¬ n + 1 + j < n by omega),
        ite_eq_right (show ¬ n + 1 + j = n by omega)]
      omega
    rw [hp] at hk
    exact hk

end PEqualNP.Outside.L_meta_1354

theorem PEqualNP.Outside.L_meta_1354 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  intro n gates
  exact PEqualNP.Outside.L_meta_1354.main n gates
