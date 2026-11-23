import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1351_aux

open PEqualNP.CircuitLowerBounds

def rho {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) : ℕ := if h : i < n then (σ ⟨i, h⟩ : ℕ) else i

theorem rho_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) : rho σ i < n := by
  simp [rho, h]

theorem rho_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {i : ℕ} (h : ¬ i < n) : rho σ i = i := by
  simp [rho, h]

def renameGate {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho σ)⟩

theorem run_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (gs : List Gate) :
    ∀ (w w' : List Bool), w.length = w'.length → n ≤ w.length →
      (∀ i, w'.getD (rho σ i) false = w.getD i false) →
      ∀ i, ((gs.map (renameGate σ)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (rho σ i) false
        = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
  induction gs with
  | nil => intro w w' _ _ h i; simpa using h i
  | cons g gs ih =>
    intro w w' hl hn h i
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [hl]
    · simp; omega
    · intro k
      have hv : (renameGate σ g).op.eval ((renameGate σ g).inputs.map fun i => w'.getD i false)
          = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [renameGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact h a
      rw [hv]
      by_cases hk : k < n
      · have h1 := rho_lt σ hk
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact h k
      · rw [rho_ge σ hk]
        by_cases hk2 : k < w.length
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          have := h k
          rwa [rho_ge σ hk] at this
        · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          simp [hl]

end PEqualNP.Outside.L_meta_1351_aux

theorem PEqualNP.Outside.L_meta_1351 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (σ : Equiv.Perm (Fin n)), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun h => h.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + j⟩ (List.ofFn (x ∘ σ)) := by
  intro n gates σ
  refine ⟨gates.map (PEqualNP.Outside.L_meta_1351_aux.renameGate σ), ?_, ?_, ?_⟩
  · simp [PEqualNP.Outside.L_meta_1351_aux.renameGate, Function.comp_def]
  · simp [PEqualNP.Outside.L_meta_1351_aux.renameGate, Function.comp_def]
  · intro j x
    have key := PEqualNP.Outside.L_meta_1351_aux.run_inv σ gates (List.ofFn (x ∘ σ)) (List.ofFn x)
      (by simp) (by simp) (by
        intro i
        by_cases hi : i < n
        · have h1 := PEqualNP.Outside.L_meta_1351_aux.rho_lt σ hi
          simp [PEqualNP.Outside.L_meta_1351_aux.rho, hi, List.getD_eq_getElem?_getD]
        · rw [PEqualNP.Outside.L_meta_1351_aux.rho_ge σ hi]
          simp [List.getD_eq_getElem?_getD, hi])
      (n + j)
    rw [PEqualNP.Outside.L_meta_1351_aux.rho_ge σ (by omega)] at key
    simpa [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires] using key
