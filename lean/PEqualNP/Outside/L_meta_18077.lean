import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18077

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_18077

theorem PEqualNP.Outside.L_meta_18077 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → x1.gates.head? ≠ Option.none := by
  intro x1 _ h
  intro hn
  have hg : x1.gates = [] := by
    cases e : x1.gates with
    | nil => rfl
    | cons a l => rw [e] at hn; simp at hn
  have hev : ∀ x : Fin 26 → Bool, x1.eval (List.ofFn x) = (List.ofFn x).getD x1.output false := by
    intro x
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, hg]
  -- an incident pair makes the output true, so the output is an input wire
  have h1 := (h (fun k => decide (k = 0 ∨ k = 13))).2 ⟨0, 0, Or.inl rfl, by decide, by decide⟩
  rw [hev] at h1
  have ho : x1.output < 26 := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by simp; omega)] at h1
    exact absurd h1 (by simp)
  -- that single input alone makes no incident pair
  have h2 := h (fun k => decide (k.val = x1.output))
  rw [hev, List.getD_eq_getElem _ _ (by simpa using ho)] at h2
  simp only [List.getElem_ofFn] at h2
  obtain ⟨a, b, _, ha, hb⟩ := h2.1 (by simp)
  simp only [Fin.coe_castAdd, Fin.coe_natAdd, decide_eq_true_eq] at ha hb
  omega
