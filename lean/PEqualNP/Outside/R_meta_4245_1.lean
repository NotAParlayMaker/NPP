import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4245_1
    (hAnd : ∀ (x1 x2 : ℕ) (x3 : Fin x1) (x4 x5 : Fin x2) (x6 : Fin x1 → Fin x2) (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 → (∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), x7.gates[j]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x10 ∧ x10.size ≤ x7.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x7 fun (x12 : Fin x1) => if x12 = x3 then x11 x4 || x11 x5 else x11 (x6 x12))
    (hOr : ∀ (x1 x2 : ℕ) (x3 : Fin x1) (x4 x5 : Fin x2) (x6 : Fin x1 → Fin x2) (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 → (∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), x7.gates[j]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x10 ∧ x10.size ≤ x7.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x7 fun (x12 : Fin x1) => if x12 = x3 then x11 x4 || x11 x5 else x11 (x6 x12))
    (hNone : ∀ (x1 x2 : ℕ) (x3 : Fin x1) (x4 x5 : Fin x2) (x6 : Fin x1 → Fin x2) (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 → (x7.gates = []) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x10 ∧ x10.size ≤ x7.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x7 fun (x12 : Fin x1) => if x12 = x3 then x11 x4 || x11 x5 else x11 (x6 x12)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1) (x4 x5 : Fin x2) (x6 : Fin x1 → Fin x2) (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x10 ∧ x10.size ≤ x7.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x7 fun (x12 : Fin x1) => if x12 = x3 then x11 x4 || x11 x5 else x11 (x6 x12) := by
  intro x1 x2 x3 x4 x5 x6 x7 h1 h2
  cases hgm : x7.gates with
  | nil => exact hNone x1 x2 x3 x4 x5 x6 x7 h1 h2 hgm
  | cons g gs =>
    have hgmem : g ∈ x7.gates := by rw [hgm]; exact List.mem_cons_self ..
    rcases (h1 g hgmem).1 with hop | hop
    · exact hAnd x1 x2 x3 x4 x5 x6 x7 h1 h2 ⟨0, g, by simp [hgm], hop⟩
    · exact hOr x1 x2 x3 x4 x5 x6 x7 h1 h2 ⟨0, g, by simp [hgm], hop⟩
