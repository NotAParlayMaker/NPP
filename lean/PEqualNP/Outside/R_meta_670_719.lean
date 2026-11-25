import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_670_719
    (h0 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (15 : ℕ) →
      (C.gates.filter fun g => g.op.eval [Bool.false] && !g.op.eval [Bool.true]).length = (0 : ℕ) →
      ¬∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (15 : ℕ) →
      (C.gates.filter fun g => g.op.eval [Bool.false] && !g.op.eval [Bool.true]).length = (1 : ℕ) →
      ¬∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (15 : ℕ) →
      (C.gates.filter fun g => g.op.eval [Bool.false] && !g.op.eval [Bool.true]).length = (2 : ℕ) →
      ¬∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h3 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (15 : ℕ) →
      (3 : ℕ) ≤ (C.gates.filter fun g => g.op.eval [Bool.false] && !g.op.eval [Bool.true]).length →
      ¬∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  rintro ⟨C, hfan, hsize, hev⟩
  have hnot : (C.gates.filter fun g => g.op.eval [Bool.false] && !g.op.eval [Bool.true]).length = 0 ∨
      (C.gates.filter fun g => g.op.eval [Bool.false] && !g.op.eval [Bool.true]).length = 1 ∨
      (C.gates.filter fun g => g.op.eval [Bool.false] && !g.op.eval [Bool.true]).length = 2 ∨
      3 ≤ (C.gates.filter fun g => g.op.eval [Bool.false] && !g.op.eval [Bool.true]).length := by
    omega
  rcases hnot with h | h | h | h
  · exact h0 C hfan hsize h hev
  · exact h1 C hfan hsize h hev
  · exact h2 C hfan hsize h hev
  · exact h3 C hfan hsize h hev
