import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_9475 : ¬ (∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (5 + 1) × Fin 5)), PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (5 + 1) 5) ρ ∧ (∅ : PEqualNP.ProofComplexity.Clause (Fin (5 + 1) × Fin 5)) ∈ ρ ∧ ρ.length ≤ 40) := by decide +kernel

