import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4362_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size = (14 : ℕ) → x1.output = (23 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => (if x5.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x5.inputs else x5.inputs).any fun (x6 : ℕ) => Decidable.decide (x6 = (6 : ℕ))) x1.gates = (1 : ℕ) → (∃ g ∈ x1.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (6 : ℕ) ∈ g.inputs) → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ))]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size = (14 : ℕ) → x1.output = (23 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => (if x5.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x5.inputs else x5.inputs).any fun (x6 : ℕ) => Decidable.decide (x6 = (6 : ℕ))) x1.gates = (1 : ℕ) → (∃ g ∈ x1.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ g.inputs) → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ))]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size = (14 : ℕ) → x1.output = (23 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => (if x5.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x5.inputs else x5.inputs).any fun (x6 : ℕ) => Decidable.decide (x6 = (6 : ℕ))) x1.gates = (1 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ))]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hM hsz hout hcnt
  have hpos : 0 < List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => (if x5.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x5.inputs else x5.inputs).any fun (x6 : ℕ) => Decidable.decide (x6 = (6 : ℕ))) x1.gates := by
    omega
  obtain ⟨g, hg, hpred⟩ := List.countP_pos_iff.mp hpos
  have hmem6 : (6 : ℕ) ∈ g.inputs := by
    rw [List.any_eq_true] at hpred
    obtain ⟨w, hw, hweq⟩ := hpred
    have h6 : w = 6 := of_decide_eq_true hweq
    subst h6
    split_ifs at hw
    · exact List.mem_of_mem_take hw
    · exact hw
  have hop := (hM g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hand | hor
  · exact h1 x1 hM hsz hout hcnt ⟨g, hg, hand, hmem6⟩
  · exact h2 x1 hM hsz hout hcnt ⟨g, hg, hor, hmem6⟩
