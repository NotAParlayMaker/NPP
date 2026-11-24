import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5162_682
    (clean :
      let neg (Q : Finset (Fin 13)) :=
        List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
          List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))
      let good (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧
        (∀ p l : Fin 13, p ∈ singerLines3 l →
          C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
        ∀ Q, IsQuadrangle singerLines3 Q → C.eval (neg Q) = false
      ∀ C, good C → C.size < 64 →
        (∃ g ∈ C.gates, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) →
        ∃ D, good D ∧ D.size < C.size)
    (move :
      let neg (Q : Finset (Fin 13)) :=
        List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
          List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))
      let good (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧
        (∀ p l : Fin 13, p ∈ singerLines3 l →
          C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
        ∀ Q, IsQuadrangle singerLines3 Q → C.eval (neg Q) = false
      ∀ C, good C → C.size < 64 →
        (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        andPairs 26 C = 1 →
        ∃ D, good D ∧ D.size < C.size) :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3.size ≤ x5.size) → PEqualNP.TopForm.andPairs (26 : ℕ) x3 = (1 : ℕ) → (64 : ℕ) ≤ x3.size := by
  intro neg good C fit least single
  by_contra! small
  have noBad (g : Gate) (hg : g ∈ C.gates) :
      ¬ (g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) := by
    intro why
    obtain ⟨D,hD,hlt⟩ := clean C fit small ⟨g,hg,why⟩
    exact (Nat.not_lt_of_ge (least D hD)) hlt
  have proper (g : Gate) (hg : g ∈ C.gates) :
      g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0 := by
    have layout : Monotone2 C := fit.1
    have hlen := (layout g hg).2
    exact ⟨Nat.le_antisymm hlen (Nat.not_lt.mp (fun h => noBad g hg (Or.inl h))),
      fun h => noBad g hg (Or.inr h)⟩
  obtain ⟨D,hD,hlt⟩ := move C fit small proper single
  exact (Nat.not_lt_of_ge (least D hD)) hlt
