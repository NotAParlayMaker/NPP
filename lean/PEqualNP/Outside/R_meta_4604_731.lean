import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.HeptadCover PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_4604_731
    (geometry : ∀ (m : ℕ) (D : Finset (Fin (m+1))), 0 ∈ D → (∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ d ∈ D, a ≠ b → a-b = c-d → a=c) →
    let S := fun l : Fin (m+1) => Finset.univ.filter (fun p : Fin (m+1) => p-l ∈ D)
    (∀ i, i ∈ S i) ∧ (∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1) ∧
      (incidences S).card = (m+1)*D.card)
    (boundary : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit), IsAO2 (n+n) C →
    (∀ p l, p ∈ S l → C.eval (incidenceInput {p} {l}) = true) →
    (∀ (X Y : Finset (Fin n)), (∀ p, p ∈ X ↔ ∀ l ∈ Y, p ∉ S l) →
       (∀ l, l ∈ Y ↔ ∀ p ∈ X, p ∉ S l) → C.eval (incidenceInput X Y) = false) →
    ∀ z : Fin (n+n) → Bool, circuitFun (n+n) C z =
      decide (∃ p l, p ∈ S l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true))
    (search : ∃ (m : ℕ) (D : Finset (Fin (m+1))) (C : Circuit), 0 ∈ D ∧
    (∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ d ∈ D, a ≠ b → a-b = c-d → a=c) ∧
    IsAO2 ((m+1)+(m+1)) C ∧ C.size+1 < (m+1)*D.card + (m+1) ∧
    (∀ p l : Fin (m+1), p-l ∈ D → C.eval (incidenceInput {p} {l}) = true) ∧
    ∀ X Y : Finset (Fin (m+1)), (∀ p, p ∈ X ↔ ∀ l ∈ Y, p-l ∉ D) →
      (∀ l, l ∈ Y ↔ ∀ p ∈ X, p-l ∉ D) → C.eval (incidenceInput X Y) = false) :
    ∃ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), x4 ∈ x2 x4) ∧ (∀ (x4 x5 : Fin x1), x4 ≠ x5 → (x2 x4 ∩ x2 x5).card ≤ (1 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x3 ∧ (∀ (x4 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x4 = Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x5 ∈ x2 x6 ∧ x4 (Fin.castAdd x1 x5) = Bool.true ∧ x4 (Fin.natAdd x1 x6) = Bool.true)) ∧ x3.size + (1 : ℕ) < (PEqualNP.HeptadCover.incidences x2).card + x1 := by
  obtain ⟨m,D,C,zero,sidon,model,small,positive,negative⟩ := search
  let S := fun l : Fin (m+1) => Finset.univ.filter (fun p : Fin (m+1) => p-l ∈ D)
  have mem (p l : Fin (m+1)) : p ∈ S l ↔ p-l ∈ D := by simp [S]
  obtain ⟨diag,linear,count⟩ := geometry m D zero sidon
  refine ⟨m+1,S,C,diag,linear,model,boundary (m+1) S C model ?_ ?_,?_⟩
  · exact fun p l h => positive p l ((mem p l).mp h)
  · intro X Y hX hY
    apply negative X Y
    · simpa only [mem] using hX
    · simpa only [mem] using hY
  · change C.size+1 < (incidences S).card+(m+1)
    rw [show (incidences S).card = _ from count]
    exact small
