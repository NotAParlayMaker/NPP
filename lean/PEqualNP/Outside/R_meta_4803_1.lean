import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4803_1
    (hForm : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C →
      (¬∃ (i : ℕ) (j : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone n C i j) →
      ∃ (t : ℕ) (A B : Fin t → Finset (Fin n)) (L : Finset (Fin n)) (k : ℕ),
        PEqualNP.SharedBlockCost.HasOrCost n (Finset.univ.image A ∪ Finset.univ.image B) k ∧
        k + t + (t - 1) ≤ C.size ∧
        ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ((∃ i : Fin t, (∃ u ∈ A i, x u = true) ∧ ∃ v ∈ B i, x v = true) ∨ ∃ u ∈ L, x u = true))
    (hCount : ∀ (t : ℕ) (A B : Fin t → Finset (Fin 26)) (L : Finset (Fin 26)) (k : ℕ),
      PEqualNP.SharedBlockCost.HasOrCost 26 (Finset.univ.image A ∪ Finset.univ.image B) k →
      (∀ x : Fin 26 → Bool, ((∃ i : Fin t, (∃ u ∈ A i, x u = true) ∧ ∃ v ∈ B i, x v = true) ∨ ∃ u ∈ L, x u = true) ↔
        ∃ (p : Fin 13) (l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      64 ≤ k + t + (t - 1)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (¬∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 x4 x5) → (64 : ℕ) ≤ x1.size := by
  intro C hC hf hflat
  obtain ⟨t, A, B, L, k, hk, hsz, hfun⟩ := hForm 26 C hC hflat
  have h := hCount t A B L k hk (fun x => (hfun x).symm.trans (hf x))
  omega
