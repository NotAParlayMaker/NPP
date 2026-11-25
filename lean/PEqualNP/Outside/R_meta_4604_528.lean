import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover PEqualNP.TopForm

-- Pairing unmatched vertices with new leaves increases the gate budget by two per added edge.
theorem PEqualNP.Outside.R_meta_4604_528
    (pad :
      let free (p l : ℕ) (S : Fin l → Finset (Fin p)) :=
        ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1
      let computes (p l : ℕ) (S : Fin l → Finset (Fin p)) (C : Circuit) :=
        IsAO2 (p+l) C ∧ ∀ x,
          circuitFun (p+l) C x = decide (∃ a b, a ∈ S b ∧ x (Fin.castAdd l a) = true ∧
            x (Fin.natAdd p b) = true)
      ∀ (p l k : ℕ) (hp : k ≤ p) (hl : k ≤ l) (S : Fin l → Finset (Fin p)) (C : Circuit),
        (∀ i : Fin k, Fin.castLE hp i ∈ S (Fin.castLE hl i)) → free p l S → computes p l S C →
        C.output < p+l+C.size → C.size+1 < (incidences S).card+k →
        let n := p+l-k
        ∃ (T : Fin n → Finset (Fin n)) (D : Circuit),
          (∀ i, i ∈ T i) ∧ free n n T ∧ computes n n T D ∧ D.size+1 < (incidences T).card+n)
    (search :
      let free (p l : ℕ) (S : Fin l → Finset (Fin p)) :=
        ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1
      let computes (p l : ℕ) (S : Fin l → Finset (Fin p)) (C : Circuit) :=
        IsAO2 (p+l) C ∧ ∀ x,
          circuitFun (p+l) C x = decide (∃ a b, a ∈ S b ∧ x (Fin.castAdd l a) = true ∧
            x (Fin.natAdd p b) = true)
      ∃ (p l k : ℕ) (hp : k ≤ p) (hl : k ≤ l) (S : Fin l → Finset (Fin p)) (C : Circuit),
        (∀ i : Fin k, Fin.castLE hp i ∈ S (Fin.castLE hl i)) ∧ free p l S ∧ computes p l S C ∧
        C.output < p+l+C.size ∧ C.size+1 < (incidences S).card+k) :
∃ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), x4 ∈ x2 x4) ∧ (∀ (x4 x5 : Fin x1), x4 ≠ x5 → (x2 x4 ∩ x2 x5).card ≤ (1 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x3 ∧ (∀ (x4 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x4 = Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x5 ∈ x2 x6 ∧ x4 (Fin.castAdd x1 x5) = Bool.true ∧ x4 (Fin.natAdd x1 x6) = Bool.true)) ∧ x3.size + (1 : ℕ) < (PEqualNP.HeptadCover.incidences x2).card + x1 := by
  obtain ⟨p,l,k,hp,hl,S,C,matched,free,computes,out,cheap⟩ := search
  obtain ⟨T,D,diag,freeD,computesD,cost⟩ := pad p l k hp hl S C matched free computes out cheap
  exact ⟨p+l-k,T,D,diag,freeD,computesD.1,computesD.2,cost⟩
