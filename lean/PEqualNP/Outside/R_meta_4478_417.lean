import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4478_417
    (remove :
      ∀ (m n : ℕ) (E : Finset (Fin m × Fin n)) (C : Circuit),
      let touch := fun (u : Fin (m+n)) (e : Fin m × Fin n) => Fin.castAdd n e.1=u ∨ Fin.natAdd m e.2=u
      let good := fun (B : Finset (Fin m × Fin n)) (D : Circuit) => IsAO2 (m+n) D ∧ ∀ x,circuitFun (m+n) D x=decide (∃ e∈B,x (Fin.castAdd n e.1)=true ∧ x (Fin.natAdd m e.2)=true)
      (∀ p q l k,p≠q → l≠k → ¬((p,l)∈E ∧ (p,k)∈E ∧ (q,l)∈E ∧ (q,k)∈E)) → good E C → (∀ u,(E.filter (touch u)).card≠1) → E.Nonempty →
      ∃ l : Fin n,(∃ p,(p,l)∈E) ∧ ∃ D,good (E.filter fun e => e.2≠l) D ∧ D.size+2≤C.size)
    (graph :
      ∀ (m n : ℕ) (E : Finset (Fin m × Fin n)),
      let touch := fun (u : Fin (m+n)) (e : Fin m × Fin n) => Fin.castAdd n e.1=u ∨ Fin.natAdd m e.2=u
      let cover := fun (B : Finset (Fin m × Fin n)) (T : Finset (Fin (m+n))) => ∀ e∈B, Fin.castAdd n e.1∈T ∨ Fin.natAdd m e.2∈T
      (∀ u,(E.filter (touch u)).card≠1) → ¬((∃ p : Fin m,(E.filter fun e => e.1=p).card=2) ∨ (∃ l : Fin n,2<(E.filter fun e => e.2=l).card)) → ∀ l : Fin n,(∃ p,(p,l)∈E) →
      let B := E.filter fun e => e.2≠l
      (∀ u,(B.filter (touch u)).card≠1) ∧ B.card+2=E.card ∧ ∀ S,cover B S → ∃ T,cover E T ∧ T.card≤S.card)
    (core :
      ∀ (m n : ℕ) (E : Finset (Fin m × Fin n)) (C : Circuit),
      let touch := fun (u : Fin (m+n)) (e : Fin m × Fin n) => Fin.castAdd n e.1=u ∨ Fin.natAdd m e.2=u
      let good := fun (B : Finset (Fin m × Fin n)) (D : Circuit) => IsAO2 (m+n) D ∧ ∀ x,circuitFun (m+n) D x=decide (∃ e∈B,x (Fin.castAdd n e.1)=true ∧ x (Fin.natAdd m e.2)=true)
      let cover := fun (B : Finset (Fin m × Fin n)) (T : Finset (Fin (m+n))) => ∀ e∈B, Fin.castAdd n e.1∈T ∨ Fin.natAdd m e.2∈T
      (∀ p q l k,p≠q → l≠k → ¬((p,l)∈E ∧ (p,k)∈E ∧ (q,l)∈E ∧ (q,k)∈E)) → good E C → (∀ u,(E.filter (touch u)).card≠1) → ((∃ p : Fin m,(E.filter fun e => e.1=p).card=2) ∨ (∃ l : Fin n,2<(E.filter fun e => e.2=l).card)) → ∃ T,cover E T ∧ E.card+T.card≤C.size+1)
    : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ ∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ x9 ∈ x6, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → x6 x3 x4 → (∀ (x9 : Fin (x1 + x2)), (Finset.filter (x5 x9) x3).card ≠ (1 : ℕ)) → ∃ (x10 : Finset (Fin (x1 + x2))), (∀ x11 ∈ x3, Fin.castAdd x2 x11.1 ∈ x10 ∨ Fin.natAdd x1 x11.2 ∈ x10) ∧ x3.card + x10.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro m n E C
  dsimp only
  induction k : E.card using Nat.strong_induction_on generalizing E C with
  | ind k ih =>
    intro rect ok deg
    by_cases edge : E.Nonempty
    · by_cases frontier : ((∃ p : Fin m,(E.filter fun e => e.1=p).card=2) ∨ (∃ l : Fin n,2<(E.filter fun e => e.2=l).card))
      · obtain ⟨T,t,b⟩ := core m n E C rect ok deg frontier
        exact ⟨T,t,by omega⟩
      obtain ⟨l,active,D,fits,small⟩ := remove m n E C rect ok deg edge
      obtain ⟨leaf,card,extend⟩ := graph m n E deg frontier l active
      let B := E.filter fun e => e.2≠l
      have sub : B⊆E := Finset.filter_subset _ _
      have rf : ∀ p q l k,p≠q → l≠k → ¬((p,l)∈B ∧ (p,k)∈B ∧ (q,l)∈B ∧ (q,k)∈B) := by
        intro p q l k d f bad
        exact rect p q l k d f ⟨sub bad.1,sub bad.2.1,sub bad.2.2.1,sub bad.2.2.2⟩
      change B.card+2=E.card at card
      obtain ⟨S,covers,bound⟩ := ih B.card (by omega) B D rfl rf fits leaf
      obtain ⟨T,cov,smaller⟩ := extend S covers
      exact ⟨T,cov,by omega⟩
    · have emp := Finset.not_nonempty_iff_eq_empty.mp edge
      subst E
      have zero : (∅ : Finset (Fin m × Fin n)).card=0 := rfl
      exact ⟨∅,by simp,by simp only [Finset.card_empty,Nat.add_zero];omega⟩
