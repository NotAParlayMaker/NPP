import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

-- A read-two circuit may leave a finite set of incident pairs to be added at the output.
-- Each such pair costs an AND and an OR. The smaller circuit can compute a smaller function.
theorem PEqualNP.Outside.R_meta_2582_83
    (addPair : ∀ (n : ℕ) (B : Circuit) (u v : Fin n),
      IsAO2 n B → B.output < n + B.size → IsReadK n B 2 →
      ∃ D : Circuit, IsAO2 n D ∧ D.output < n + D.size ∧ IsReadK n D 2 ∧
        D.size ≤ B.size + 2 ∧
        ∀ x : Fin n → Bool, circuitFun n D x = (circuitFun n B x || (x u && x v)))
    (partialCircuit : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q^2 + q + 1 →
      (∀ l (E : Finset (Fin N)), (∀ p, p ∈ E ↔ I p l) → E.card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N + N) C →
      (∀ x, circuitFun (N + N) C x =
        decide (∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)) →
      ∃ (B : Circuit) (M : Finset (Fin N × Fin N)),
        IsAO2 (N + N) B ∧ B.output < N + N + B.size ∧ IsReadK (N + N) B 2 ∧
        B.size + 2 * M.card ≤ C.size ∧ ∀ x, circuitFun (N + N) C x =
          (circuitFun (N + N) B x || decide (∃ e ∈ M,
            x (Fin.castAdd N e.1) = true ∧ x (Fin.natAdd N e.2) = true))) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q^2 + q + 1 →
      (∀ l, (Finset.univ.filter fun p => I p l).card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N + N) C →
      (∀ x, circuitFun (N + N) C x =
        decide (∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)) →
      ∃ D : Circuit, IsAO2 (N + N) D ∧
        (∀ x, circuitFun (N + N) D x =
          decide (∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)) ∧
        D.size ≤ C.size ∧ IsReadK (N + N) D 2 := by
  classical
  intro q N I inst C hq hN points line ao computes
  have lineSize (l : Fin N) (E : Finset (Fin N)) (h : ∀ p, p ∈ E ↔ I p l) : E.card = q+1 := by
    have hE : E = Finset.univ.filter (fun p => I p l) := by
      ext p
      simpa using h p
    rw [hE, points]
  obtain ⟨B,M,hB,valid,readB,budget,spec⟩ := partialCircuit q N I C hq hN lineSize line ao computes
  let hit (M : Finset (Fin N × Fin N)) (x : Fin (N+N) → Bool) :=
    decide (∃ e ∈ M, x (Fin.castAdd N e.1) = true ∧ x (Fin.natAdd N e.2) = true)
  have fill (S : Finset (Fin N × Fin N)) : ∃ D : Circuit,
      IsAO2 (N+N) D ∧ D.output < N+N+D.size ∧ IsReadK (N+N) D 2 ∧
      D.size ≤ B.size + 2 * S.card ∧ ∀ x, circuitFun (N+N) D x = (circuitFun (N+N) B x || hit S x) := by
    induction S using Finset.induction_on with
    | empty => exact ⟨B,hB,valid,readB,by simp,by simp [hit]⟩
    | @insert e S he ih =>
      obtain ⟨D,aoD,outD,readD,sizeD,funD⟩ := ih
      obtain ⟨D',aoD',outD',readD',sizeD',funD'⟩ :=
        addPair (N+N) D (Fin.castAdd N e.1) (Fin.natAdd N e.2) aoD outD readD
      refine ⟨D',aoD',outD',readD',?_,?_⟩
      · rw [Finset.card_insert_of_notMem he]
        omega
      · intro x
        rw [funD',funD,Bool.or_assoc]
        congr 1
        apply Bool.eq_iff_iff.mpr
        simp only [hit,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Finset.mem_insert]
        aesop
  obtain ⟨D,aoD,_,readD,sizeD,funD⟩ := fill M
  exact ⟨D,aoD,fun x => (funD x).trans ((spec x).symm.trans (computes x)),sizeD.trans budget,readD⟩
