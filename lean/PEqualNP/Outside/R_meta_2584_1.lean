import Mathlib
import PEqualNP.Defs

-- Cut L-meta-2584 into two steps. hNorm: under the rectangle-free incidence hypothesis, every
-- IsAO2 circuit computing the incidence function rewires (same model, same function, no extra
-- gates) so that every edge is the cross pair of some AND gate lying in the output's OR closure
-- (the OR-of-stars normal form; the star-cover cost is the work inside this step). hRead: such a
-- gate gives the prime implicant {p, l} a proof tree reading each of its two variables once, so
-- the circuit is read-2 on it.
theorem PEqualNP.Outside.R_meta_2584_1
    (hNorm : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
          ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
        PEqualNP.TopForm.IsAO2 (P + L) C →
        (∀ z : Fin (P + L) → Bool,
          PEqualNP.MetaComplexity.circuitFun (P + L) C z =
            decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
              z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsAO2 (P + L) D ∧
          (∀ y : Fin (P + L) → Bool,
            PEqualNP.MetaComplexity.circuitFun (P + L) D y =
              decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
                y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
          D.size ≤ C.size ∧
          ∀ (p : Fin P) (l : Fin L), I p l →
            ∃ a : ℕ, a < D.gates.length ∧
              (PEqualNP.MetaComplexity.NestedCover.gateAt D a).op =
                PEqualNP.CircuitLowerBounds.GateOp.and ∧
              (∃ b : Fin 2,
                Fin.castAdd L p ∈ PEqualNP.TopForm.orIn (P + L) D
                  (PEqualNP.TopForm.opnd D a b) ∧
                Fin.natAdd P l ∈ PEqualNP.TopForm.orIn (P + L) D
                  (PEqualNP.TopForm.opnd D a (1 - b))) ∧
              PEqualNP.CleanedNonEdge.OrReaches (P + L) D D.output a)
    (hRead : ∀ (n : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : Fin n),
        (∃ a : ℕ, a < D.gates.length ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt D a).op =
            PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (∃ b : Fin 2,
            i ∈ PEqualNP.TopForm.orIn n D (PEqualNP.TopForm.opnd D a b) ∧
            j ∈ PEqualNP.TopForm.orIn n D (PEqualNP.TopForm.opnd D a (1 - b))) ∧
          PEqualNP.CleanedNonEdge.OrReaches n D D.output a) →
        PEqualNP.ReadK.readsAtMost D n
          (PEqualNP.ReadK.setList ({i, j} : Finset (Fin n))) 2 = true) :
    ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (P + L) C →
      (∀ z : Fin (P + L) → Bool,
        PEqualNP.MetaComplexity.circuitFun (P + L) C z =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (P + L) D ∧
        (∀ y : Fin (P + L) → Bool,
          PEqualNP.MetaComplexity.circuitFun (P + L) D y =
            decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
              y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
        D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 2 := by
  intro P L I _ C hnorect hao hfun
  obtain ⟨D, hDao, hDfun, hDsize, hDnorm⟩ := hNorm P L I C hnorect hao hfun
  refine ⟨D, hDao, hDfun, hDsize, ?_⟩
  intro S hS
  obtain ⟨hStrue, hSmin⟩ := hS
  have hedge : ∃ p : Fin P, ∃ l : Fin L, I p l ∧
      PEqualNP.ReadK.setInput S (Fin.castAdd L p) = true ∧
      PEqualNP.ReadK.setInput S (Fin.natAdd P l) = true := by
    have h := hDfun (PEqualNP.ReadK.setInput S)
    rw [hStrue] at h
    exact of_decide_eq_true h.symm
  obtain ⟨p, l, hI, hpS, hlS⟩ := hedge
  have hpm : Fin.castAdd L p ∈ S := of_decide_eq_true hpS
  have hlm : Fin.natAdd P l ∈ S := of_decide_eq_true hlS
  set T : Finset (Fin (P + L)) := {Fin.castAdd L p, Fin.natAdd P l} with hTdef
  have hTS : T ⊆ S := by
    intro x hx
    simp [hTdef] at hx
    rcases hx with rfl | rfl <;> assumption
  by_cases hTe : T = S
  · subst hTe
    obtain ⟨a, ha, hop, hside, hreach⟩ := hDnorm p l hI
    exact hRead (P + L) D (Fin.castAdd L p) (Fin.natAdd P l)
      ⟨a, ha, hop, hside, hreach⟩
  · have hsub : T ∈ S.ssubsets := Finset.mem_ssubsets.mpr
      ⟨hTS, fun h => hTe (Finset.Subset.antisymm hTS h)⟩
    have hfalse : PEqualNP.MetaComplexity.circuitFun (P + L) D
        (PEqualNP.ReadK.setInput T) = false := hSmin T hsub
    have htrueT : PEqualNP.MetaComplexity.circuitFun (P + L) D
        (PEqualNP.ReadK.setInput T) = true := by
      rw [hDfun]
      apply decide_eq_true_eq.mpr
      exact ⟨p, l, hI,
        by simp [PEqualNP.ReadK.setInput, hTdef],
        by simp [PEqualNP.ReadK.setInput, hTdef]⟩
    rw [htrueT] at hfalse
    exact Bool.noConfusion hfalse
