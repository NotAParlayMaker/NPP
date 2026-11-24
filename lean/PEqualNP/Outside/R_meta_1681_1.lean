import Mathlib
import PEqualNP.Defs

-- At order 3, every generic maximal false point set has three or four points
-- (the triangles and the quadrangles). The remaining search only has to reject
-- inputs of those two sizes.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_1681_1
    (hCard :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ (P : Finset (Fin 13)),
        (∀ (v : Fin 13), ¬ (v ∈ P) → ∃ (w2 : Fin 13),
          (∀ (pp : Fin 13), pp ∈ P → ¬ (pp - w2 ∈ D)) ∧ v - w2 ∈ D) →
        (¬ ∃ (w3 : Fin 13), ∀ (p3 : Fin 13), p3 ∈ P → p3 - w3 ∈ D) ∧
        (¬ ∃ (v4 : Fin 13), ∀ (w4 : Fin 13),
          (∀ (pp : Fin 13), pp ∈ P → ¬ (pp - w4 ∈ D)) → v4 - w4 ∈ D) →
        P.card = 3 ∨ P.card = 4)
    (hSearch :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧
        (∀ (p w : Fin 13), p - w ∈ D →
          PEqualNP.MetaComplexity.circuitFun (13 + 13) C
            (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
        (∀ (P : Finset (Fin 13)),
          (∀ (v : Fin 13), ¬ (v ∈ P) → ∃ (w2 : Fin 13),
            (∀ (pp : Fin 13), pp ∈ P → ¬ (pp - w2 ∈ D)) ∧ v - w2 ∈ D) →
          (¬ ∃ (w3 : Fin 13), ∀ (p3 : Fin 13), p3 ∈ P → p3 - w3 ∈ D) ∧
          (¬ ∃ (v4 : Fin 13), ∀ (w4 : Fin 13),
            (∀ (pp : Fin 13), pp ∈ P → ¬ (pp - w4 ∈ D)) → v4 - w4 ∈ D) →
          (P.card = 3 ∨ P.card = 4) →
          PEqualNP.MetaComplexity.circuitFun (13 + 13) C
            (fun kk : Fin (13 + 13) =>
              decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
                (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
                  (∀ pp ∈ P, ¬ (∃ dd ∈ D, pp = ww + dd))))) = false)) :
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  have inc (p w : Fin 13) : (∃ d ∈ D, p = w + d) ↔ p - w ∈ D := by
    refine ⟨?_, ?_⟩
    · intro h
      apply Exists.elim h
      intro d hd
      have hs : p - w = d := sub_eq_iff_eq_add.2 (hd.2.trans (add_comm _ _))
      rw [hs]
      exact hd.1
    · intro h
      refine ⟨p - w, h, (sub_add_cancel p w).symm.trans (add_comm _ _)⟩
  apply Exists.elim hSearch
  intro C hC
  have hmon := hC.1
  have hsz := hC.2.1
  have hinc := hC.2.2.1
  have hrej := hC.2.2.2
  refine ⟨C, hmon, hsz, ?_, ?_⟩
  · intro p w hpw
    exact hinc p w ((inc p w).1 hpw)
  · intro P hclosed hgeneric
    have hclosed' : ∀ (v : Fin 13), ¬ (v ∈ P) → ∃ (w2 : Fin 13),
        (∀ (pp : Fin 13), pp ∈ P → ¬ (pp - w2 ∈ D)) ∧ v - w2 ∈ D := by
      intro v hv
      apply Exists.elim (hclosed v hv)
      intro w2 hw2
      refine ⟨w2, ?_, (inc v w2).1 hw2.2⟩
      intro pp hpp hhit
      exact hw2.1 pp hpp ((inc pp w2).2 hhit)
    have hgeneric' :
        (¬ ∃ (w3 : Fin 13), ∀ (p3 : Fin 13), p3 ∈ P → p3 - w3 ∈ D) ∧
        (¬ ∃ (v4 : Fin 13), ∀ (w4 : Fin 13),
          (∀ (pp : Fin 13), pp ∈ P → ¬ (pp - w4 ∈ D)) → v4 - w4 ∈ D) := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hgeneric.1
        apply Exists.elim h
        intro w3 hw3
        refine ⟨w3, ?_⟩
        intro p3 hp3
        exact (inc p3 w3).2 (hw3 p3 hp3)
      · intro h
        apply hgeneric.2
        apply Exists.elim h
        intro v4 hv4
        refine ⟨v4, ?_⟩
        intro w4 hw4
        have hmiss : ∀ (pp : Fin 13), pp ∈ P → ¬ (pp - w4 ∈ D) := by
          intro pp hpp hhit
          exact hw4 pp hpp ((inc pp w4).2 hhit)
        exact (inc v4 w4).2 (hv4 w4 hmiss)
    exact hrej P hclosed' hgeneric' (hCard P hclosed' hgeneric')
