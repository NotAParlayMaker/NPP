import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1682_639
    (geometry : let D : Finset (Fin 13) := {0, 1, 3, 9};
      let I := fun p w : Fin 13 => ∃ d ∈ D, p = w + d
      ∀ C : Circuit, Monotone2 C →
        (∀ P : Finset (Fin 13),
          (∀ v : Fin 13, v ∉ P → ∃ w : Fin 13,
            (∀ p ∈ P, ¬ I p w) ∧ I v w) →
          (¬ ∃ w : Fin 13, ∀ p ∈ P, I p w) ∧
            (¬ ∃ v : Fin 13, ∀ w : Fin 13, (∀ p ∈ P, ¬ I p w) → I v w) →
          circuitFun (13 + 13) C (fun k => decide
            ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
              ∃ w : Fin 13, k = Fin.natAdd 13 w ∧ ∀ p ∈ P, ¬ I p w)) = false) →
        ∀ x : Fin (13 + 13) → Bool,
          (∀ p w : Fin 13, I p w → x (Fin.castAdd 13 p) = true →
            x (Fin.natAdd 13 w) = false) →
          (∀ w : Fin 13, Set.ncard {p : Fin 13 | I p w ∧ x (Fin.castAdd 13 p) = true} ≤ 2) →
          (∀ p : Fin 13, Set.ncard {w : Fin 13 | I p w ∧ x (Fin.natAdd 13 w) = true} ≤ 2) →
          circuitFun (13 + 13) C x = false)
    (circuit_bound : let D : Finset (Fin 13) := {0, 1, 3, 9};
      let I := fun p w : Fin 13 => ∃ d ∈ D, p = w + d
      ∀ C : Circuit, Monotone2 C →
        (∀ p w : Fin 13, I p w → circuitFun (13 + 13) C
          (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) →
        (∀ x : Fin (13 + 13) → Bool,
          (∀ p w : Fin 13, I p w → x (Fin.castAdd 13 p) = true →
            x (Fin.natAdd 13 w) = false) →
          (∀ w : Fin 13, Set.ncard {p : Fin 13 | I p w ∧ x (Fin.castAdd 13 p) = true} ≤ 2) →
          (∀ p : Fin 13, Set.ncard {w : Fin 13 | I p w ∧ x (Fin.natAdd 13 w) = true} ≤ 2) →
          circuitFun (13 + 13) C x = false) →
        64 ≤ C.size) : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  rintro ⟨C, hmono, hsize, htrue, hfalse⟩
  have hlarge := circuit_bound C hmono htrue (geometry C hmono hfalse)
  omega
