import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1684_1
    (hExtract : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ p w : Fin 13,
        (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) →
        PEqualNP.MetaComplexity.circuitFun (13 + 13) C
          (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) →
      (∀ P : Finset (Fin 13),
        (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13,
          (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧
          (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) →
        ((∃ w3 : Fin 13, ∀ p3 ∈ P,
            (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨
          (∃ v4 : Fin 13, ∀ w4 : Fin 13,
            (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) →
            (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) →
        PEqualNP.MetaComplexity.circuitFun (13 + 13) C
          (fun kk : Fin (13 + 13) => decide
            ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
              (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
                (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) →
      ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ),
        gates.length + 25 ≤ C.size ∧
        (∀ g ∈ gates,
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        (∀ w : Fin 13, ∀ x : Fin 13 → Bool,
          (∀ i j k : Fin 13, x i = true → x j = true → x k = true →
            i = j ∨ j = k ∨ i = k) →
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
            decide (∃ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)),
              x v = true)))
    (hStarLower : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate)
      (out : Fin 13 → ℕ),
      (∀ g ∈ gates,
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ (w : Fin 13) (x : Fin 13 → Bool),
        (∀ i j k : Fin 13, x i = true → x j = true → x k = true →
          i = j ∨ j = k ∨ i = k) →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
          decide (∃ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)),
            x v = true)) → 39 ≤ gates.length) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧
      (∀ p w : Fin 13,
        (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) →
        PEqualNP.MetaComplexity.circuitFun (13 + 13) C
          (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
      (∀ P : Finset (Fin 13),
        (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13,
          (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧
          (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) →
        ((∃ w3 : Fin 13, ∀ p3 ∈ P,
            (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨
          (∃ v4 : Fin 13, ∀ w4 : Fin 13,
            (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) →
            (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) →
        PEqualNP.MetaComplexity.circuitFun (13 + 13) C
          (fun kk : Fin (13 + 13) => decide
            ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
              (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
                (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  rintro ⟨C, hMono, hSize, hIncident, hFalse⟩
  obtain ⟨gates, out, hCost, hGates, hStars⟩ := hExtract C hMono hIncident hFalse
  have h39 := hStarLower gates out hGates hStars
  omega
