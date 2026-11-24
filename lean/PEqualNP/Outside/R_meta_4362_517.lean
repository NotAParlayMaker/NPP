import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Cut: drop the reader condition on wire 6. Any monotone circuit with 14 gates that computes the
-- edge function on the ten wires (wire 9 = vertex 0 OR vertex 6) agrees with it on 24 rows: the
-- 12 edges and the 12 maximal independent sets, with bit 9 = bit 0 OR bit 6. link is the generic
-- cube link lemma (desk step L-meta-4805, verbatim); free says every one of the 72 cubes of the
-- symmetry-broken CNF encoding for 14 gates on those 24 rows is unsatisfiable (finite, LRAT-checkable).
theorem PEqualNP.Outside.R_meta_4362_517
    (link : ∀ (n s : Nat) (g : Nat → Bool) (rows : List Nat) (C : PEqualNP.CircuitLowerBounds.Circuit),
      0 < s → (∀ r ∈ rows, r < 2 ^ n) → PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn (fun i : Fin n => r.testBit i.val)) = g r) →
      ∃ k < PEqualNP.Defs.LratEncoding.enc2CubeCount n s,
        PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 n s g rows ++
          PEqualNP.Defs.LratEncoding.enc2Cube n s k))
    (free : ∀ k < PEqualNP.Defs.LratEncoding.enc2CubeCount 10 14,
      ¬ PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 10 14
        (fun r : Nat => [515,6,12,24,529,545,578,132,264,160,832,288].contains r)
        [515,6,12,24,529,545,578,132,264,160,832,288,720,616,276,628,402,50,138,42,897,713,773,581] ++
        PEqualNP.Defs.LratEncoding.enc2Cube 10 14 k)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size = (14 : ℕ) → x1.output = (23 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => (if x5.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x5.inputs else x5.inputs).any fun (x6 : ℕ) => Decidable.decide (x6 = (6 : ℕ))) x1.gates = (1 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ))]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C hm hs _ _
  by_contra! he
  let b : List Nat := [515,6,12,24,529,545,578,132,264,160,832,288,720,616,276,628,402,50,138,42,897,713,773,581]
  let p := fun r : Nat => [515,6,12,24,529,545,578,132,264,160,832,288].contains r
  have good : ∀ r ∈ b,
      (List.ofFn (fun i : Fin 10 => r.testBit i.val)) =
        (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 || r.testBit 6]) ∧
      (let x := fun i : Fin 9 => r.testBit i.val
       x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
       x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) = p r := by
    decide +kernel
  have bounded : ∀ r ∈ b, r < 2 ^ 10 := by decide +kernel
  obtain ⟨k, hk, hsat⟩ := link 10 14 p b C (by decide) bounded hm (by omega) (by
    intro r hr
    obtain ⟨hw, hv⟩ := good r hr
    rw [hw]
    exact (he _).trans hv)
  exact free k hk hsat
