import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

-- The clauses of enc encode the circuit on the specified rows.
-- The adjacent independent gates can then be put in lexicographic order.
-- The last gate supplies a first source and an opcode indexing a cube.
theorem PEqualNP.Outside.R_meta_4805_19
    (base : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : Circuit),
      (∀ r ∈ rows, r < 2 ^ n) → Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) →
      FormulaSat (enc n s g rows))
    (order : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ), 0 < s →
      (∀ r ∈ rows, r < 2 ^ n) → FormulaSat (enc n s g rows) →
      FormulaSat (enc2 n s g rows))
    (cover : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ), 0 < s →
      FormulaSat (enc2 n s g rows) →
      ∃ k < enc2CubeCount n s, FormulaSat (enc2 n s g rows ++ enc2Cube n s k)) :
    ∀ (x1 x2 : ℕ) (x3 : ℕ → Bool) (x4 : List ℕ) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x2 → (∀ x7 ∈ x4, x7 < (2 : ℕ) ^ x1) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.size ≤ x2 → (∀ x10 ∈ x4, x5.eval (List.ofFn fun (x12 : Fin x1) => x10.testBit ↑x12) = x3 x10) → ∃ x11 < PEqualNP.Defs.LratEncoding.enc2CubeCount x1 x2, PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 x1 x2 x3 x4 ++ PEqualNP.Defs.LratEncoding.enc2Cube x1 x2 x11) := by
  intro n s g rows C hs rowBound mono size agrees
  exact cover n s g rows hs (order n s g rows hs rowBound (base n s g rows C rowBound mono size agrees))
