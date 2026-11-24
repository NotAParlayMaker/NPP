import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1900_438
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      let f := fun x : Fin n → Bool => ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
      PEqualNP.MetaComplexity.Monotone2 C → (∀ x, C.eval (List.ofFn x) = true ↔ f x) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ C.size ∧
        (∀ x, D.eval (List.ofFn x) = true ↔ f x) ∧
        ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[j]? = some g →
          g.op = .and → let w := fun x : Fin n → Bool => (D.wires (List.ofFn x)).getD (n + j) false
          (∀ x, w x = true → f x) ∨ 2 ≤ ({e ∈ G.edgeSet | w (fun i => decide (i ∈ e)) = true} :
            Set (Sym2 (Fin n))).ncard)
    (remaining : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      let f := fun x : Fin n → Bool => ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
      (∃ u v, G.Adj u v) →
      (∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.Monotone2 C → (∀ x, C.eval (List.ofFn x) = true ↔ f x) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        g.op = .and → let w := fun x : Fin n → Bool => (C.wires (List.ofFn x)).getD (n + j) false
        (∀ x, w x = true → f x) ∨ 2 ≤ ({e ∈ G.edgeSet | w (fun i => decide (i ∈ e)) = true} :
          Set (Sym2 (Fin n))).ncard) →
      PEqualNP.BicliqueBlockCost.HasBlockCost G C.size) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x3.size := by
  intro n G C edges noFour mono exactC
  obtain ⟨D, monoD, cap, exactD, large⟩ := normalize n G C mono exactC
  obtain ⟨blocks, covers, cost⟩ := remaining n G D edges noFour monoD exactD large
  exact ⟨blocks, covers, cost.trans cap⟩
