import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1774_347
    (trace : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ (j : ℕ) (u v : Fin n),
      Owns n C j u v → ∀ w ∈ (gateAt C j).inputs, u ∈ orIn n C w ∨ v ∈ orIn n C w)
    (exchange : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      let E := fun (D : Circuit) j a b => G.Adj a b ∧ Owns n D j a b
      let useful := fun (D : Circuit) => ∀ j < D.size, (gateAt D j).op = .and → ∃ a b, E D j a b
      let bad := fun (D : Circuit) => {j : ℕ | ∃ a b c d, E D j a b ∧ E D j c d ∧
        a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d}
      ∀ C, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → useful C →
      ∀ j ∈ bad C, (∀ i < j, i ∉ bad C) →
      (∀ a b, E C j a b → ∀ w ∈ (gateAt C j).inputs, a ∈ orIn n C w ∨ b ∈ orIn n C w) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        useful D ∧ (bad D).ncard < (bad C).ncard) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8 := by
  classical
  intro n G dec triangle square useful cost C least computes every positive
  let bad (D : Circuit) : Set ℕ := {j | ∃ a b c d : Fin n, (G.Adj a b ∧ Owns n D j a b) ∧
    (G.Adj c d ∧ Owns n D j c d) ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d}
  have equal (D : Circuit) : cost D = (bad D).ncard := by
    change Set.ncard _ = Set.ncard (bad D)
    apply congrArg (fun s : Set ℕ => s.ncard)
    ext j
    simp only [bad, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, b, c, d, ab, cd, jab, jcd, ac, ad, bc, bd⟩
      exact ⟨a, b, c, d, ⟨ab, jab⟩, ⟨cd, jcd⟩, ac, ad, bc, bd⟩
    · rintro ⟨a, b, c, d, ⟨ab, jab⟩, ⟨cd, jcd⟩, ac, ad, bc, bd⟩
      exact ⟨a, b, c, d, ab, cd, jab, jcd, ac, ad, bc, bd⟩
  rw [equal C] at positive
  have finite : (bad C).Finite := by
    apply (Set.finite_Iio C.size).subset
    rintro j ⟨a, b, c, d, ⟨_, own⟩, _⟩
    exact own.1
  have existsBad : ∃ j, j ∈ bad C := (Set.ncard_pos finite).mp positive
  let first := Nat.find existsBad
  have firstBad : first ∈ bad C := Nat.find_spec existsBad
  have earlierGood (i : ℕ) (hi : i < first) : i ∉ bad C := Nat.find_min existsBad hi
  obtain ⟨D, mono, eval, size, works, drop⟩ :=
    exchange n G triangle square C least computes every first firstBad earlierGood
      (fun a b hab => trace n C least.1 first a b hab.2)
  exact ⟨D, mono, eval, size, works, by rw [equal D, equal C]; exact drop⟩
