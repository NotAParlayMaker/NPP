import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2475_1
    (hSupport : ∀ (n : ℕ) (C : Circuit), (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
      (∀ i : Fin n, ∃ x y : Fin n → Bool,
        (∀ j, j ≠ i → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) →
      n ≤ C.size + 1)
    (hLarge : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → 2 * x3 ≤ x6.size + 1 → ∀ x16 ⊆ Finset.range x6.size, (∀ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x18]? = Option.some x19 → (x18 ∈ x16 ↔ x1 x3 x6 x19)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size) :
  have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (∀ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x18]? = Option.some x19 → (x18 ∈ x16 ↔ x1 x3 x6 x19)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  dsimp only
  intro q N I _ C hq hN hline huniq hmono hout hsorted haccept hreject U hrange hexact hcount
  have hdist (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro he
    have hval := congrArg Fin.val he
    simp at hval
    omega
  have hsingleton (w : Fin (N + N)) :
      circuitFun (N + N) C (fun j => decide (j = w)) = false := by
    apply hreject
    · have hu : Fintype.card {l : Fin N // decide (Fin.natAdd N l = w) = true} ≤
          Fintype.card Unit := by
        apply Fintype.card_le_of_injective (fun _ => ())
        intro l l' _
        apply Subtype.ext
        have he : Fin.natAdd N l.val = Fin.natAdd N l'.val :=
          (of_decide_eq_true l.prop).trans (of_decide_eq_true l'.prop).symm
        apply Fin.ext
        have hval := congrArg Fin.val he
        simp at hval
        omega
      simp only [Fintype.card_unit] at hu
      omega
    · rintro ⟨p, l, _, hp, hl⟩
      exact hdist p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  have hpoint (p : Fin N) : ∃ l, I p l := by
    let zero : Fin N := ⟨0, by omega⟩
    let one : Fin N := ⟨1, by omega⟩
    have hzo : zero ≠ one := by
      intro h
      have hval := congrArg Fin.val h
      change 0 = 1 at hval
      contradiction
    by_cases hp : p = zero
    · obtain ⟨l, hl, _⟩ := huniq p one (by simpa only [hp] using hzo)
      exact ⟨l, hl.1⟩
    · obtain ⟨l, hl, _⟩ := huniq p zero hp
      exact ⟨l, hl.1⟩
  have hlinePoint (l : Fin N) : ∃ p, I p l := by
    have hpos : 0 < Fintype.card {p : Fin N // I p l} := by rw [hline l]; omega
    obtain ⟨p⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨p.val, p.prop⟩
  have hv : N + N ≤ C.size + 1 := by
    apply hSupport (N + N) C (fun g hg => (hmono g hg).2)
    intro i
    induction i using Fin.addCases with
    | left p =>
      obtain ⟨l, hp⟩ := hpoint p
      refine ⟨(fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)),
        (fun j => decide (j = Fin.natAdd N l)), ?_, ?_⟩
      · intro j hj
        simp only [hj, false_or, or_false]
      · rw [haccept p l hp, hsingleton]
        decide
    | right l =>
      obtain ⟨p, hl⟩ := hlinePoint l
      refine ⟨(fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)),
        (fun j => decide (j = Fin.castAdd N p)), ?_, ?_⟩
      · intro j hj
        simp only [hj, false_or, or_false]
      · rw [haccept p l hl, hsingleton]
        decide
  by_cases hsmall : q ≤ 199
  · have hNbig : 100 ≤ N := by omega
    exact (Nat.mul_le_mul_left N hsmall).trans (by omega)
  · exact hLarge q N I C (by omega) hN hline huniq hmono hout hsorted haccept hreject
      (by omega) U hrange hexact hcount
