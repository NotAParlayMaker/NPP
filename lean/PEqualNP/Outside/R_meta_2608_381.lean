import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.BlindGate PEqualNP.TopForm

-- Enumerate point masks. The line mask and the condition for a maximal row are forced.
-- This leaves explicit edge and mask tests for the two inputs to the last gate.
theorem PEqualNP.Outside.R_meta_2608_381
    (rows : ∀ (E : Fin 13 → Fin 13 → Prop) [DecidableRel E] (z : Fin 26 → Bool),
      Maximal (fun x : Fin 26 → Bool => ¬ ∃ p l, E p l ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) z →
      let y := fun p : Fin 13 => z (Fin.castAdd 13 p)
      let lines := fun l : Fin 13 => decide (∀ p, E p l → y p = false)
      z = Fin.append y lines ∧ ∀ p, y p = false → ∃ l, E p l ∧ lines l = true)
    (search :
      let E := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let Z := fun (y : Fin 13 → Bool) (l : Fin 13) => !(y l || y (l+1) || y (l+3) || y (l+9))
      ∃ (C : Circuit) (j a b : ℕ), C.size ≤ 64 ∧ IsAO2 26 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.output = 26+j ∧
        C.gates[j]? = some ⟨.and, [a,b]⟩ ∧
        (∀ p l, E p l →
          let x := Fin.append (fun i : Fin 13 => decide (i = p)) (fun i : Fin 13 => decide (i = l))
          wireValue C 26 x a = true ∧ wireValue C 26 x b = true) ∧
        ∀ y, (∀ p, y p = false → ∃ l, E p l ∧ Z y l = true) →
          wireValue C 26 (Fin.append y (Z y)) (if Z y 0 then a else b) = false) : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  let E := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let Z := fun (y : Fin 13 → Bool) (l : Fin 13) => !(y l || y (l+1) || y (l+3) || y (l+9))
  obtain ⟨C,j,a,b,hsize,hao,hdup,hout,hgate,hyes,hno⟩ := search
  refine ⟨C,j,a,b,hsize,hao,hdup,hout,hgate,?_,?_⟩
  · intro p l h
    have disjoint (i k : Fin 13) : Fin.castAdd 13 i ≠ Fin.natAdd 13 k := by
      intro e
      have hv := congrArg Fin.val e
      simp at hv
      omega
    have inputs : (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) =
        Fin.append (fun i => decide (i = p)) (fun i => decide (i = l)) := by
      funext i
      refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
      · intro k
        simp only [Fin.append_left, disjoint k l, or_false, (Fin.castAdd_injective 13 13).eq_iff]
      · intro k
        simp only [Fin.append_right, (disjoint p k).symm, false_or, (Fin.natAdd_injective 13 13).eq_iff]
    simpa only [inputs] using hyes p l h
  · intro z hz
    let y := fun p : Fin 13 => z (Fin.castAdd 13 p)
    have hline (l : Fin 13) : decide (∀ p, E p l → y p = false) = Z y l := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Z, Bool.not_eq_true', Bool.or_eq_false_iff]
      constructor
      · intro h
        exact ⟨⟨⟨h l (.inl rfl), h (l+1) (.inr (.inl rfl))⟩,
          h (l+3) (.inr (.inr (.inl rfl)))⟩, h (l+9) (.inr (.inr (.inr rfl)))⟩
      · rintro ⟨⟨⟨h0,h1⟩,h3⟩,h9⟩ p hp
        change p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9 at hp
        rcases hp with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨hrow,hclosed⟩ := rows E z hz
    change z = Fin.append y (fun l => decide (∀ p, E p l → y p = false)) at hrow
    simp only [hline] at hrow
    change (∀ p, y p = false → ∃ l, E p l ∧ decide (∀ v, E v l → y v = false) = true) at hclosed
    simp only [hline] at hclosed
    have linezero : Fin.append y (Z y) (13 : Fin 26) = Z y 0 := by
      exact Fin.append_right y (Z y) 0
    simpa only [hrow, linezero] using hno y hclosed
