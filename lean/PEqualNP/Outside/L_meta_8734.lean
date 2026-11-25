import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8734_aux

open PEqualNP.CircuitLowerBounds

theorem cf_nil (n : ℕ) (C : Circuit) (hg : C.gates = []) (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n C x =
      if h : C.output < n then x ⟨C.output, h⟩ else false := by
  unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval Circuit.wires
  rw [hg]
  simp only [List.foldl_nil]
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default]
    simp
    omega

end PEqualNP.Outside.L_meta_8734_aux

open PEqualNP.Outside.L_meta_8734_aux in
theorem PEqualNP.Outside.L_meta_8734 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (130 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x5.gates = [] → Fintype.card { x14 : Fin x2 × Fin x2 // x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x14.1 ∨ x15 = Fin.natAdd x2 x14.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  intro x1 x2 x3 x4 x5 h1 _ _ _ _ _ hyp hg
  have hs : x5.size = 0 := by simp [PEqualNP.CircuitLowerBounds.Circuit.size, hg]
  rw [hs, Nat.mul_zero, Nat.le_zero, Fintype.card_eq_zero_iff]
  constructor
  rintro ⟨p, hp, hc⟩
  rw [cf_nil _ _ hg] at hc
  split_ifs at hc with ho
  · have hcard : Fintype.card { x13 : Fin x2 // (fun i : Fin (x2 + x2) => decide (i = ⟨x5.output, ho⟩)) (Fin.natAdd x2 x13) = Bool.true } ≤ x1 := by
      refine le_trans ?_ (by omega : 1 ≤ x1)
      rw [Fintype.card_le_one_iff]
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [decide_eq_true_eq] at ha hb
      apply Subtype.ext
      apply Fin.ext
      have h1 := congrArg Fin.val ha
      have h2 := congrArg Fin.val hb
      simp at h1 h2 ⊢
      omega
    have hno : ¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ (fun i : Fin (x2 + x2) => decide (i = ⟨x5.output, ho⟩)) (Fin.castAdd x2 x14) = Bool.true ∧ (fun i : Fin (x2 + x2) => decide (i = ⟨x5.output, ho⟩)) (Fin.natAdd x2 x15) = Bool.true := by
      rintro ⟨a, b, _, ha, hb⟩
      simp only [decide_eq_true_eq] at ha hb
      have h1 := congrArg Fin.val ha
      have h2 := congrArg Fin.val hb
      simp at h1 h2
      omega
    have key := hyp (fun i : Fin (x2 + x2) => decide (i = ⟨x5.output, ho⟩)) hcard hno
    rw [cf_nil _ _ hg] at key
    simp at key
    omega
