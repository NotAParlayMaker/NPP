import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4647

def tbl : List ℕ := [(16771220242439 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (182572334459126281 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)]

def T (j : ℕ) : Fin 14 → Bool := fun x3 => (tbl.getD ↑x3 (0 : ℕ)).testBit j

abbrev incid (p l : Fin 7) : Prop := p = l ∨ p = l + (1 : Fin 7) ∨ p = l + (3 : Fin 7)

def Inc (x : Fin 14 → Bool) : Prop :=
  ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x (Fin.natAdd (7 : ℕ) x4) = Bool.true

def MP (P : Fin 7 → Bool) : Fin 14 → Bool := fun i =>
  if h : i.val < 7 then P ⟨i.val, h⟩ else decide (∀ p : Fin 7, P p = true → ¬ incid p ⟨i.val - 7, by omega⟩)

theorem tests : ∀ j : Fin 58, (Inc (T j.val) ↔ j.val < 21) := by
  unfold Inc
  decide +kernel

theorem cover : ∀ P : Fin 7 → Bool, ∃ j : Fin 37, ∀ i : Fin 14, MP P i = true → T (21 + j.val) i = true := by
  decide +kernel

theorem above : ∀ p l : Fin 7, incid p l → ∃ j : Fin 21, ∀ i : Fin 14, T j.val i = true →
    (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l) := by
  decide +kernel

theorem le_imp {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  subst ha; revert h; cases b <;> decide

theorem imp_le {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> first | decide | exact absurd (h rfl) (by decide)

end PEqualNP.Outside.L_meta_4647

open PEqualNP.Outside.L_meta_4647

theorem PEqualNP.Outside.L_meta_4647 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool), (∀ (x2 : Fin (14 : ℕ) → Bool), x1 x2 = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ↔ Monotone x1 ∧ ∀ (x2 : Fin (58 : ℕ)), (x1 fun (x3 : Fin (14 : ℕ)) => ([(16771220242439 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (182572334459126281 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑x2) = Decidable.decide (↑x2 < (21 : ℕ)) := by
  intro f
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply imp_le
      intro ha
      rw [hf] at ha ⊢
      obtain ⟨p, l, hpl, h1, h2⟩ := ha
      exact ⟨p, l, hpl, le_imp (hab _) h1, le_imp (hab _) h2⟩
    · intro j
      rw [Bool.eq_iff_iff, hf]
      exact (tests j).trans decide_eq_true_iff.symm
  · rintro ⟨hmono, htest⟩ x
    constructor
    · intro hx
      by_contra hni
      obtain ⟨j, hj⟩ := cover (fun p => x (Fin.castAdd 7 p))
      have hle : x ≤ T (21 + j.val) := by
        intro i
        apply imp_le
        intro hxi
        apply hj i
        unfold MP
        split_ifs with h
        · have e : Fin.castAdd 7 (⟨i.val, h⟩ : Fin 7) = i := Fin.ext rfl
          show x (Fin.castAdd 7 ⟨i.val, h⟩) = true
          rw [e]; exact hxi
        · apply decide_eq_true
          intro p hp hpi
          apply hni
          refine ⟨p, ⟨i.val - 7, by omega⟩, hpi, hp, ?_⟩
          have e : Fin.natAdd 7 (⟨i.val - 7, by omega⟩ : Fin 7) = i := Fin.ext (by simp; omega)
          rw [e]; exact hxi
      have h1 := hmono hle
      rw [hx] at h1
      have h3 : f (T (21 + j.val)) = false := by
        rw [show f (T (21 + j.val)) = decide ((21 + j.val) < 21) from htest ⟨21 + j.val, by omega⟩]
        simp
      rw [h3] at h1
      exact absurd h1 (by decide)
    · intro hinc
      obtain ⟨p, l, hpl, hp, hl⟩ := hinc
      obtain ⟨j, hj⟩ := above p l hpl
      have hle : T j.val ≤ x := by
        intro i
        apply imp_le
        intro hti
        rcases hj i hti with rfl | rfl
        · exact hp
        · exact hl
      have h1 := hmono hle
      have h2 : f (T j.val) = true := by
        rw [show f (T j.val) = decide (j.val < 21) from htest ⟨j.val, by omega⟩]
        simp [j.isLt]
      rw [h2] at h1
      exact le_imp h1 rfl
