import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4649

abbrev Sig := Fin 62 → Bool

def seed : List Sig :=
  ([2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696,
    54820275478360064, 3870282840506368, 133412159488, 1911954591369396745,
    218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114,
    270286071509155872, 288160007408582916] : List Nat).map
    (fun n t => n.testBit t.val)

def target : Sig := fun t => decide (t.val < 21)

def zero : Sig := fun _ => false

def GateLaw (s : List Sig) : Prop :=
  ∀ j < s.length, ∃ a b : ℕ, a ≠ b ∧ a < 14 + j ∧ b < 14 + j ∧
    let A := (seed ++ s).getD a zero
    let B := (seed ++ s).getD b zero
    s.getD j zero = (fun t => A t || B t) ∨
      0 < j ∧ s.getD j zero = (fun t =>
        if t = 60 then (A 58 && B 60) || (A 60 && B 58)
        else if t = 61 then (A 59 && B 61) || (A 61 && B 59)
        else A t && B t)

def Sparse (s : List Sig) : Prop :=
  ∀ x : Sig, let k := (seed ++ s).count x
    k ≤ 2 ∧ (1 < k → ∃ y ∈ s, y ≠ x ∧
      y = fun i => x i && (decide (i.val < 60) || x (i - 2)))

end PEqualNP.Outside.L_meta_4649

theorem PEqualNP.Outside.L_meta_4649
    (normalize : ∀ s : List PEqualNP.Outside.L_meta_4649.Sig,
      PEqualNP.Outside.L_meta_4649.target ∈ s →
      PEqualNP.Outside.L_meta_4649.GateLaw s →
      ∃ t, t.length ≤ s.length ∧ PEqualNP.Outside.L_meta_4649.target ∈ t ∧
        PEqualNP.Outside.L_meta_4649.GateLaw t ∧ PEqualNP.Outside.L_meta_4649.Sparse t)
    (obstruction : ∀ t : List PEqualNP.Outside.L_meta_4649.Sig,
      t.length ≤ 27 → PEqualNP.Outside.L_meta_4649.target ∈ t →
      PEqualNP.Outside.L_meta_4649.GateLaw t →
      PEqualNP.Outside.L_meta_4649.Sparse t → False) :
    (have x1 : List (Fin (62 : ℕ) → Bool) := List.map
      (fun (x1 : ℕ) (x2 : Fin (62 : ℕ)) => x1.testBit ↑x2)
      [(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ),
       (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ),
       (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ),
       (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ),
       (270286071509155872 : ℕ), (288160007408582916 : ℕ)];
      ¬∃ (x2 : List (Fin (62 : ℕ) → Bool)), x2.length ≤ (27 : ℕ) ∧
        (fun (x3 : Fin (62 : ℕ)) => Decidable.decide (↑x3 < (21 : ℕ))) ∈ x2 ∧
        ∀ x3 < x2.length, ∃ (x5 : ℕ) (x6 : ℕ), x5 ≠ x6 ∧
          x5 < (14 : ℕ) + x3 ∧ x6 < (14 : ℕ) + x3 ∧
          have x7 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x5
            (fun (x7 : Fin (62 : ℕ)) => Bool.false)
          have x8 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x6
            (fun (x8 : Fin (62 : ℕ)) => Bool.false)
          ((x2.getD x3 (fun (x9 : Fin (62 : ℕ)) => Bool.false) =
            fun (x9 : Fin (62 : ℕ)) => x7 x9 || x8 x9) ∨
            (0 : ℕ) < x3 ∧
            x2.getD x3 (fun (x9 : Fin (62 : ℕ)) => Bool.false) =
              fun (x9 : Fin (62 : ℕ)) =>
                if x9 = (60 : Fin (62 : ℕ)) then
                  x7 (58 : Fin (62 : ℕ)) && x8 (60 : Fin (62 : ℕ)) ||
                    x7 (60 : Fin (62 : ℕ)) && x8 (58 : Fin (62 : ℕ))
                else if x9 = (61 : Fin (62 : ℕ)) then
                  x7 (59 : Fin (62 : ℕ)) && x8 (61 : Fin (62 : ℕ)) ||
                    x7 (61 : Fin (62 : ℕ)) && x8 (59 : Fin (62 : ℕ))
                else x7 x9 && x8 x9)) := by
  classical
  change ¬ ∃ s : List PEqualNP.Outside.L_meta_4649.Sig,
    s.length ≤ 27 ∧ PEqualNP.Outside.L_meta_4649.target ∈ s ∧
      PEqualNP.Outside.L_meta_4649.GateLaw s
  rintro ⟨s, hlen, htarget, hgate⟩
  obtain ⟨t, hshort, htarget', hgate', hsparse⟩ := normalize s htarget hgate
  exact obstruction t (hshort.trans hlen) htarget' hgate' hsparse
