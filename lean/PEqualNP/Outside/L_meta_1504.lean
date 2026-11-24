import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1504

open Classical

theorem main
    (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (t : Fin N → (Fin N → Bool) → Bool)
    (_hRect : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (hMono : ∀ l0 : Fin N, Monotone (t l0))
    (hSound : ∀ (x y : Fin N → Bool),
      (∀ l1 : Fin N,
        (Finset.univ.filter (fun p1 : Fin N => I p1 l1 ∧ x p1 = true)).card ≤ 2) →
      (∃ l2 : Fin N, y l2 = true ∧ t l2 x = true) →
      ∃ p3 l3 : Fin N, I p3 l3 ∧ x p3 = true ∧ y l3 = true)
    (hPin : ∀ p4 l4 : Fin N, I p4 l4 →
      ∃ l5 : Fin N, decide (l5 = l4) = true ∧
        t l5 (fun k4 : Fin N => decide (k4 = p4)) = true)
    (l6 : Fin N) (z : Fin N → Bool)
    (hDeg : ∀ l7 : Fin N,
      (Finset.univ.filter (fun p7 : Fin N => I p7 l7 ∧ z p7 = true)).card ≤ 2) :
    t l6 z = true ↔ ∃ p8 : Fin N, I p8 l6 ∧ z p8 = true := by
  constructor
  · intro ht
    -- Soundness with y concentrated on l6 recovers an incident true point.
    have hy : ∃ l2 : Fin N, (decide (l2 = l6) = true) ∧ t l2 z = true :=
      ⟨l6, by simp, ht⟩
    have hY : ∃ l2 : Fin N,
        (fun l : Fin N => decide (l = l6)) l2 = true ∧ t l2 z = true := by
      simpa using hy
    obtain ⟨p3, l3, hI, hz, hy3⟩ := hSound z (fun l => decide (l = l6)) hDeg hY
    have hl : l3 = l6 := by
      simpa [decide_eq_true_eq] using hy3
    subst hl
    exact ⟨p3, hI, hz⟩
  · intro ⟨p8, hI, hz⟩
    obtain ⟨l5, hl5, hpin⟩ := hPin p8 l6 hI
    have hl5' : l5 = l6 := by simpa [decide_eq_true_eq] using hl5
    -- Singleton e ≤ z on the true coordinate, then monotone lifts the pin.
    set e : Fin N → Bool := fun k4 => decide (k4 = p8)
    have hle : e ≤ z := by
      intro k
      change e k ≤ z k
      by_cases hk : k = p8
      · subst hk; simp [e, hz]
      · simp [e, hk]
    have hpin' : t l6 e = true := by simpa [hl5', e] using hpin
    have hlift : t l6 e ≤ t l6 z := hMono l6 hle
    have htop : true ≤ t l6 z := by simpa [hpin'] using hlift
    cases hz' : t l6 z with
    | false =>
      have htf : true ≤ false := by simpa [hz'] using htop
      exact htf rfl
    | true => rfl

end PEqualNP.Outside.L_meta_1504

theorem PEqualNP.Outside.L_meta_1504 :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (t : Fin N → (Fin N → Bool) → Bool),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      (∀ l0 : Fin N, Monotone (t l0)) →
      (∀ (x y : Fin N → Bool),
        (∀ l1 : Fin N,
          (Finset.univ.filter (fun p1 : Fin N => I p1 l1 ∧ x p1 = true)).card ≤ 2) →
        (∃ l2 : Fin N, y l2 = true ∧ t l2 x = true) →
        ∃ p3 l3 : Fin N, I p3 l3 ∧ x p3 = true ∧ y l3 = true) →
      (∀ p4 l4 : Fin N, I p4 l4 →
        ∃ l5 : Fin N, decide (l5 = l4) = true ∧
          t l5 (fun k4 : Fin N => decide (k4 = p4)) = true) →
      ∀ (l6 : Fin N) (z : Fin N → Bool),
        (∀ l7 : Fin N,
          (Finset.univ.filter (fun p7 : Fin N => I p7 l7 ∧ z p7 = true)).card ≤ 2) →
        (t l6 z = true ↔ ∃ p8 : Fin N, I p8 l6 ∧ z p8 = true) := by
  intro N I _ t _hRect hMono hSound hPin l6 z hDeg
  exact PEqualNP.Outside.L_meta_1504.main N I t _hRect hMono hSound hPin l6 z hDeg
