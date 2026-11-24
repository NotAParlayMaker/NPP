import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1504_aux

theorem unit_le {N : ℕ} (p : Fin N) (z : Fin N → Bool) (hz : z p = true) :
    (fun k : Fin N => decide (k = p)) ≤ z := by
  intro k hk
  simp only [decide_eq_true_eq] at hk
  subst k
  exact hz

theorem t_of_incident {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (t : Fin N → (Fin N → Bool) → Bool)
    (hmono : ∀ l0 : Fin N, Monotone (t l0))
    (hunit : ∀ p4 l4 : Fin N, I p4 l4 →
      ∃ l5 : Fin N, decide (l5 = l4) = true ∧
        t l5 (fun k4 : Fin N => decide (k4 = p4)) = true)
    (l6 p8 : Fin N) (z : Fin N → Bool)
    (hI : I p8 l6) (hz : z p8 = true) :
    t l6 z = true := by
  obtain ⟨l5, hl5, ht⟩ := hunit p8 l6 hI
  have hl5' : l5 = l6 := by
    simpa using hl5
  subst l5
  exact hmono l6 (unit_le p8 z hz) ht

theorem incident_of_t {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (t : Fin N → (Fin N → Bool) → Bool)
    (hcover : ∀ (x y : Fin N → Bool),
      (∀ l1 : Fin N,
        (Finset.univ.filter (fun p1 : Fin N => I p1 l1 ∧ x p1 = true)).card ≤ 2) →
      (∃ l2 : Fin N, y l2 = true ∧ t l2 x = true) →
      ∃ p3 l3 : Fin N, I p3 l3 ∧ x p3 = true ∧ y l3 = true)
    (l6 : Fin N) (z : Fin N → Bool)
    (hzcard : ∀ l7 : Fin N,
      (Finset.univ.filter (fun p7 : Fin N => I p7 l7 ∧ z p7 = true)).card ≤ 2)
    (ht : t l6 z = true) :
    ∃ p8 : Fin N, I p8 l6 ∧ z p8 = true := by
  let y : Fin N → Bool := fun l => decide (l = l6)
  have hy : ∃ l2 : Fin N, y l2 = true ∧ t l2 z = true := by
    refine ⟨l6, ?_, ht⟩
    simp [y]
  obtain ⟨p3, l3, hI, hx, hy3⟩ := hcover z y hzcard hy
  have hl3 : l3 = l6 := by
    simpa [y] using hy3
  subst l3
  exact ⟨p3, hI, hx⟩

theorem main : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
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
  intro N I _ t _hC4 hmono hcover hunit l6 z hzcard
  constructor
  · intro ht
    exact incident_of_t I t hcover l6 z hzcard ht
  · intro ⟨p8, hI, hz⟩
    exact t_of_incident I t hmono hunit l6 p8 z hI hz

end PEqualNP.Outside.L_meta_1504_aux

theorem PEqualNP.Outside.L_meta_1504 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
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
      (t l6 z = true ↔ ∃ p8 : Fin N, I p8 l6 ∧ z p8 = true) :=
  PEqualNP.Outside.L_meta_1504_aux.main
