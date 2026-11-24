import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1504

theorem le_of_singleton_mem {N : ℕ} (z : Fin N → Bool) (p : Fin N) (hz : z p = true) :
    (fun k : Fin N => decide (k = p)) ≤ z := by
  intro k hk
  have : k = p := by
    simpa using hk
  subst this
  exact hz

theorem bool_le_true {b : Bool} (h : true ≤ b) : b = true := by
  cases b
  · exact (Bool.false_lt_true.not_ge h).elim
  · rfl

end PEqualNP.Outside.L_meta_1504

open PEqualNP.Outside.L_meta_1504

theorem PEqualNP.Outside.L_meta_1504 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (t : Fin N → (Fin N → Bool) → Bool),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    (∀ l0 : Fin N, Monotone (t l0)) →
    (∀ (x y : Fin N → Bool),
      (∀ l1 : Fin N, (Finset.univ.filter (fun p1 : Fin N => I p1 l1 ∧ x p1 = true)).card ≤ 2) →
      (∃ l2 : Fin N, y l2 = true ∧ t l2 x = true) →
      ∃ p3 l3 : Fin N, I p3 l3 ∧ x p3 = true ∧ y l3 = true) →
    (∀ p4 l4 : Fin N, I p4 l4 →
      ∃ l5 : Fin N, decide (l5 = l4) = true ∧
        t l5 (fun k4 : Fin N => decide (k4 = p4)) = true) →
    ∀ (l6 : Fin N) (z : Fin N → Bool),
      (∀ l7 : Fin N, (Finset.univ.filter (fun p7 : Fin N => I p7 l7 ∧ z p7 = true)).card ≤ 2) →
      (t l6 z = true ↔ ∃ p8 : Fin N, I p8 l6 ∧ z p8 = true) := by
  intro N I _ t _hC4 hMono hBelow hInc l6 z hBand
  constructor
  · intro ht
    have hy : ∃ l2 : Fin N, (fun l => decide (l = l6)) l2 = true ∧ t l2 z = true :=
      ⟨l6, by simp, ht⟩
    obtain ⟨p3, l3, hI, hx, hy'⟩ := hBelow z (fun l => decide (l = l6)) hBand hy
    have hl : l3 = l6 := by
      simpa using hy'
    subst hl
    exact ⟨p3, hI, hx⟩
  · intro hex
    obtain ⟨p8, hI, hz⟩ := hex
    obtain ⟨l5, hl5, ht5⟩ := hInc p8 l6 hI
    have hl : l5 = l6 := by
      simpa using hl5
    have hle : (fun k : Fin N => decide (k = p8)) ≤ z := le_of_singleton_mem z p8 hz
    have hle' : t l6 (fun k => decide (k = p8)) ≤ t l6 z := hMono l6 hle
    have ht6 : t l6 (fun k => decide (k = p8)) = true := by
      simpa [hl] using ht5
    have : true ≤ t l6 z := by
      simpa [ht6] using hle'
    exact bool_le_true this
