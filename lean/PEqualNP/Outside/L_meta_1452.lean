import PEqualNP.Defs
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Order.Basic

/-!
# Partition lemma: AND over splitting colourings of OR over colours of monotone one-point tests
-/

set_option linter.dupNamespace false

namespace PEqualNP.Outside.L_meta_1452

theorem L_meta_1452 :
    ∀ (n f k w : ℕ) (L : Finset (Fin n)) (c : Fin f → Fin n → Fin k)
      (T : Fin f → Fin k → (Fin n → Bool) → Bool),
      (∀ S : Finset (Fin n), S.card ≤ w → ∃ j0 : Fin f, Set.InjOn (c j0) (S : Set (Fin n))) →
      (∀ (j1 : Fin f) (a1 : Fin k) (u v : Fin n → Bool), u ≤ v → T j1 a1 u ≤ T j1 a1 v) →
      (∀ (j2 : Fin f) (a2 : Fin k) (z : Fin n → Bool),
          (∀ p2 : Fin n, z p2 = true → c j2 p2 ≠ a2) → T j2 a2 z = false) →
      (∀ (j3 : Fin f) (a3 : Fin k) (y : Fin n → Bool) (p3 : Fin n),
          y p3 = true → c j3 p3 = a3 →
          (∀ q3 : Fin n, y q3 = true → c j3 q3 = a3 → q3 = p3) →
          (T j3 a3 y = true ↔ p3 ∈ L)) →
      ∀ x : Fin n → Bool,
        (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ w →
        ((∀ j : Fin f, ∃ a : Fin k, T j a x = true) ↔ ∃ p : Fin n, x p = true ∧ p ∈ L) := by
  intro n f k w L c T hInj hMono hSupp hPoint x hx
  set S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => x i = true)
  constructor
  · -- (∀ j, ∃ a, T j a x) → ∃ p, x p ∧ p ∈ L
    intro hAll
    obtain ⟨j0, hj0⟩ := hInj S hx
    obtain ⟨a0, ha0⟩ := hAll j0
    have hex : ∃ p : Fin n, x p = true ∧ c j0 p = a0 := by
      by_contra hnone
      push Not at hnone
      have hfalse : T j0 a0 x = false :=
        hSupp j0 a0 x fun p2 hp2 => hnone p2 hp2
      simp [hfalse] at ha0
    obtain ⟨p, hp_true, hp_col⟩ := hex
    have huniq : ∀ q : Fin n, x q = true → c j0 q = a0 → q = p := by
      intro q hq_true hq_col
      have hqS : q ∈ S := by simp [S, hq_true]
      have hpS : p ∈ S := by simp [S, hp_true]
      exact hj0 hqS hpS (hq_col.trans hp_col.symm)
    have hiff : T j0 a0 x = true ↔ p ∈ L :=
      hPoint j0 a0 x p hp_true hp_col fun q3 hq3 hq3c => huniq q3 hq3 hq3c
    exact ⟨p, hp_true, hiff.mp ha0⟩
  · -- ∃ p, x p ∧ p ∈ L → ∀ j, ∃ a, T j a x
    intro hEx j
    obtain ⟨p, hp_true, hpL⟩ := hEx
    set a : Fin k := c j p
    -- Keep only `p` among the colour-`a` true bits of `x`.
    set y : Fin n → Bool := fun q =>
      decide (x q = true ∧ (c j q ≠ a ∨ q = p))
    have hy_le : y ≤ x := by
      intro q
      change y q ≤ x q
      simp only [y]
      cases x q <;> simp
    have hyp : y p = true := by
      simp [y, hp_true, a]
    have hy_uniq : ∀ q3 : Fin n, y q3 = true → c j q3 = a → q3 = p := by
      intro q3 hq3 hq3c
      have hq3' : x q3 = true ∧ (c j q3 ≠ a ∨ q3 = p) := by
        simpa [y, decide_eq_true_eq] using hq3
      rcases hq3'.2 with hne | heq
      · exact (hne hq3c).elim
      · exact heq
    have hyT : T j a y = true :=
      (hPoint j a y p hyp rfl hy_uniq).mpr hpL
    have hle : T j a y ≤ T j a x := hMono j a y x hy_le
    have : T j a x = true := by
      have ht : true ≤ T j a x := by simpa [hyT] using hle
      exact (Bool.le_iff_imp.mp ht) rfl
    exact ⟨a, this⟩

end PEqualNP.Outside.L_meta_1452
