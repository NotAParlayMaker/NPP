import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8061

theorem main (x1 x2 x3 : ℕ) (x4 x5 : ℕ → ℕ) (x6 x7 x8 : ℕ → Bool)
    (h3 : x3 < x1) (hlt : ∀ k < x2, x4 k < x1 + k ∧ x5 k < x1 + k)
    (hin : ∀ i < x1, x8 i = decide (i = x3))
    (hg : ∀ k < x2, x8 (x1 + k) = (x8 (x4 k) && x6 k || x8 (x5 k) && x7 k)) :
    ∀ n < x1 + x2, x8 n = true ↔ Relation.ReflTransGen
      (fun (a b : ℕ) => ∃ k < x2, b = x1 + k ∧
        (a = x4 k ∧ x6 k = true ∨ a = x5 k ∧ x7 k = true)) x3 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt1 : n < x1
    · rw [hin n hlt1]
      constructor
      · intro h
        have hh : n = x3 := by simpa using h
        rw [hh]
      · intro h
        rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, _, k, _, hk, _⟩
        · simp [h]
        · omega
    · obtain ⟨k, hnk⟩ : ∃ k, n = x1 + k := ⟨n - x1, by omega⟩
      have hk : k < x2 := by omega
      have h4 := (hlt k hk).1
      have h5 := (hlt k hk).2
      have ih4 := ih (x4 k) (by omega) (by omega)
      have ih5 := ih (x5 k) (by omega) (by omega)
      rw [hnk, hg k hk]
      constructor
      · intro h
        simp only [Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Relation.ReflTransGen.tail (ih4.1 ha) ⟨k, hk, rfl, Or.inl ⟨rfl, hb⟩⟩
        · exact Relation.ReflTransGen.tail (ih5.1 ha) ⟨k, hk, rfl, Or.inr ⟨rfl, hb⟩⟩
      · intro h
        rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hc, j, hj, hkk, hor⟩
        · omega
        · have hjk : j = k := by omega
          rw [hjk] at hor
          simp only [Bool.or_eq_true, Bool.and_eq_true]
          rcases hor with ⟨hca, hb⟩ | ⟨hca, hb⟩
          · rw [hca] at hc
            exact Or.inl ⟨ih4.2 hc, hb⟩
          · rw [hca] at hc
            exact Or.inr ⟨ih5.2 hc, hb⟩

end PEqualNP.Outside.L_meta_8061

theorem PEqualNP.Outside.L_meta_8061 : ∀ (x1 x2 x3 : ℕ) (x4 x5 : ℕ → ℕ) (x6 x7 x8 : ℕ → Bool),   x3 < x1 →     (∀ x10 < x2, x4 x10 < x1 + x10 ∧ x5 x10 < x1 + x10) →       (∀ x11 < x1, x8 x11 = Decidable.decide (x11 = x3)) →         (∀ x12 < x2, x8 (x1 + x12) = (x8 (x4 x12) && x6 x12 || x8 (x5 x12) && x7 x12)) →           have x13 : ℕ → ℕ → Prop := fun (x13 x14 : ℕ) => ∃ x15 < x2, x14 = x1 + x15 ∧ (x13 = x4 x15 ∧ x6 x15 = Bool.true ∨ x13 = x5 x15 ∧ x7 x15 = Bool.true);           ∀ x14 < x1 + x2, x8 x14 = Bool.true ↔ Relation.ReflTransGen x13 x3 x14 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 h3 hlt hin hg
  exact PEqualNP.Outside.L_meta_8061.main x1 x2 x3 x4 x5 x6 x7 x8 h3 hlt hin hg
