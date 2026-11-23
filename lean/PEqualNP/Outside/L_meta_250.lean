import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_250_aux (m x y : ℕ) (hx : x < m) (hy : y < m)
    (h : (x + y) % m = 0) : (x = 0 ∧ y = 0) ∨ x + y = m := by
  rcases Nat.lt_or_ge (x + y) m with hl | hl
  · rw [Nat.mod_eq_of_lt hl] at h
    omega
  · rw [Nat.mod_eq_sub_mod hl, Nat.mod_eq_of_lt (by omega)] at h
    omega

theorem PEqualNP.Outside.L_meta_250_mod (m x : ℕ) (hx : x < m) :
    (x + 1 < m ∧ (x + 1) % m = x + 1) ∨ (x + 1 = m ∧ (x + 1) % m = 0) := by
  rcases Nat.lt_or_ge (x + 1) m with hl | hl
  · exact Or.inl ⟨hl, Nat.mod_eq_of_lt hl⟩
  · have : x + 1 = m := by omega
    exact Or.inr ⟨this, by rw [this, Nat.mod_self]⟩

theorem PEqualNP.Outside.L_meta_250 : ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos pos' : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ v : Fin N, pos' v ≤ 2 * k ∧ (pos v + pos' v) % (2 * k + 1) = 0) → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos' u ≠ 0 ∨ pos' v ≠ 0) ∧ ∀ v : Fin N, pos' v ≠ 0 → pos' v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos' a + 1 = pos' v ∧ pos' b = (pos' v + 1) % (2 * k + 1)) := by
  intro N k E pos pos' hk ⟨hsym, hnz, hloc⟩ hrel
  have key : ∀ v : Fin N, pos v ≤ 2 * k → pos' v ≤ 2 * k ∧ ((pos v = 0 ∧ pos' v = 0) ∨ pos v + pos' v = 2 * k + 1) := by
    intro v hv
    refine ⟨(hrel v).1, ?_⟩
    exact PEqualNP.Outside.L_meta_250_aux (2 * k + 1) (pos v) (pos' v) (by omega)
      (by have := (hrel v).1; omega) (hrel v).2
  have zero_iff : ∀ v : Fin N, pos' v ≠ 0 → pos v ≠ 0 := by
    intro v hv h0
    have := key v (by omega)
    omega
  refine ⟨hsym, ?_, ?_⟩
  · intro u v huv
    rcases hnz u v huv with h | h
    · left
      have := key u (hloc u h).1
      have := (hloc u h).1
      omega
    · right
      have := key v (hloc v h).1
      have := (hloc v h).1
      omega
  · intro v hv
    have hp := zero_iff v hv
    obtain ⟨hle, a, b, hw, ha, hb⟩ := hloc v hp
    refine ⟨(hrel v).1, b, a, fun w => (hw w).trans or_comm, ?_, ?_⟩
    · have kv := key v hle
      rcases PEqualNP.Outside.L_meta_250_mod (2 * k + 1) (pos v) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2] at hb
        have kb := key b (by omega)
        omega
      · rw [h2] at hb
        have kb := key b (by omega)
        omega
    · have kv := key v hle
      have ka := key a (by omega)
      rcases PEqualNP.Outside.L_meta_250_mod (2 * k + 1) (pos' v) (by have := (hrel v).1; omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]; omega
      · rw [h2]; omega
