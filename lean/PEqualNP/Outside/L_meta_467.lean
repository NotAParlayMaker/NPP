import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_467 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ T' ∨ y ∈ T' := by
  intro m k H Q S hk hQ hS T T' hcover hT x y hxy
  obtain ⟨u,v,huv,hadj,p,hp,hxy'⟩ := (hS x y).mp hxy
  have endpoint {w : Fin (m + 2 * k * (m * m))} {a : Fin m} (ha : a ∈ T)
      (hw : w.val = a.val) : w ∈ T' :=
    (hT w).mpr (Or.inl ⟨a, ha, hw⟩)
  have inner {i : ℕ} {w : Fin (m + 2 * k * (m * m))} (hi : i < 2 * k)
      (hw : Q u v (i + 1) w) (hpar : i % 2 = 1 ↔ u ∈ T) : w ∈ T' := by
    apply (hT w).mpr
    refine Or.inr ⟨u, v, i, hi, huv, hadj, ?_, hpar⟩
    rcases (hQ u v (i+1) w).mp hw with hw | hw | hw <;> omega
  have oriented (a b : Fin (m + 2 * k * (m * m)))
      (ha : Q u v p a) (hb : Q u v (p+1) b) : a ∈ T' ∨ b ∈ T' := by
    cases p with
    | zero =>
      by_cases hu : u ∈ T
      · left
        apply endpoint hu
        rcases (hQ u v 0 a).mp ha with ha | ha | ha <;> omega
      · right
        apply inner (i := 0) (by omega) hb
        simp [hu]
    | succ i =>
      by_cases hpar : i % 2 = 1 ↔ u ∈ T
      · exact Or.inl (inner (by omega) ha hpar)
      · right
        by_cases he : i + 1 = 2 * k
        · have hu : u ∉ T := by
            intro hu
            apply hpar
            simpa [hu] using (show i % 2 = 1 by omega)
          have hv : v ∈ T := (hcover u v hadj).resolve_left hu
          apply endpoint hv
          rcases (hQ u v (i+1+1) b).mp hb with hb | hb | hb <;> omega
        · apply inner (i := i+1) (by omega) hb
          by_cases hu : u ∈ T <;> simp_all <;> omega
  rcases hxy' with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact oriented x y hx hy
  · exact (oriented y x hy hx).symm
