import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4326 : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∀ (x3 : Fin (42 : ℕ)), x2 x3 = Bool.true ↔ ∀ (x4 : Fin (42 : ℕ)), x2 x4 = Bool.true → ¬(x1 x3 x4 ∨ x1 x4 x3); ∀ (x3 : Fin (42 : ℕ) → Bool), x2 x3 ↔ (∀ (x4 x5 : Fin (42 : ℕ)), x3 x4 = Bool.true → x3 x5 = Bool.true → ¬x1 x4 x5) ∧ ∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.false → ∃ (x6 : Fin (42 : ℕ)), x3 x6 = Bool.true ∧ (x1 x4 x6 ∨ x1 x6 x4) := by
  intro edge fixed x
  constructor
  · intro h
    constructor
    · intro u v hu hv huv
      exact (h u).mp hu v hv (Or.inl huv)
    · intro u hu
      by_contra hnone
      have htrue := (h u).mpr (fun v hv hadj => hnone ⟨v, hv, hadj⟩)
      simp [hu] at htrue
  · rintro ⟨hind, hdom⟩ u
    constructor
    · intro hu v hv hadj
      exact hadj.elim (hind u v hu hv) (hind v u hv hu)
    · intro hfree
      cases hu : x u with
      | false =>
        obtain ⟨v, hv, hadj⟩ := hdom u hu
        exact (hfree v hv hadj).elim
      | true => rfl
