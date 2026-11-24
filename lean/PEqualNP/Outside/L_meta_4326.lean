import Mathlib.Data.Fin.Basic

theorem PEqualNP.Outside.L_meta_4326 : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∀ (x3 : Fin (42 : ℕ)), x2 x3 = Bool.true ↔ ∀ (x4 : Fin (42 : ℕ)), x2 x4 = Bool.true → ¬(x1 x3 x4 ∨ x1 x4 x3); ∀ (x3 : Fin (42 : ℕ) → Bool), x2 x3 ↔ (∀ (x4 x5 : Fin (42 : ℕ)), x3 x4 = Bool.true → x3 x5 = Bool.true → ¬x1 x4 x5) ∧ ∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.false → ∃ (x6 : Fin (42 : ℕ)), x3 x6 = Bool.true ∧ (x1 x4 x6 ∨ x1 x6 x4) := by
  intro R M x
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v hu hv huv
      exact ((h u).1 hu) v hv (Or.inl huv)
    · intro v hv
      by_contra hne
      have : ∀ (u : Fin 42), x u = true → ¬(R v u ∨ R u v) := by
        intro u hu hr
        exact hne ⟨u, hu, hr⟩
      have := (h v).2 this
      rw [hv] at this
      exact Bool.false_ne_true this
  · rintro ⟨hind, hmax⟩ v
    constructor
    · intro hv u hu hr
      rcases hr with hr | hr
      · exact hind v u hv hu hr
      · exact hind u v hu hv hr
    · intro hall
      by_contra hv
      have hv' : x v = false := by simpa using hv
      obtain ⟨u, hu, hr⟩ := hmax v hv'
      exact hall u hu hr
