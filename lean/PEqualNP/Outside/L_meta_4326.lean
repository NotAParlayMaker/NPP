import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4326 : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∀ (x3 : Fin (42 : ℕ)), x2 x3 = Bool.true ↔ ∀ (x4 : Fin (42 : ℕ)), x2 x4 = Bool.true → ¬(x1 x3 x4 ∨ x1 x4 x3); ∀ (x3 : Fin (42 : ℕ) → Bool), x2 x3 ↔ (∀ (x4 x5 : Fin (42 : ℕ)), x3 x4 = Bool.true → x3 x5 = Bool.true → ¬x1 x4 x5) ∧ ∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.false → ∃ (x6 : Fin (42 : ℕ)), x3 x6 = Bool.true ∧ (x1 x4 x6 ∨ x1 x6 x4) := by
  dsimp only
  intro x
  constructor
  · intro h
    refine ⟨fun a b ha hb hab => (h a).1 ha b hb (Or.inl hab), fun a ha => ?_⟩
    by_contra hne
    have hx : x a = true := (h a).2 fun u hu hadj => hne ⟨u, hu, hadj⟩
    rw [ha] at hx
    exact Bool.false_ne_true hx
  · rintro ⟨hind, hdom⟩ v
    constructor
    · intro hv u hu hadj
      rcases hadj with hvu | huv
      · exact hind v u hv hu hvu
      · exact hind u v hu hv huv
    · intro hall
      by_contra hv
      have hv' : x v = false := by simpa using hv
      obtain ⟨u, hu, hadj⟩ := hdom v hv'
      exact hall u hu hadj
