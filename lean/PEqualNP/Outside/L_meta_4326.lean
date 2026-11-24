import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4326 : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∀ (x3 : Fin (42 : ℕ)), x2 x3 = Bool.true ↔ ∀ (x4 : Fin (42 : ℕ)), x2 x4 = Bool.true → ¬(x1 x3 x4 ∨ x1 x4 x3); ∀ (x3 : Fin (42 : ℕ) → Bool), x2 x3 ↔ (∀ (x4 x5 : Fin (42 : ℕ)), x3 x4 = Bool.true → x3 x5 = Bool.true → ¬x1 x4 x5) ∧ ∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.false → ∃ (x6 : Fin (42 : ℕ)), x3 x6 = Bool.true ∧ (x1 x4 x6 ∨ x1 x6 x4) := by
  dsimp only
  intro z
  constructor
  · intro h
    refine ⟨fun a b ha hb hab => ?_, fun v hv => ?_⟩
    · exact (h a).1 ha b hb (Or.inl hab)
    · by_contra hne
      have ht : z v = true := (h v).2 (fun w hw hadj => hne ⟨w, hw, hadj⟩)
      rw [hv] at ht
      exact Bool.false_ne_true ht
  · rintro ⟨hi, hd⟩ v
    constructor
    · intro hv w hw hadj
      rcases hadj with h | h
      · exact hi v w hv hw h
      · exact hi w v hw hv h
    · intro h
      by_contra hne
      have hf : z v = false := Bool.eq_false_iff.mpr hne
      obtain ⟨w, hw, hadj⟩ := hd v hf
      exact h w hw hadj
