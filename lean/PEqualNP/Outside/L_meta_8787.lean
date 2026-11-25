import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_8787 : ∀ (x1 : List ℕ) (x2 : ℕ),   have x3 : (ℕ → Prop) → (ℕ → Prop) → ℕ → Prop := fun (x3 x4 : ℕ → Prop) (x5 : ℕ) => ∃ (x6 : ℕ), x3 x6 ∧ ∃ (x7 : ℕ), x4 x7 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7);   have x4 : List ℕ → ℕ → Prop := fun (x4 : List ℕ) => x3 (fun (x5 : ℕ) => x5 ∈ x4) fun (x5 : ℕ) => x5 ∈ x4;   (have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 ∈ x1;     have x6 : ℕ → Prop := x3 x5 x5;     x3 x6 x6 x2 ∨ x3 x5 (x3 x5 x6) x2) →     ∃ (x6 : List ℕ), x6.length ≤ (2 : ℕ) ∧ (∀ (x7 : Fin x6.length), x4 (x1 ++ List.take (↑x7) x6) (x6.get x7)) ∧ x4 (x1 ++ x6) x2 := by
  intro x1 x2 x3 x4 h
  simp only [x3, x4] at h ⊢
  rcases h with ⟨a, ⟨c, hc, d, hd, ha⟩, b, ⟨e, he, f, hf, hb⟩, h2⟩ | ⟨a, ha, b, ⟨c, hc, d, ⟨e, he, f, hf, hd⟩, hb⟩, h2⟩
  · refine ⟨[a, b], by simp, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨c, by simp [hc], d, by simp [hd], ha⟩
      · exact ⟨e, by simp [he], f, by simp [hf], hb⟩
    · exact ⟨a, by simp, b, by simp, h2⟩
  · refine ⟨[d, b], by simp, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨e, by simp [he], f, by simp [hf], hd⟩
      · exact ⟨c, by simp [hc], d, by simp, hb⟩
    · exact ⟨a, by simp [ha], b, by simp, h2⟩
