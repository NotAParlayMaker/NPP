import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8787 : ∀ (x1 : List ℕ) (x2 : ℕ),   have x3 : (ℕ → Prop) → (ℕ → Prop) → ℕ → Prop := fun (x3 x4 : ℕ → Prop) (x5 : ℕ) => ∃ (x6 : ℕ), x3 x6 ∧ ∃ (x7 : ℕ), x4 x7 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7);   have x4 : List ℕ → ℕ → Prop := fun (x4 : List ℕ) => x3 (fun (x5 : ℕ) => x5 ∈ x4) fun (x5 : ℕ) => x5 ∈ x4;   (have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 ∈ x1;     have x6 : ℕ → Prop := x3 x5 x5;     x3 x6 x6 x2 ∨ x3 x5 (x3 x5 x6) x2) →     ∃ (x6 : List ℕ), x6.length ≤ (2 : ℕ) ∧ (∀ (x7 : Fin x6.length), x4 (x1 ++ List.take (↑x7) x6) (x6.get x7)) ∧ x4 (x1 ++ x6) x2 := by
  intro L t
  dsimp only
  intro h
  rcases h with ⟨g1, ⟨a, ha, b, hb, hg1⟩, g2, ⟨c, hc, d, hd, hg2⟩, ht⟩ | ⟨a, ha, y, ⟨a', ha', b, ⟨c, hc, d, hd, hb⟩, hy⟩, ht⟩
  · refine ⟨[g1, g2], by simp, ?_, ⟨g1, by simp, g2, by simp, ht⟩⟩
    intro i
    match i with
    | ⟨0, _⟩ => exact ⟨a, by simp [ha], b, by simp [hb], hg1⟩
    | ⟨1, _⟩ => exact ⟨c, by simp [hc], d, by simp [hd], hg2⟩
    | ⟨n + 2, hn⟩ => exact absurd hn (by simp)
  · refine ⟨[b, y], by simp, ?_, ⟨a, by simp [ha], y, by simp, ht⟩⟩
    intro i
    match i with
    | ⟨0, _⟩ => exact ⟨c, by simp [hc], d, by simp [hd], hb⟩
    | ⟨1, _⟩ => exact ⟨a', by simp [ha'], b, by simp, hy⟩
    | ⟨n + 2, hn⟩ => exact absurd hn (by simp)
