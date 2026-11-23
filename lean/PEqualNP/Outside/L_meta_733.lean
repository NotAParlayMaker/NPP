import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_733_aux
end PEqualNP.Outside.L_meta_733_aux

theorem PEqualNP.Outside.L_meta_733 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (X : Set (Fin n)),
  (∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X)) →
  ∀ I : Set (Fin n),
    ((∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u)) ↔
    ∃ B : Set (Fin n), (∀ b ∈ B, b ∉ X) ∧
      (∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) ↔ y ∈ B)) ∧
      ∀ v, v ∈ I ↔ (v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)) := by
  intro n G X hbip I
  constructor
  · rintro ⟨hind, hdom⟩
    refine ⟨{v | v ∈ I ∧ v ∉ X}, fun b hb => hb.2, ?_, ?_⟩
    · intro y hy
      constructor
      · intro hall
        by_contra hyB
        have hyI : y ∉ I := fun h => hyB ⟨h, hy⟩
        obtain ⟨u, huI, hyu⟩ := hdom y hyI
        have huX : u ∈ X := by
          have := hbip y u hyu
          by_contra h
          exact hy (this.mpr h)
        obtain ⟨b, hb, hub⟩ := hall u hyu
        exact hind u huI b hb.1 hub
      · intro hyB x hyx
        exact ⟨y, hyB, hyx.symm⟩
    · intro v
      constructor
      · intro hv
        by_cases hvX : v ∈ X
        · exact Or.inr ⟨hvX, fun b hb hvb => hind v hv b hb.1 hvb⟩
        · exact Or.inl ⟨hv, hvX⟩
      · rintro (h | ⟨hvX, hnb⟩)
        · exact h.1
        · by_contra hvI
          obtain ⟨u, huI, hvu⟩ := hdom v hvI
          have huX : u ∉ X := (hbip v u hvu).mp hvX
          exact hnb u ⟨huI, huX⟩ hvu
  · rintro ⟨B, hBX, hsat, hI⟩
    constructor
    · intro u hu v hv huv
      rw [hI] at hu hv
      rcases hu with hu | ⟨huX, hun⟩ <;> rcases hv with hv | ⟨hvX, hvn⟩
      · exact hBX u hu ((hbip u v huv).mpr (hBX v hv)) |>.elim
      · exact hvn u hu huv.symm
      · exact hun v hv huv
      · exact ((hbip u v huv).mp huX) hvX
    · intro v hvI
      rw [hI] at hvI
      push_neg at hvI
      obtain ⟨hvB, hvX⟩ := hvI
      by_cases hX : v ∈ X
      · obtain ⟨b, hb, hvb⟩ := hvX hX
        exact ⟨b, (hI b).mpr (Or.inl hb), hvb⟩
      · have hn : ¬ (∀ x, G.Adj v x → ∃ b ∈ B, G.Adj x b) := fun h => hvB ((hsat v hX).mp h)
        push_neg at hn
        obtain ⟨x, hvx, hxb⟩ := hn
        have hxX : x ∈ X := by
          have := hbip v x hvx
          by_contra h
          exact hX (this.mpr h)
        exact ⟨x, (hI x).mpr (Or.inr ⟨hxX, hxb⟩), hvx⟩
