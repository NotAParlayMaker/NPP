import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_733 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (X : Set (Fin n)),
  (∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X)) →
  ∀ I : Set (Fin n),
    ((∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u)) ↔
    ∃ B : Set (Fin n), (∀ b ∈ B, b ∉ X) ∧
      (∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) ↔ y ∈ B)) ∧
      ∀ v, v ∈ I ↔ (v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)) := by
  intro n G X hX I
  constructor
  · rintro ⟨hind, hdom⟩
    refine ⟨{v | v ∈ I ∧ v ∉ X}, fun b hb => hb.2, ?_, ?_⟩
    · intro y hy
      constructor
      · intro h
        refine ⟨?_, hy⟩
        by_contra hyI
        obtain ⟨u, huI, hadj⟩ := hdom y hyI
        have huX : u ∈ X := by
          by_contra huX
          exact hy ((hX y u hadj).mpr huX)
        obtain ⟨b, hb, hub⟩ := h u hadj
        exact hind u huI b hb.1 hub
      · intro hyB x hadj
        exact ⟨y, hyB, hadj.symm⟩
    · intro v
      constructor
      · intro hv
        by_cases hvX : v ∈ X
        · exact Or.inr ⟨hvX, fun b hb => hind v hv b hb.1⟩
        · exact Or.inl ⟨hv, hvX⟩
      · rintro (hv | ⟨hvX, hno⟩)
        · exact hv.1
        · by_contra hvI
          obtain ⟨u, huI, hadj⟩ := hdom v hvI
          have huX : u ∉ X := (hX v u hadj).mp hvX
          exact hno u ⟨huI, huX⟩ hadj
  · rintro ⟨B, hB1, hB2, hB3⟩
    constructor
    · intro u hu v hv hadj
      rcases (hB3 u).mp hu with huB | ⟨huX, hun⟩
      · rcases (hB3 v).mp hv with hvB | ⟨hvX, hvn⟩
        · exact hB1 u huB ((hX u v hadj).mpr (hB1 v hvB))
        · exact hvn u huB hadj.symm
      · rcases (hB3 v).mp hv with hvB | ⟨hvX, hvn⟩
        · exact hun v hvB hadj
        · exact (hX u v hadj).mp huX hvX
    · intro v hv
      have hvB : v ∉ B := fun h => hv ((hB3 v).mpr (Or.inl h))
      by_cases hvX : v ∈ X
      · have h1 : ¬ ∀ b ∈ B, ¬ G.Adj v b := fun h => hv ((hB3 v).mpr (Or.inr ⟨hvX, h⟩))
        push_neg at h1
        obtain ⟨b, hb, hadj⟩ := h1
        exact ⟨b, (hB3 b).mpr (Or.inl hb), hadj⟩
      · have h2 : ¬ ∀ x, G.Adj v x → ∃ b ∈ B, G.Adj x b := fun h => hvB ((hB2 v hvX).mp h)
        push_neg at h2
        obtain ⟨x, hadj, hx⟩ := h2
        have hxX : x ∈ X := by
          by_contra hxX
          exact hvX ((hX v x hadj).mpr hxX)
        exact ⟨x, (hB3 x).mpr (Or.inr ⟨hxX, hx⟩), hadj⟩
