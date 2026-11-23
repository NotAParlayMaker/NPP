import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_733 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (X : Set (Fin n)),
  (∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X)) →
  ∀ I : Set (Fin n),
    ((∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u)) ↔
    ∃ B : Set (Fin n), (∀ b ∈ B, b ∉ X) ∧
      (∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) ↔ y ∈ B)) ∧
      ∀ v, v ∈ I ↔ (v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)) := by
  classical
  intro n G X side I
  constructor
  · rintro ⟨indep, maximal⟩
    let B := I \ X
    have left (x : Fin n) (hx : x ∈ X) :
        x ∈ I ↔ ∀ b ∈ B, ¬ G.Adj x b := by
      constructor
      · intro hi b hb
        exact indep x hi b hb.1
      · intro avoids
        by_contra missing
        obtain ⟨b, hi, edge⟩ := maximal x missing
        exact avoids b ⟨hi, (side x b edge).mp hx⟩ edge
    refine ⟨B, fun _ hb => hb.2, ?_, ?_⟩
    · intro y hy
      constructor
      · intro cover
        refine ⟨?_, hy⟩
        by_contra missing
        obtain ⟨x, hx, edge⟩ := maximal y missing
        obtain ⟨b, hb, xb⟩ := cover x edge
        exact indep x hx b hb.1 xb
      · intro hb x edge
        exact ⟨y, hb, edge.symm⟩
    · intro v
      constructor
      · intro hv
        by_cases hx : v ∈ X
        · exact Or.inr ⟨hx, (left v hx).mp hv⟩
        · exact Or.inl ⟨hv, hx⟩
      · rintro (hb | ⟨hx, avoids⟩)
        · exact hb.1
        · exact (left v hx).mpr avoids
  · rintro ⟨B, outside, saturated, members⟩
    constructor
    · intro u hu v hv edge
      rcases (members u).mp hu with bu | ⟨ux, avoids⟩
      · have vx := (side v u edge.symm).mpr (outside u bu)
        rcases (members v).mp hv with bv | ⟨_, avoids⟩
        · exact outside v bv vx
        · exact avoids u bu edge.symm
      · rcases (members v).mp hv with bv | ⟨vx, _⟩
        · exact avoids v bv edge
        · exact (side u v edge).mp ux vx
    · intro v missing
      by_cases vx : v ∈ X
      · have neighbor : ∃ b ∈ B, G.Adj v b := by
          by_contra! avoids
          exact missing ((members v).mpr (Or.inr ⟨vx, avoids⟩))
        obtain ⟨b, hb, edge⟩ := neighbor
        exact ⟨b, (members b).mpr (Or.inl hb), edge⟩
      · have vb : v ∉ B := fun hb => missing ((members v).mpr (Or.inl hb))
        have neighbor : ∃ x, G.Adj v x ∧ ∀ b ∈ B, ¬ G.Adj x b := by
          by_contra! cover
          exact vb ((saturated v vx).mp cover)
        obtain ⟨x, edge, avoids⟩ := neighbor
        exact ⟨x, (members x).mpr (Or.inr ⟨(side x v edge.symm).mpr vx, avoids⟩), edge⟩
