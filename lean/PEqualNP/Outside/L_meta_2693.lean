import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2693_aux

abbrev G : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]

theorem cover : ∀ s : Finset (Fin 11), (∀ v w : Fin 11, G.Adj v w → v ∈ s ∨ w ∈ s) → 7 ≤ s.card := by
  decide +kernel

theorem main : ∀ (x2 : Finset (Sym2 (Fin (11 : ℕ)))) (x3 : Finset (Fin (11 : ℕ))), (G.deleteEdges ↑x2).IsVertexCover ↑x3 → (7 : ℕ) ≤ x3.card + x2.card := by
  intro x2 x3 h
  have hc := cover (x3 ∪ x2.image (fun e => (Quot.out e).1)) (by
    intro v w hvw
    by_cases hm : s(v, w) ∈ x2
    · have h1 : (Quot.out s(v, w)).1 ∈ s(v, w) := Sym2.out_fst_mem _
      have h2 : (Quot.out s(v, w)).1 ∈ x2.image (fun e => (Quot.out e).1) :=
        Finset.mem_image_of_mem _ hm
      rcases Sym2.mem_iff.mp h1 with h3 | h3
      · left
        rw [← h3]
        exact Finset.mem_union_right _ h2
      · right
        rw [← h3]
        exact Finset.mem_union_right _ h2
    · have h1 : (G.deleteEdges ↑x2).Adj v w := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hvw, by simpa using hm⟩
      rcases h h1 with h3 | h3
      · left
        exact Finset.mem_union_left _ (by simpa using h3)
      · right
        exact Finset.mem_union_left _ (by simpa using h3))
  have h4 := Finset.card_union_le x3 (x2.image (fun e => (Quot.out e).1))
  have h5 : (x2.image (fun e => (Quot.out e).1)).card ≤ x2.card := Finset.card_image_le
  omega

end PEqualNP.Outside.L_meta_2693_aux

theorem PEqualNP.Outside.L_meta_2693 : have x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Finset (Sym2 (Fin (11 : ℕ)))) (x3 : Finset (Fin (11 : ℕ))), (x1.deleteEdges ↑x2).IsVertexCover ↑x3 → (7 : ℕ) ≤ x3.card + x2.card :=
  PEqualNP.Outside.L_meta_2693_aux.main
