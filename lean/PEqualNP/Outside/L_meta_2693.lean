import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2693 : have x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Finset (Sym2 (Fin (11 : ℕ)))) (x3 : Finset (Fin (11 : ℕ))), (x1.deleteEdges ↑x2).IsVertexCover ↑x3 → (7 : ℕ) ≤ x3.card + x2.card := by
  dsimp only
  intro x2 x3 hvc
  classical
  let G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let pick : Sym2 (Fin 11) → Fin 11 := fun e => (Quot.out e).1
  let S : Finset (Fin 11) := x3 ∪ x2.image pick
  have hScard : S.card ≤ x3.card + x2.card :=
    le_trans (Finset.card_union_le x3 (x2.image pick)) (Nat.add_le_add_left Finset.card_image_le x3.card)
  have hcover : ∀ u v : Fin 11, G.Adj u v → u ∈ S ∨ v ∈ S := by
    intro u v hadj
    by_cases hmem : s(u, v) ∈ x2
    · have hp : pick s(u, v) ∈ S := Finset.mem_union_right x3 (Finset.mem_image_of_mem pick hmem)
      have hq : s((Quot.out s(u, v)).1, (Quot.out s(u, v)).2) = s(u, v) := Quot.out_eq s(u, v)
      rw [Sym2.eq_iff] at hq
      rcases hq with ⟨h1, _⟩ | ⟨h1, _⟩
      · left
        exact h1 ▸ hp
      · right
        exact h1 ▸ hp
    · have hadj' : (G.deleteEdges (x2 : Set (Sym2 (Fin 11)))).Adj u v := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hadj, hmem⟩
      rcases hvc hadj' with hu | hv
      · left
        exact Finset.mem_union_left _ hu
      · right
        exact Finset.mem_union_left _ hv
  let ind : Fin 11 → ℕ := fun v => if v ∈ S then 1 else 0
  have hedge : ∀ u v : Fin 11, G.Adj u v → 1 ≤ ind u + ind v := by
    intro u v hadj
    rcases hcover u v hadj with hu | hv
    · dsimp [ind]
      split_ifs <;> omega
    · dsimp [ind]
      split_ifs <;> omega
  have hsum : S.card = ∑ v : Fin 11, ind v := by
    rw [Finset.card_eq_sum_ones]
    have h1 : S = Finset.univ.filter (fun v : Fin 11 => v ∈ S) := by
      ext v
      simp
    rw [h1, Finset.sum_filter]
  have hsum' : ∑ v : Fin 11, ind v = ind 0 + (ind 1 + (ind 2 + (ind 3 + (ind 4 + (ind 5 + (ind 6 + (ind 7 + (ind 8 + (ind 9 + ind 10))))))))) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  have e14 : 1 ≤ ind 1 + ind 4 := hedge 1 4 (by decide)
  have e48 : 1 ≤ ind 4 + ind 8 := hedge 4 8 (by decide)
  have e18 : 1 ≤ ind 1 + ind 8 := hedge 1 8 (by decide)
  have e36 : 1 ≤ ind 3 + ind 6 := hedge 3 6 (by decide)
  have e67 : 1 ≤ ind 6 + ind 7 := hedge 6 7 (by decide)
  have e37 : 1 ≤ ind 3 + ind 7 := hedge 3 7 (by decide)
  have e09 : 1 ≤ ind 0 + ind 9 := hedge 0 9 (by decide)
  have e95 : 1 ≤ ind 9 + ind 5 := hedge 9 5 (by decide)
  have e52 : 1 ≤ ind 5 + ind 2 := hedge 5 2 (by decide)
  have e2a : 1 ≤ ind 2 + ind 10 := hedge 2 10 (by decide)
  have ea0 : 1 ≤ ind 10 + ind 0 := hedge 10 0 (by decide)
  omega
