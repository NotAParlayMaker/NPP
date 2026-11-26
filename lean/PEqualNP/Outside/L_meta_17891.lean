import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17891_aux

theorem tri (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] (h1 : p ∨ q) (h2 : p ∨ r) (h3 : q ∨ r) :
    2 ≤ (if p then 1 else 0) + (if q then 1 else 0) + (if r then 1 else 0) := by
  split_ifs <;> tauto

theorem pent (a b c d e : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d] [Decidable e]
    (h1 : a ∨ b) (h2 : b ∨ c) (h3 : c ∨ d) (h4 : d ∨ e) (h5 : e ∨ a) :
    3 ≤ (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) + (if d then 1 else 0) + (if e then 1 else 0) := by
  split_ifs <;> tauto

end PEqualNP.Outside.L_meta_17891_aux

open PEqualNP.Outside.L_meta_17891_aux in
theorem PEqualNP.Outside.L_meta_17891 : have x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Finset (Sym2 (Fin (11 : ℕ)))) (x3 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (x1.deleteEdges ↑x2) x3 → (7 : ℕ) ≤ x3.card + x2.card := by
  intro x1
  simp only [x1]
  intro D S hS
  set G := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] with hG
  let f : Sym2 (Fin 11) → Fin 11 := Sym2.lift ⟨fun a b => min a b, fun a b => min_comm a b⟩
  have hc : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G (S ∪ D.image f) := by
    intro u v huv
    by_cases hd : s(u, v) ∈ D
    · have hm : f s(u, v) ∈ D.image f := Finset.mem_image_of_mem f hd
      have : f s(u, v) = min u v := rfl
      rcases min_choice u v with h | h
      · left; rw [Finset.mem_union]; right; rw [← h, ← this]; exact hm
      · right; rw [Finset.mem_union]; right; rw [← h, ← this]; exact hm
    · have h2 : (G.deleteEdges ↑D).Adj u v := by
        rw [SimpleGraph.deleteEdges_adj]; exact ⟨huv, by simpa using hd⟩
      rcases hS u v h2 with h | h
      · left; exact Finset.mem_union_left _ h
      · right; exact Finset.mem_union_left _ h
  have hcard : (S ∪ D.image f).card ≤ S.card + D.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  suffices h7 : 7 ≤ (S ∪ D.image f).card by omega
  generalize S ∪ D.image f = T at hc
  have e : ∀ a b : Fin 11, G.Adj a b → a ∈ T ∨ b ∈ T := fun a b h => hc a b h
  have t1 := tri _ _ _ (e 1 4 (by decide)) (e 1 8 (by decide)) (e 4 8 (by decide))
  have t2 := tri _ _ _ (e 3 6 (by decide)) (e 3 7 (by decide)) (e 6 7 (by decide))
  have t3 := pent _ _ _ _ _ (e 0 9 (by decide)) (e 9 5 (by decide)) (e 5 2 (by decide)) (e 2 10 (by decide)) (e 10 0 (by decide))
  have hT : T.card = ∑ i : Fin 11, if i ∈ T then 1 else 0 := by
    rw [← Finset.card_filter]; congr 1; ext; simp
  rw [hT]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc] at *
  omega
