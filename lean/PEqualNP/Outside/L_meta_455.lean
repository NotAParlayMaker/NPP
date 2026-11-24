import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_455

theorem adj_symm {n : ℕ} (G : SimpleGraph (Fin n)) {a b : Fin n} (h : G.Adj a b) :
    G.Adj b a := by
  rw [G.adj_comm] at h
  exact h

theorem no_adj_in_nbr_filter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (x : Fin n) :
    ∀ a ∈ Finset.univ.filter (fun w => G.Adj x w),
      ∀ b ∈ Finset.univ.filter (fun w => G.Adj x w), ¬ G.Adj a b := by
  intro a ha b hb hab
  simp only [Finset.mem_filter] at ha hb
  exact h3 x a b ⟨ha.2, hab, adj_symm G hb.2⟩

theorem no_adj_in_union_nbr_filter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    {u v : Fin n} (huv : G.Adj u v) :
    ∀ a ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
            Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v),
      ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
            Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v), ¬ G.Adj a b := by
  intro a ha b hb hab
  simp only [Finset.mem_union, Finset.mem_filter] at ha hb
  rcases ha with ⟨_, hva, hau⟩ | ⟨_, hua, hav⟩
  · rcases hb with ⟨_, hvb, _⟩ | ⟨_, hub, hbv⟩
    · exact h3 v a b ⟨hva, hab, adj_symm G hvb⟩
    · exact h4 u v a b (Ne.symm hau) (Ne.symm hbv) ⟨huv, hva, hab, adj_symm G hub⟩
  · rcases hb with ⟨_, hvb, hbu⟩ | ⟨_, hub, _⟩
    · exact h4 u v b a (Ne.symm hbu) (Ne.symm hav) ⟨huv, hvb, adj_symm G hab, adj_symm G hua⟩
    · exact h3 u a b ⟨hua, hab, adj_symm G hub⟩

end PEqualNP.Outside.L_meta_455

theorem PEqualNP.Outside.L_meta_455 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) →
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
    ∀ u v : Fin n, G.Adj u v →
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj u w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj u w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v), ¬ G.Adj a b) := by
  intro n G _ h3 h4 u v huv
  refine ⟨?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_455.no_adj_in_nbr_filter G h3 v
  · exact PEqualNP.Outside.L_meta_455.no_adj_in_nbr_filter G h3 u
  · exact PEqualNP.Outside.L_meta_455.no_adj_in_union_nbr_filter G h3 h4 huv
