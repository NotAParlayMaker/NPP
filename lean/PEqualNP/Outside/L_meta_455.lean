import Mathlib.Combinatorics.SimpleGraph.Basic
import PEqualNP.Defs

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
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    exact h3 v a b ⟨ha.2, hab, hb.2.symm⟩
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    exact h3 u a b ⟨ha.2, hab, hb.2.symm⟩
  · intro a ha b hb hab
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at ha hb
    rcases ha with ⟨_, hva, hau⟩ | ⟨_, hua, hav⟩ <;>
      rcases hb with ⟨_, hvb, hbu⟩ | ⟨_, hub, hbv⟩
    · exact h3 v a b ⟨hva, hab, hvb.symm⟩
    · exact h4 u v a b (Ne.symm hau) (Ne.symm hbv) ⟨huv, hva, hab, hub.symm⟩
    · exact h4 v u a b (Ne.symm hav) (Ne.symm hbu) ⟨huv.symm, hua, hab, hvb.symm⟩
    · exact h3 u a b ⟨hua, hab, hub.symm⟩
