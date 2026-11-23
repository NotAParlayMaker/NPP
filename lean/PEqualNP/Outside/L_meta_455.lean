import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_455 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
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
  intro n G _ htri hC4 u v huv
  have side (p : Fin n) :
      ∀ a ∈ Finset.univ.filter (fun w => G.Adj p w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj p w), ¬ G.Adj a b := by
    intro a ha b hb hab
    have hpa : G.Adj p a := by simpa [Finset.mem_filter] using ha
    have hpb : G.Adj p b := by simpa [Finset.mem_filter] using hb
    exact htri a b p ⟨hab, G.adj_symm hpb, hpa⟩
  refine ⟨side v, side u, ?_⟩
  intro a ha b hb hab
  have hmem {x : Fin n}
      (hx : x ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v)) :
      (G.Adj v x ∧ x ≠ u) ∨ (G.Adj u x ∧ x ≠ v) := by
    simpa [Finset.mem_union, Finset.mem_filter] using hx
  rcases hmem ha with ⟨hva, hau⟩ | ⟨hua, hav⟩
  · rcases hmem hb with ⟨hvb, _⟩ | ⟨hub, hbv⟩
    · exact htri a b v ⟨hab, G.adj_symm hvb, hva⟩
    · exact hC4 u v a b (Ne.symm hau) (Ne.symm hbv) ⟨huv, hva, hab, G.adj_symm hub⟩
  · rcases hmem hb with ⟨hvb, hbu⟩ | ⟨hub, _⟩
    · exact hC4 u a b v (Ne.symm hbu) hav ⟨hua, hab, G.adj_symm hvb, G.adj_symm huv⟩
    · exact htri a b u ⟨hab, G.adj_symm hub, hua⟩
