import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_157 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
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
  intro n G _ noTriangle noSquare u v huv
  have independent (w a b : Fin n) (ha : G.Adj w a) (hb : G.Adj w b) :
      ¬ G.Adj a b := by
    intro hab
    exact noTriangle w a b ⟨ha, hab, hb.symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    exact independent v a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  · intro a ha b hb
    exact independent u a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  · intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact independent v a b (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp hb).2.1 hab
    · have ⟨hva, hau⟩ := (Finset.mem_filter.mp ha).2
      have ⟨hub, hbv⟩ := (Finset.mem_filter.mp hb).2
      exact noSquare u v a b (Ne.symm hau) (Ne.symm hbv) ⟨huv, hva, hab, hub.symm⟩
    · have ⟨hua, hav⟩ := (Finset.mem_filter.mp ha).2
      have ⟨hvb, hbu⟩ := (Finset.mem_filter.mp hb).2
      exact noSquare v u a b (Ne.symm hav) (Ne.symm hbu) ⟨huv.symm, hua, hab, hvb.symm⟩
    · exact independent u a b (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp hb).2.1 hab
