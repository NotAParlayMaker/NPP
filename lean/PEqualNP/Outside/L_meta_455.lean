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
  intro n G _ noTriangle noSquare u v huv
  have oneSide (s a b : Fin n) (ha : G.Adj s a) (hb : G.Adj s b) :
      ¬ G.Adj a b :=
    fun hab => noTriangle s a b ⟨ha, hab, hb.symm⟩
  have across (a b : Fin n) (ha : G.Adj v a ∧ a ≠ u) (hb : G.Adj u b ∧ b ≠ v) :
      ¬ G.Adj a b :=
    fun hab => noSquare u v a b ha.2.symm hb.2.symm ⟨huv, ha.1, hab, hb.1.symm⟩
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun a ha b hb => oneSide v a b ha hb, fun a ha b hb => oneSide u a b ha hb, ?_⟩
  intro a ha b hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact oneSide v a b ha.1 hb.1
  · exact across a b ha hb
  · exact fun hab => across b a hb ha hab.symm
  · exact oneSide u a b ha.1 hb.1
