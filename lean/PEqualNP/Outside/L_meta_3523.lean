import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3523 :
    ∀ (n m : ℕ) (edges matching : Finset (Fin n × Fin m)),
      matching ⊆ edges →
      (∀ p ∈ matching, ∀ q ∈ matching, p.1 = q.1 → p = q) →
      (∀ p ∈ matching, ∀ q ∈ matching, p.2 = q.2 → p = q) →
      ∃ G : SimpleGraph (Fin (n + m)),
        (∀ u v, G.Adj u v ↔
          ∃ p ∈ edges,
            u = Fin.castAdd m p.1 ∧ v = Fin.natAdd n p.2 ∨
            v = Fin.castAdd m p.1 ∧ u = Fin.natAdd n p.2) ∧
        G.edgeSet.ncard = edges.card ∧
        ∀ cover : Finset (Fin (n + m)),
          PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G cover →
          matching.card ≤ cover.card := by
  intro n m edges matching sub firstUnique secondUnique
  let left : Fin n → Fin (n + m) := Fin.castAdd m
  let right : Fin m → Fin (n + m) := Fin.natAdd n
  have leftInj : Function.Injective left := (Fin.castAddEmb m).injective
  have rightInj : Function.Injective right := (Fin.natAddEmb n).injective
  have different (i : Fin n) (j : Fin m) : left i ≠ right j := by
    intro eq
    have sameValue := congrArg Fin.val eq
    change i.val = n + j.val at sameValue
    have range := i.isLt
    omega
  let edge (p : Fin n × Fin m) : Sym2 (Fin (n + m)) := s(left p.1, right p.2)
  have edgeInj : Function.Injective edge := by
    intro p q eq
    change s(left p.1, right p.2) = s(left q.1, right q.2) at eq
    rcases Sym2.eq_iff.mp eq with ⟨hleft, hright⟩ | ⟨hcross, _⟩
    · exact Prod.ext (leftInj hleft) (rightInj hright)
    · exact (different p.1 q.2 hcross).elim
  let edgeImage := edge '' (edges : Set (Fin n × Fin m))
  let G := SimpleGraph.fromEdgeSet edgeImage
  have edgeSet : G.edgeSet = edgeImage := by
    change (SimpleGraph.fromEdgeSet edgeImage).edgeSet = edgeImage
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    apply Set.Subset.antisymm Set.sdiff_subset
    intro e he
    refine ⟨he, ?_⟩
    obtain ⟨p, _, rfl⟩ := he
    intro diagonal
    exact different p.1 p.2 (Sym2.mk_isDiag_iff.mp (Sym2.mem_diagSet.mp diagonal))
  have adj (u v : Fin (n + m)) : G.Adj u v ↔
      ∃ p ∈ edges,
        u = left p.1 ∧ v = right p.2 ∨ v = left p.1 ∧ u = right p.2 := by
    rw [← SimpleGraph.mem_edgeSet, edgeSet]
    constructor
    · rintro ⟨p, hp, eq⟩
      refine ⟨p, hp, ?_⟩
      rcases Sym2.eq_iff.mp eq.symm with straight | ⟨crossLeft, crossRight⟩
      · exact Or.inl straight
      · exact Or.inr ⟨crossRight, crossLeft⟩
    · rintro ⟨p, hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨p, hp, rfl⟩
      · exact ⟨p, hp, Sym2.eq_swap⟩
  refine ⟨G, adj, ?_, ?_⟩
  · rw [edgeSet]
    change (edge '' (edges : Set (Fin n × Fin m))).ncard = edges.card
    rw [Set.ncard_image_of_injective _ edgeInj, Set.ncard_coe_finset]
  · intro cover covers
    let endpoint (p : Fin n × Fin m) :=
      if left p.1 ∈ cover then left p.1 else right p.2
    apply Finset.card_le_card_of_injOn endpoint
    · intro p hp
      change endpoint p ∈ cover
      have covered := covers (left p.1) (right p.2)
        ((adj _ _).mpr ⟨p, sub hp, Or.inl ⟨rfl, rfl⟩⟩)
      by_cases h : left p.1 ∈ cover
      · simpa only [endpoint, ite_eq_left h] using h
      · simpa only [endpoint, ite_eq_right h] using covered.resolve_left h
    · intro p hp q hq eq
      by_cases hleft : left p.1 ∈ cover <;> by_cases hright : left q.1 ∈ cover
      · exact firstUnique p hp q hq
          (leftInj (by simpa only [endpoint, ite_eq_left hleft, ite_eq_left hright] using eq))
      · exact (different p.1 q.2
          (by simpa only [endpoint, ite_eq_left hleft, ite_eq_right hright] using eq)).elim
      · exact (different q.1 p.2
          (by simpa only [endpoint, ite_eq_right hleft, ite_eq_left hright] using eq.symm)).elim
      · exact secondUnique p hp q hq
          (rightInj (by simpa only [endpoint, ite_eq_right hleft, ite_eq_right hright] using eq))
