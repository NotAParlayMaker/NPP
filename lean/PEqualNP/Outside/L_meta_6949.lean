import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6949
open PEqualNP.CircuitLowerBounds



theorem minEq {n : ℕ} (F G : Finset (Finset (Fin n))) (hGF : G ⊆ F)
    (hdom : ∀ T ∈ F, ∃ M ∈ G, M ⊆ T) :
    F.filter (fun S => ∀ T ∈ F, T ⊆ S → S ⊆ T) = G.filter (fun S => ∀ T ∈ G, T ⊆ S → S ⊆ T) := by
  ext X
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hX, hmin⟩
    obtain ⟨M, hM, hMX⟩ := hdom X hX
    have hXM : X = M := Finset.Subset.antisymm (hmin M (hGF hM) hMX) hMX
    exact ⟨hXM ▸ hM, fun T hT hTX => hmin T (hGF hT) hTX⟩
  · rintro ⟨hX, hmin⟩
    refine ⟨hGF hX, fun T hT hTX => ?_⟩
    obtain ⟨M, hM, hMT⟩ := hdom T hT
    exact (hmin M hM (hMT.trans hTX)).trans hMT

theorem below {n : ℕ} (F : Finset (Finset (Fin n))) : ∀ k (S : Finset (Fin n)), S.card = k →
    S ∈ F → ∃ M ∈ F.filter (fun S => ∀ T ∈ F, T ⊆ S → S ⊆ T), M ⊆ S := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S hk hS
    by_cases hmin : ∀ T ∈ F, T ⊆ S → S ⊆ T
    · exact ⟨S, Finset.mem_filter.2 ⟨hS, hmin⟩, Finset.Subset.refl _⟩
    · push_neg at hmin
      obtain ⟨T, hT, hTS, hnot⟩ := hmin
      have hlt : T.card < S.card := Finset.card_lt_card ⟨hTS, hnot⟩
      obtain ⟨M, hM, hMT⟩ := ih T.card (hk ▸ hlt) T rfl hT
      exact ⟨M, hM, hMT.trans hTS⟩

end PEqualNP.Outside.L_meta_6949

open PEqualNP.Outside.L_meta_6949 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6949 : ∀ (x1 : ℕ) (x2 x3 : Finset (Finset (Fin x1))),   have x4 : Finset (Finset (Fin x1)) → Finset (Finset (Fin x1)) := fun (x4 : Finset (Finset (Fin x1))) => {x5 ∈ x4 | ∀ x6 ∈ x4, x6 ⊆ x5 → x5 ⊆ x6};   x4 (x2 ∪ x3) = x4 (x4 x2 ∪ x4 x3) ∧ x4 (x2.biUnion fun (x5 : Finset (Fin x1)) => Finset.image (fun (x6 : Finset (Fin x1)) => x5 ∪ x6) x3) = x4 ((x4 x2).biUnion fun (x5 : Finset (Fin x1)) => Finset.image (fun (x6 : Finset (Fin x1)) => x5 ∪ x6) (x4 x3)) := by
  intro n A B m
  constructor
  · exact minEq (A ∪ B) (m A ∪ m B)
      (Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _)) (by
      intro T hT
      rcases Finset.mem_union.1 hT with h | h
      · obtain ⟨M, hM, hMT⟩ := below A _ T rfl h
        exact ⟨M, Finset.mem_union_left _ hM, hMT⟩
      · obtain ⟨M, hM, hMT⟩ := below B _ T rfl h
        exact ⟨M, Finset.mem_union_right _ hM, hMT⟩)
  · exact minEq (A.biUnion fun a => B.image fun b => a ∪ b)
      ((m A).biUnion fun a => (m B).image fun b => a ∪ b) (by
      intro X hX
      obtain ⟨a, ha, hX'⟩ := Finset.mem_biUnion.1 hX
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hX'
      exact Finset.mem_biUnion.2 ⟨a, (Finset.mem_filter.1 ha).1,
        Finset.mem_image.2 ⟨b, (Finset.mem_filter.1 hb).1, rfl⟩⟩) (by
      intro T hT
      obtain ⟨a, ha, hT'⟩ := Finset.mem_biUnion.1 hT
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hT'
      obtain ⟨Ma, hMa, hMaa⟩ := below A _ a rfl ha
      obtain ⟨Mb, hMb, hMbb⟩ := below B _ b rfl hb
      exact ⟨Ma ∪ Mb, Finset.mem_biUnion.2 ⟨Ma, hMa, Finset.mem_image.2 ⟨Mb, hMb, rfl⟩⟩,
        Finset.union_subset_union hMaa hMbb⟩)
