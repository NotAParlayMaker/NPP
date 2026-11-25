import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7834

open Classical

private def delVertex {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin n) where
  Adj u w := G.Adj u w ∧ u ≠ v ∧ w ≠ v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

private theorem delVertex_le {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    delVertex G v ≤ G :=
  fun _ _ h => h.1

private theorem delVertex_support {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (s : Finset (Fin n)) (hs : G.support ⊆ (s : Set (Fin n))) :
    (delVertex G v).support ⊆ ((s.erase v : Finset (Fin n)) : Set (Fin n)) := by
  intro u hu
  rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]
  rcases hu with ⟨w, hw⟩
  exact ⟨hs ⟨w, hw.1⟩, hw.2.1⟩

private theorem edgeSet_le_delVertex_add {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    G.edgeSet.ncard ≤ (delVertex G v).edgeSet.ncard + (G.neighborSet v).ncard := by
  have hsub : G.edgeSet ⊆ (delVertex G v).edgeSet ∪ ((fun w => s(v, w)) '' G.neighborSet v) := by
    intro e he
    rcases e with ⟨a, b⟩
    have hadj : G.Adj a b := he
    by_cases ha : a = v
    · subst ha
      right
      exact ⟨b, hadj, rfl⟩
    · by_cases hb : b = v
      · subst hb
        right
        exact ⟨a, hadj.symm, Sym2.eq_swap⟩
      · left
        exact ⟨hadj, ha, hb⟩
  have h1 : G.edgeSet.ncard ≤ ((delVertex G v).edgeSet ∪ ((fun w => s(v, w)) '' G.neighborSet v)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ((delVertex G v).edgeSet ∪ ((fun w => s(v, w)) '' G.neighborSet v)).ncard ≤
      (delVertex G v).edgeSet.ncard + ((fun w => s(v, w)) '' G.neighborSet v).ncard :=
    Set.ncard_union_le _ _
  have h3 : ((fun w => s(v, w)) '' G.neighborSet v).ncard ≤ (G.neighborSet v).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  omega

private theorem aux {n : ℕ} (w : Fin n → ℕ) :
    ∀ (k : ℕ) (s : Finset (Fin n)) (G : SimpleGraph (Fin n)),
      s.card = k →
      G.support ⊆ (s : Set (Fin n)) →
      ∃ H ≤ G,
        (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ w v < (H.neighborSet v).ncard) ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard + ∑ v ∈ s, w v := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro s G hk hsupp
    by_cases hex : ∃ v : Fin n, 0 < (G.neighborSet v).ncard ∧ (G.neighborSet v).ncard ≤ w v
    · rcases hex with ⟨v, hpos, hle⟩
      have hne : (G.neighborSet v).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      rcases hne with ⟨u, hu⟩
      have hvs : v ∈ s := hsupp ⟨u, hu⟩
      have hcard_lt : (s.erase v).card < k := by
        rw [Finset.card_erase_of_mem hvs, hk]
        exact Nat.sub_lt (Finset.card_pos.mpr ⟨v, hvs⟩ |> fun hp => by omega) zero_lt_one
      obtain ⟨H, hHG', hdeg, hedges⟩ :=
        ih (s.erase v).card hcard_lt (s.erase v) (delVertex G v) rfl (delVertex_support G v s hsupp)
      refine ⟨H, hHG'.trans (delVertex_le G v), hdeg, ?_⟩
      have hsplit := edgeSet_le_delVertex_add G v
      have hsum : w v + ∑ x ∈ s.erase v, w x = ∑ x ∈ s, w x := Finset.add_sum_erase s w hvs
      omega
    · refine ⟨G, le_rfl, ?_, Nat.le_add_right _ _⟩
      intro v
      by_contra hbad
      apply hex
      exact ⟨v, by omega, by omega⟩

end PEqualNP.Outside.L_meta_7834

theorem PEqualNP.Outside.L_meta_7834 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : Fin x1 → ℕ),
      x2.support ⊆ ↑x3 →
      ∃ x6 ≤ x2,
        (∀ (x7 : Fin x1), (x6.neighborSet x7).ncard = (0 : ℕ) ∨ x4 x7 < (x6.neighborSet x7).ncard) ∧
        x2.edgeSet.ncard ≤ x6.edgeSet.ncard + ∑ x7 ∈ x3, x4 x7 := by
  intro x1 x2 x3 x4 hsupp
  exact PEqualNP.Outside.L_meta_7834.aux x4 x3.card x3 x2 rfl hsupp
