import Mathlib
import PEqualNP.Defs

-- Two distinct lines meet in at most one point, so the other lines of the set cover at most
-- one point of the line each; the line has q + 1 points.
namespace PEqualNP.Outside.L_meta_4763

theorem meet_le_one {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (l m : Fin N) (hlm : m ≠ l) :
    (Finset.univ.filter (fun p => I p l ∧ I p m)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp p' hp'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
  by_contra hne
  obtain ⟨k, _, hk⟩ := huniq p p' hne
  have h1 := hk l ⟨hp.1, hp'.1⟩
  have h2 := hk m ⟨hp.2, hp'.2⟩
  exact hlm (h2.trans h1.symm)

end PEqualNP.Outside.L_meta_4763

theorem PEqualNP.Outside.L_meta_4763 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), ∀ x8 ∈ x7, x1 + (2 : ℕ) ≤ x7.card + Fintype.card { x10 : Fin x2 // x3 x10 x8 ∧ ∀ x11 ∈ x7.erase x8, ¬x3 x10 x11 } := by
  classical
  intro q N I _ hline huniq S l hl
  set P := Finset.univ.filter (fun p => I p l) with hP
  have hPc : P.card = q + 1 := by
    rw [hP, ← Fintype.card_subtype]; exact hline l
  set U := P.filter (fun p => ∀ m ∈ S.erase l, ¬ I p m) with hU
  set C := P.filter (fun p => ¬ ∀ m ∈ S.erase l, ¬ I p m) with hC
  have hsplit : C.card + U.card = P.card := by
    rw [hC, hU, add_comm]; exact Finset.card_filter_add_card_filter_not _
  have hCle : C.card ≤ (S.erase l).card := by
    have hsub : C ⊆ (S.erase l).biUnion (fun m => Finset.univ.filter (fun p => I p l ∧ I p m)) := by
      intro p hp
      simp only [hC, hP, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hp
      obtain ⟨hpl, m, hm, hpm⟩ := hp
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨m, hm, hpl, hpm⟩
    calc C.card ≤ ((S.erase l).biUnion (fun m => Finset.univ.filter (fun p => I p l ∧ I p m))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ m ∈ S.erase l, (Finset.univ.filter (fun p => I p l ∧ I p m)).card := Finset.card_biUnion_le
      _ ≤ ∑ m ∈ S.erase l, 1 := by
          apply Finset.sum_le_sum; intro m hm
          exact PEqualNP.Outside.L_meta_4763.meet_le_one I huniq l m (Finset.ne_of_mem_erase hm)
      _ = (S.erase l).card := by simp
  have hSe : (S.erase l).card + 1 = S.card := Finset.card_erase_add_one hl
  have hUc : Fintype.card {p : Fin N // I p l ∧ ∀ m ∈ S.erase l, ¬ I p m} = U.card := by
    rw [Fintype.card_subtype, hU, hP, Finset.filter_filter]
  rw [hUc]
  omega
