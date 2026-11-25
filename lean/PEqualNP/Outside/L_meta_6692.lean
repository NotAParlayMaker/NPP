import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6692

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6692

theorem PEqualNP.Outside.L_meta_6692 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)),   (0 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x6 : Fin x2), (x3 x6).card = x1 + (1 : ℕ)) →         (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x7 ∈ x3 x10 ∧ x8 ∈ x3 x10) →           (∀ (x8 : Fin x2),               have x9 : Finset (Fin x2) := {x9 : Fin x2 | x8 ∈ x3 x9};               x9.card = x1 + (1 : ℕ)) ∧             (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x11 ∈ x3 x8 ∧ x11 ∈ x3 x9) ∧               ∀ (x8 : Finset (Fin x2)),                 x8.card ≤ x1 →                   have x10 : Finset (Fin x2) := {x10 : Fin x2 | ∀ x11 ∈ x8, x10 ∉ x3 x11};                   x1 ≤ x10.card := by
  intro q n S hq hn hc hu
  have uni : ∀ p p' : Fin n, p ≠ p' → ∀ l l', p ∈ S l → p' ∈ S l → p ∈ S l' → p' ∈ S l' → l = l' := by
    intro p p' h l l' a b c d
    obtain ⟨m, _, hm⟩ := hu p p' h
    rw [hm l ⟨a, b⟩, hm l' ⟨c, d⟩]
  have deg : ∀ p : Fin n, (Finset.univ.filter fun l => p ∈ S l).card = q + 1 := by
    intro p
    have e : (Finset.univ.erase p : Finset (Fin n)) = (Finset.univ.filter fun l => p ∈ S l).biUnion fun l => (S l).erase p := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion, Finset.mem_filter, true_and]
      constructor
      · intro h
        obtain ⟨l, hl, _⟩ := hu p x (Ne.symm h)
        exact ⟨l, hl.1, h, hl.2⟩
      · rintro ⟨l, _, h, _⟩; exact h
    have c := congrArg Finset.card e
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, Finset.card_biUnion] at c
    · rw [Finset.sum_congr rfl (fun l hl => by rw [Finset.card_erase_of_mem (Finset.mem_filter.1 hl).2, hc l])] at c
      simp only [Nat.add_sub_cancel, Finset.sum_const, smul_eq_mul] at c
      have : (Finset.univ.filter fun l => p ∈ S l).card * q = (q + 1) * q := by
        rw [← c, hn]; ring_nf; omega
      exact Nat.eq_of_mul_eq_mul_right hq this
    · intro l hl l' hl' hne
      refine Finset.disjoint_left.2 fun x h1 h2 => hne ?_
      simp only [Finset.mem_erase] at h1 h2
      exact uni p x (Ne.symm h1.1) l l' (Finset.mem_filter.1 hl).2 h1.2 (Finset.mem_filter.1 hl').2 h2.2
  have meet : ∀ l l' : Fin n, l ≠ l' → ∃ p, p ∈ S l ∧ p ∈ S l' := by
    intro l l' hne
    have sub : ((S l).biUnion fun p => (Finset.univ.filter fun m => p ∈ S m).erase l) ⊆ Finset.univ.erase l := by
      intro x hx
      simp only [Finset.mem_biUnion, Finset.mem_erase] at hx
      obtain ⟨p, _, h, _⟩ := hx
      simp [h]
    have cd : ((S l).biUnion fun p => (Finset.univ.filter fun m => p ∈ S m).erase l).card = (q + 1) * q := by
      rw [Finset.card_biUnion]
      · rw [Finset.sum_congr rfl (fun p hp => by rw [Finset.card_erase_of_mem (by simpa using hp), deg p])]
        simp [hc l]
      · intro p hp p' hp' hne
        refine Finset.disjoint_left.2 fun x h1 h2 => ?_
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact h1.1 (uni p p' hne x l h1.2 h2.2 hp hp')
    have e := Finset.eq_of_subset_of_card_le sub (by
      rw [cd, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, hn]
      ring_nf; omega)
    have hm : l' ∈ (Finset.univ.erase l : Finset (Fin n)) := by simp [Ne.symm hne]
    rw [← e] at hm
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    obtain ⟨p, h1, _, h2⟩ := hm
    exact ⟨p, h1, h2⟩
  refine ⟨deg, ?_, ?_⟩
  · intro l l' hne
    obtain ⟨p, h1, h2⟩ := meet l l' hne
    refine ⟨p, ⟨h1, h2⟩, ?_⟩
    rintro p' ⟨h3, h4⟩
    by_contra h
    exact hne (uni p p' (Ne.symm h) l l' h1 h3 h2 h4)
  · have cov : ∀ Y : Finset (Fin n), (Y.biUnion S).card ≤ Y.card * q + 1 := by
      intro Y
      induction Y using Finset.induction_on with
      | empty => simp
      | @insert l Y hl ih =>
        rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hl]
        rcases Y.eq_empty_or_nonempty with rfl | ⟨m, hm⟩
        · simp [hc l]
        · obtain ⟨p, h1, h2⟩ := meet l m (fun h => hl (h ▸ hm))
          have hp : p ∈ S l ∩ Y.biUnion S := by
            simp only [Finset.mem_inter, Finset.mem_biUnion]
            exact ⟨h1, m, hm, h2⟩
          have c := Finset.card_union_add_card_inter (S l) (Y.biUnion S)
          have : 1 ≤ (S l ∩ Y.biUnion S).card := Finset.card_pos.2 ⟨p, hp⟩
          rw [hc l] at c
          rw [add_mul]
          omega
    intro Y hY
    have e : (Finset.univ.filter fun p => ∀ l ∈ Y, p ∉ S l) = Finset.univ \ Y.biUnion S := by
      ext x; simp
    simp only
    rw [e, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have c := cov Y
    have : Y.card * q ≤ q * q := Nat.mul_le_mul_right q hY
    have h2 : q ^ 2 = q * q := sq q
    omega
