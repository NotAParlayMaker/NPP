import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1466_aux

private theorem extend {q n m : ℕ}
    (L : Fin (m + 1) → Finset (Fin n)) (X A : Finset (Fin n))
    (hq : 2 ≤ q) (hL : ∀ i, (L i).card = q + 1)
    (hcap : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hpair : ∀ p p' : Fin n, p ≠ p' → ∃ i, p ∈ L i ∧ p' ∈ L i)
    (hX : 15 * q ≤ X.card + 8) (hAX : A ⊆ X) (hA : A.card ≤ 6)
    (hArc : ∀ i, (L i ∩ A).card ≤ 2) :
    ∃ B : Finset (Fin n), B ⊆ X ∧ B.card = A.card + 1 ∧ ∀ i, (L i ∩ B).card ≤ 2 := by
  classical
  have locate : ∀ P : Finset (Fin n), P.card = 2 → ∃ i, P ⊆ L i := by
    intro P hP
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hP
    obtain ⟨i, hx, hy⟩ := hpair x y hxy
    refine ⟨i, ?_⟩
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hx
    · simpa only [Finset.mem_singleton.mp hp] using hy
  let line (P : Finset (Fin n)) : Fin (m + 1) :=
    if hP : P.card = 2 then Classical.choose (locate P hP) else 0
  let pairs := A.powersetCard 2
  let removed (P : Finset (Fin n)) := L (line P) \ A
  let forbidden := A ∪ pairs.biUnion removed
  have lineSub (P : Finset (Fin n)) (hp : P.card = 2) : P ⊆ L (line P) := by
    simpa only [line, dif_pos hp] using Classical.choose_spec (locate P hp)
  have removedBound (P : Finset (Fin n)) (hp : P ∈ pairs) : (removed P).card ≤ q - 1 := by
    obtain ⟨hpa, hpc⟩ := Finset.mem_powersetCard.mp hp
    calc
      (removed P).card ≤ (L (line P) \ P).card :=
        Finset.card_le_card (Finset.sdiff_subset_sdiff_right (L (line P)) hpa)
      _ = q - 1 := by rw [Finset.card_sdiff_of_subset (lineSub P hpc), hL, hpc]; omega
  have pairsBound : pairs.card ≤ 15 := by
    rw [Finset.card_powersetCard]
    exact (Nat.choose_le_choose 2 hA).trans (by decide)
  have unionBound : (pairs.biUnion removed).card ≤ 15 * (q - 1) := by
    calc
      (pairs.biUnion removed).card ≤ ∑ P ∈ pairs, (removed P).card := Finset.card_biUnion_le
      _ ≤ ∑ _P ∈ pairs, (q - 1) := Finset.sum_le_sum removedBound
      _ = pairs.card * (q - 1) := by simp
      _ ≤ 15 * (q - 1) := Nat.mul_le_mul_right _ pairsBound
  have strict : forbidden.card < X.card := by
    have b1 := (Finset.card_union_le A (pairs.biUnion removed)).trans
      (Nat.add_le_add hA unionBound)
    change forbidden.card ≤ 6 + 15 * (q - 1) at b1
    omega
  obtain ⟨x, hxX, hxF⟩ := Finset.exists_mem_notMem_of_card_lt_card strict
  have hxA : x ∉ A := fun h => hxF (Finset.mem_union_left _ h)
  refine ⟨insert x A, ?_, Finset.card_insert_of_notMem hxA, ?_⟩
  · exact Finset.insert_subset hxX hAX
  intro i
  by_contra! hbig
  have sub : L i ∩ insert x A ⊆ insert x (L i ∩ A) := by
    intro y hy
    obtain ⟨hyL, hyin⟩ := Finset.mem_inter.mp hy
    rcases Finset.mem_insert.mp hyin with rfl | hyA
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hyL,hyA⟩)
  have cap := (Finset.card_le_card sub).trans (Finset.card_insert_le x _)
  have hTwo : (L i ∩ A).card = 2 := by have := hArc i; omega
  have hxL : x ∈ L i := by
    by_contra hx
    have sub' : L i ∩ insert x A ⊆ L i ∩ A := by
      intro y hy
      obtain ⟨hyL, hyin⟩ := Finset.mem_inter.mp hy
      rcases Finset.mem_insert.mp hyin with rfl | hyA
      · exact False.elim (hx hyL)
      · exact Finset.mem_inter.mpr ⟨hyL,hyA⟩
    exact (not_lt_of_ge ((Finset.card_le_card sub').trans (hArc i))) hbig
  let P := L i ∩ A
  have hp : P ∈ pairs := Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hTwo⟩
  have same : i = line P := by
    by_contra h
    have both : P ⊆ L i ∩ L (line P) :=
      Finset.subset_inter Finset.inter_subset_left (lineSub P hTwo)
    have count := Finset.card_le_card both
    rw [hcap i (line P) h] at count
    change P.card = 2 at hTwo
    omega
  exact hxF (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨P, hp, Finset.mem_sdiff.mpr ⟨same ▸ hxL, hxA⟩⟩))

end PEqualNP.Outside.L_meta_1466_aux

open PEqualNP.Outside.L_meta_1466_aux in
theorem PEqualNP.Outside.L_meta_1466 :
    ∀ (q : ℕ) (L : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1)))
    (X : Finset (Fin (q ^ 2 + q + 1))),
    2 ≤ q → (∀ i, (L i).card = q + 1) → (∀ i j, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin (q ^ 2 + q + 1), p ≠ p' → ∃ i, p ∈ L i ∧ p' ∈ L i) →
    15 * q ≤ X.card + 8 →
    ∃ A : Finset (Fin (q ^ 2 + q + 1)), A ⊆ X ∧ A.card = 7 ∧ ∀ i, (L i ∩ A).card ≤ 2 := by
  intro q L X hq hL hcap hpair hX
  have all : ∀ k : ℕ, k ≤ 7 →
      ∃ A : Finset _, A ⊆ X ∧ A.card = k ∧ ∀ i, (L i ∩ A).card ≤ 2 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨∅, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨A, hAX, hA, hArc⟩ := ih (by omega)
      obtain ⟨B, hBX, hB, hBArc⟩ := extend L X A hq hL hcap hpair hX hAX (by omega) hArc
      exact ⟨B, hBX, by omega, hBArc⟩
  exact all 7 (by decide)
