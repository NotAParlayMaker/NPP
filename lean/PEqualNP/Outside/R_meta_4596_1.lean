import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4596_1
    (cone : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 m C →
      ∃ R : Finset (Fin m), R.card ≤ C.size + 1 ∧
        ∀ x y : Fin m → Bool, (∀ i ∈ R, x i = y i) →
          PEqualNP.MetaComplexity.circuitFun m C x = PEqualNP.MetaComplexity.circuitFun m C y)
    (count : ∀ (N s : ℕ) (I : Fin N → Fin N → Prop) (P L : Finset (Fin N))
      (E : Finset (Fin N × Fin N)),
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      (∀ e ∈ E, I e.1 e.2 ∧ e.1 ∈ P ∧ e.2 ∈ L) →
      P.card + L.card ≤ s + 1 → s ≤ 4400 → E.card ≤ 24 * s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : PEqualNP.CircuitLowerBounds.Circuit)
      (x5 : Finset (Fin x2 × Fin x2)), (1 : ℕ) ≤ x1 →
      (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      (∀ (x9 : Fin (x2 + x2) → Bool),
        Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 →
        (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧
          x9 (Fin.natAdd x2 x12) = Bool.true) →
        PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x9 = Bool.false) →
      (∀ x10 ∈ x5, x3 x10.1 x10.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4
        fun (x12 : Fin (x2 + x2)) =>
          Decidable.decide (x12 = Fin.castAdd x2 x10.1 ∨ x12 = Fin.natAdd x2 x10.2)) = Bool.true) →
      x4.size ≤ (4400 : ℕ) → x5.card ≤ (24 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 x5 hq huniq hao hsound hE hsize
  obtain ⟨R, hR, hdep⟩ := cone (x2 + x2) x4 hao
  have hne : ∀ a b : Fin x2, Fin.castAdd x2 a ≠ Fin.natAdd x2 b := by
    intro a b h
    have := congrArg Fin.val h
    simp at this
    omega
  let P := Finset.univ.filter (fun p : Fin x2 => Fin.castAdd x2 p ∈ R)
  let L := Finset.univ.filter (fun l : Fin x2 => Fin.natAdd x2 l ∈ R)
  have hPL : P.card + L.card ≤ R.card := by
    have hdisj : Disjoint (P.image (Fin.castAdd x2)) (L.image (Fin.natAdd x2)) := by
      rw [Finset.disjoint_left]
      intro i hi hj
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hj
      exact hne a b hb.symm
    have hsub : P.image (Fin.castAdd x2) ∪ L.image (Fin.natAdd x2) ⊆ R := by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp ha).2
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp hb).2
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (Fin.castAdd_injective x2 x2),
      Finset.card_image_of_injective _ (Fin.natAdd_injective x2 x2)] at h1
    exact h1
  refine count x2 x4.size x3 P L x5 huniq ?_ (by omega) hsize
  intro e he
  obtain ⟨hI, hacc⟩ := hE e he
  refine ⟨hI, ?_, ?_⟩
  · -- the point of an accepted pair is read by the output
    by_contra hp
    have hp' : Fin.castAdd x2 e.1 ∉ R := by simpa [P] using hp
    have heq := hdep
      (fun i => decide (i = Fin.castAdd x2 e.1 ∨ i = Fin.natAdd x2 e.2))
      (fun i => decide (i = Fin.natAdd x2 e.2)) (by
        intro i hi
        have : i ≠ Fin.castAdd x2 e.1 := fun h => hp' (h ▸ hi)
        simp [this])
    have hfalse := hsound (fun i => decide (i = Fin.natAdd x2 e.2)) (by
        refine le_trans (Fintype.card_le_one_iff.mpr ?_) hq
        intro a b
        apply Subtype.ext
        have ha := a.2
        have hb := b.2
        simp only [decide_eq_true_eq] at ha hb
        exact (Fin.natAdd_injective x2 x2) (ha.trans hb.symm))
      (by
        rintro ⟨p, l, -, h1, -⟩
        simp only [decide_eq_true_eq] at h1
        exact hne p e.2 h1)
    rw [hacc] at heq
    rw [← heq] at hfalse
    exact Bool.noConfusion hfalse
  · -- the line of an accepted pair is read by the output
    by_contra hl
    have hl' : Fin.natAdd x2 e.2 ∉ R := by simpa [L] using hl
    have heq := hdep
      (fun i => decide (i = Fin.castAdd x2 e.1 ∨ i = Fin.natAdd x2 e.2))
      (fun i => decide (i = Fin.castAdd x2 e.1)) (by
        intro i hi
        have : i ≠ Fin.natAdd x2 e.2 := fun h => hl' (h ▸ hi)
        show decide (i = Fin.castAdd x2 e.1 ∨ i = Fin.natAdd x2 e.2) =
          decide (i = Fin.castAdd x2 e.1)
        exact decide_eq_decide.mpr (or_iff_left this))
    have hfalse := hsound (fun i => decide (i = Fin.castAdd x2 e.1)) (by
        refine le_trans (le_of_eq (Fintype.card_eq_zero_iff.mpr ⟨fun a => ?_⟩)) (Nat.zero_le _)
        have ha := a.2
        simp only [decide_eq_true_eq] at ha
        exact hne e.1 a.1 ha.symm)
      (by
        rintro ⟨p, l, -, -, h2⟩
        simp only [decide_eq_true_eq] at h2
        exact hne e.1 l h2.symm)
    rw [hacc] at heq
    rw [← heq] at hfalse
    exact Bool.noConfusion hfalse
