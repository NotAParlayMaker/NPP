import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Basis.Defs


theorem PEqualNP.Outside.L_meta_452 :
    ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  intro k m r hne hdep
  classical
  -- `A` collects the "essential" indices: those whose vector is not in the span of the others.
  set A := {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} with hA
  haveI : Fintype A := Fintype.ofFinite A
  -- `V` is the span of the whole family.
  set V : Submodule ℚ (Fin m → ℚ) := Submodule.span ℚ (Set.range r) with hV
  have hmemV : ∀ i : Fin k, r i ∈ V := by
    intro i
    rw [hV]
    exact Submodule.subset_span ⟨i, rfl⟩
  let v : A → V := fun a => ⟨r a.1, hmemV a.1⟩
  -- Coercion of a finite linear combination from `V` down to `Fin m → ℚ`.
  have hcoe : ∀ (s : Finset A) (g : A → ℚ),
      ((∑ a ∈ s, g a • v a : V) : Fin m → ℚ) = ∑ a ∈ s, g a • r a.1 := by
    intro s g
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [Submodule.coe_smul]

  -- Step 1: the family `v` indexed by `A` is linearly independent.
  have hind : LinearIndependent ℚ v := by
    rw [linearIndependent_iff']
    intro s g hsum a₀ ha₀
    by_contra hg
    have hsum' : ∑ a ∈ s, g a • r a.1 = 0 := by
      have h4 : ((∑ a ∈ s, g a • v a : V) : Fin m → ℚ) = 0 := by
        rw [hsum]
        rfl
      rw [hcoe s g] at h4
      exact h4
    -- the tail sum lies in the span of all vectors except `r a₀`
    have hT : (∑ a ∈ s.erase a₀, g a • r a.1) ∈
        Submodule.span ℚ (r '' {l : Fin k | l ≠ a₀.1}) := by
      apply Submodule.sum_mem
      intro a ha
      have hane : a ≠ a₀ := (Finset.mem_erase.mp ha).1
      have hane' : a.1 ≠ a₀.1 := fun h => hane (Subtype.ext h)
      have hmem : r a.1 ∈ r '' {l : Fin k | l ≠ a₀.1} := ⟨a.1, hane', rfl⟩
      exact Submodule.smul_mem _ (g a) (Submodule.subset_span hmem)
    have hsplit : (∑ a ∈ s.erase a₀, g a • r a.1) + g a₀ • r a₀.1 = 0 := by
      rw [Finset.sum_erase_add _ _ ha₀]
      exact hsum'
    have h1 : g a₀ • r a₀.1 = -(∑ a ∈ s.erase a₀, g a • r a.1) := by
      refine eq_neg_of_add_eq_zero_left ?_
      rw [add_comm]
      exact hsplit
    have h2 : r a₀.1 = (g a₀)⁻¹ • (g a₀ • r a₀.1) := (inv_smul_smul₀ hg (r a₀.1)).symm
    refine a₀.2 ?_
    rw [h2, h1]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hT)

  -- Step 2: the span of `v` is a proper submodule of `V`.
  have hspan_ne : Submodule.span ℚ (Set.range v) ≠ ⊤ := by
    intro htop
    obtain ⟨j, hj⟩ := hdep
    -- `j` is not essential
    have hja : ∀ a : A, a.1 ≠ j := by
      intro a ha
      exact a.2 (by rwa [← ha] at hj)
    have hjV : (⟨r j, hmemV j⟩ : V) ∈ Submodule.span ℚ (Set.range v) := by
      simp [htop]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℚ)).mp hjV
    have hc' : ∑ a : A, c a • r a.1 = r j := by
      have h4 : ((∑ a : A, c a • v a : V) : Fin m → ℚ) = r j := by
        rw [hc]
      have h5 : ((∑ a : A, c a • v a : V) : Fin m → ℚ) = ∑ a : A, c a • r a.1 :=
        hcoe Finset.univ c
      rw [h5] at h4
      exact h4
    by_cases hex : ∃ a : A, c a ≠ 0
    · obtain ⟨a₀, hc₀⟩ := hex
      have hja₀ : j ≠ a₀.1 := (hja a₀).symm
      have hTmem : (∑ a ∈ (Finset.univ : Finset A).erase a₀, c a • r a.1) ∈
          Submodule.span ℚ (r '' {l : Fin k | l ≠ a₀.1}) := by
        apply Submodule.sum_mem
        intro a ha
        have hane : a ≠ a₀ := (Finset.mem_erase.mp ha).1
        have hane' : a.1 ≠ a₀.1 := fun h => hane (Subtype.ext h)
        have hmem : r a.1 ∈ r '' {l : Fin k | l ≠ a₀.1} := ⟨a.1, hane', rfl⟩
        exact Submodule.smul_mem _ (c a) (Submodule.subset_span hmem)
      have hrj : r j ∈ Submodule.span ℚ (r '' {l : Fin k | l ≠ a₀.1}) :=
        Submodule.subset_span ⟨j, hja₀, rfl⟩
      have hsplit : (∑ a ∈ (Finset.univ : Finset A).erase a₀, c a • r a.1) + c a₀ • r a₀.1 = r j := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ a₀)]
        exact hc'
      have h1 : c a₀ • r a₀.1 =
          r j - (∑ a ∈ (Finset.univ : Finset A).erase a₀, c a • r a.1) := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact hsplit
      have h2 : r a₀.1 = (c a₀)⁻¹ •
          (r j - (∑ a ∈ (Finset.univ : Finset A).erase a₀, c a • r a.1)) := by
        rw [← h1]
        exact (inv_smul_smul₀ hc₀ (r a₀.1)).symm
      refine a₀.2 ?_
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hrj hTmem)
    · simp only [not_exists, not_not] at hex
      have hzero : r j = 0 := by
        rw [← hc']
        simp [hex]
      exact hne j hzero

  -- Step 3: dimension count.
  have hlt : Module.finrank ℚ (Submodule.span ℚ (Set.range v)) < Module.finrank ℚ V := by
    have h := Submodule.finrank_lt_finrank_of_lt (s := Submodule.span ℚ (Set.range v)) (t := ⊤)
      (lt_of_le_of_ne le_top hspan_ne)
    rwa [finrank_top] at h
  have hcard : Module.finrank ℚ (Submodule.span ℚ (Set.range v)) = Fintype.card A :=
    finrank_span_eq_card hind
  have hfinal : Nat.card A + 1 ≤ Module.finrank ℚ V := by
    have h1 : Nat.card A = Fintype.card A := Nat.card_eq_fintype_card
    have h2 : Fintype.card A < Module.finrank ℚ V := by
      rw [← hcard]
      exact hlt
    omega
  exact hfinal

