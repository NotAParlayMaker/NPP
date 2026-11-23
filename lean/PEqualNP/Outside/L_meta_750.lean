import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_750 : ∀ (n T K : ℕ) (h : Fin T → (Fin n → Bool) → Bool), 1 ≤ K → (∀ j : Fin T, Monotone (h j)) → ∃ (y : Fin n → Bool) (D : Finset (Fin T)), (∀ j1 ∈ D, h j1 y = true) ∧ (∀ j2 : Fin T, j2 ∉ D → ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) → (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)).card ≤ K → h j2 x = false) ∧ (Finset.univ.filter (fun i2 : Fin n => y i2 = true)).card ≤ K * D.card := by
  classical
  intro n T K h _ hm
  let bits (y : Fin n → Bool) := Finset.univ.filter (fun i => y i = true)
  let active (y : Fin n → Bool) := Finset.univ.filter (fun j => h j y = true)
  let good := Finset.univ.filter (fun y => (bits y).card ≤ K * (active y).card)
  have hnon : good.Nonempty := by
    refine ⟨fun _ => false, ?_⟩
    simp [good, bits]
  obtain ⟨y, hy, hmax⟩ := good.exists_max_image (fun x => (active x).card) hnon
  have hbound : (bits y).card ≤ K * (active y).card := (Finset.mem_filter.mp hy).2
  refine ⟨y, active y, fun j hj => (Finset.mem_filter.mp hj).2, ?_, hbound⟩
  intro j hj x he hd
  by_contra hf
  have ht : h j x = true := by simpa using hf
  have hyx : y ≤ x := fun i => Bool.le_iff_imp.mpr (he i)
  have hsub : active y ⊆ active x := by
    intro a ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact Bool.le_iff_imp.mp (hm a hyx) (Finset.mem_filter.mp ha).2
  have hstrict : (active y).card < (active x).card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro heq
    apply hj
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
  let added := Finset.univ.filter (fun i => x i = true ∧ y i = false)
  have hcover : bits x ⊆ bits y ∪ added := by
    intro i hi
    have hx := (Finset.mem_filter.mp hi).2
    cases hbit : y i <;> simp [bits, added, hbit, hx]
  have hxgood : x ∈ good := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    calc
      (bits x).card ≤ (bits y ∪ added).card := Finset.card_le_card hcover
      _ ≤ (bits y).card + added.card := Finset.card_union_le _ _
      _ ≤ K * (active y).card + K := Nat.add_le_add hbound hd
      _ = K * ((active y).card + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ K * (active x).card := Nat.mul_le_mul_left _ hstrict
  exact (Nat.not_lt_of_ge (hmax x hxgood)) hstrict
