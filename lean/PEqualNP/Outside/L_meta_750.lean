import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_750 : ∀ (n T K : ℕ) (h : Fin T → (Fin n → Bool) → Bool), 1 ≤ K → (∀ j : Fin T, Monotone (h j)) → ∃ (y : Fin n → Bool) (D : Finset (Fin T)), (∀ j1 ∈ D, h j1 y = true) ∧ (∀ j2 : Fin T, j2 ∉ D → ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) → (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)).card ≤ K → h j2 x = false) ∧ (Finset.univ.filter (fun i2 : Fin n => y i2 = true)).card ≤ K * D.card := by
  classical
  intro n T K h _ hm
  let bits (v : Fin n → Bool) := Finset.univ.filter (fun i => v i = true)
  let active (v : Fin n → Bool) := Finset.univ.filter (fun j => h j v = true)
  let feasible := Finset.univ.filter (fun v => (bits v).card ≤ K * (active v).card)
  have memF (v : Fin n → Bool) : v ∈ feasible ↔ (bits v).card ≤ K * (active v).card := by
    simp [feasible]
  have nonempty : feasible.Nonempty := by
    refine ⟨fun _ => false, (memF _).mpr ?_⟩
    simp [bits]
  obtain ⟨y, hy, hmax⟩ := feasible.exists_max_image (fun v => (active v).card) nonempty
  refine ⟨y, active y, ?_, ?_, (memF y).mp hy⟩
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro j hj x hxy hk
    by_contra bad
    have hit : h j x = true := by cases e : h j x <;> simp_all
    have xy : y ≤ x := by
      intro i
      cases e : y i
      · exact Bool.false_le _
      · simp [hxy i e]
    have sub : active y ⊆ active x := by
      intro a ha
      have ha' := (Finset.mem_filter.mp ha).2
      have le := hm a xy
      rw [ha'] at le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Bool.eq_true_of_true_le le⟩
    have hjx : j ∈ active x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩
    have lt : (active y).card < (active x).card := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨sub, fun eq => hj (eq ▸ hjx)⟩)
    have bsub : bits y ⊆ bits x := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy i (Finset.mem_filter.mp hi).2⟩
    have diff : bits x \ bits y = Finset.univ.filter (fun i => x i = true ∧ y i = false) := by
      ext i
      simp [bits]
    have sum := Finset.card_sdiff_add_card_eq_card bsub
    rw [diff] at sum
    have budget := Nat.mul_le_mul_left K lt
    rw [Nat.mul_succ] at budget
    have hold := (memF y).mp hy
    have hx : x ∈ feasible := (memF x).mpr (by omega)
    exact (Nat.not_le_of_gt lt) (hmax x hx)
