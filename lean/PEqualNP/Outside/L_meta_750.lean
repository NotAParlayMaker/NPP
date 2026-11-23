import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.PiLex

namespace PEqualNP.Outside.L_meta_750

open Finset

private def support {n : ℕ} (y : Fin n → Bool) : Finset (Fin n) :=
  univ.filter (fun i => y i = true)

private theorem newBits {n : ℕ} (x y : Fin n → Bool) :
    support x \ support y = univ.filter (fun i => x i = true ∧ y i = false) := by
  ext i
  simp [support, Bool.not_eq_true]

private def enabled {n T : ℕ} (h : Fin T → (Fin n → Bool) → Bool) (y : Fin n → Bool) : Finset (Fin T) :=
  univ.filter (fun j => h j y = true)

private theorem enlarge {n T K : ℕ} {h : Fin T → (Fin n → Bool) → Bool}
    (hm : ∀ j, Monotone (h j)) (r : ℕ) :
    ∀ y : Fin n → Bool, T - (enabled h y).card = r → (support y).card ≤ K * (enabled h y).card →
    ∃ z : Fin n → Bool, (support z).card ≤ K * (enabled h z).card ∧
      ∀ j, j ∉ enabled h z → ∀ x : Fin n → Bool, z ≤ x → (support x \ support z).card ≤ K → h j x = false := by
  classical
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro y hr hy
    by_cases step : ∃ j, j ∉ enabled h y ∧ ∃ x : Fin n → Bool,
        y ≤ x ∧ (support x \ support y).card ≤ K ∧ h j x = true
    · obtain ⟨j, hj, x, hxy, hstep, hx⟩ := step
      have hsub : support y ⊆ support x := by
        intro i hi
        have hi' : y i = true := (mem_filter.mp hi).2
        exact mem_filter.mpr ⟨mem_univ _, Bool.eq_true_of_true_le (hi' ▸ hxy i)⟩
      have hsub' : enabled h y ⊆ enabled h x := by
        intro i hi
        have hi' : h i y = true := (mem_filter.mp hi).2
        exact mem_filter.mpr ⟨mem_univ _, Bool.eq_true_of_true_le (hi' ▸ hm i hxy)⟩
      have hlt : (enabled h y).card < (enabled h x).card := by
        apply card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub', ?_⟩
        intro e
        apply hj
        rw [e]
        exact mem_filter.mpr ⟨mem_univ j, hx⟩
      have hcard := card_sdiff_add_card_eq_card hsub
      have hb : (enabled h x).card ≤ T := by
        simpa using (enabled h x).card_le_univ
      apply ih (T - (enabled h x).card) (by omega) x rfl
      calc
        (support x).card ≤ K * (enabled h y).card + K := by omega
        _ = K * ((enabled h y).card + 1) := by rw [Nat.mul_succ]
        _ ≤ K * (enabled h x).card := Nat.mul_le_mul_left _ hlt
    · refine ⟨y, hy, ?_⟩
      intro j hj x hxy hcard
      exact Bool.eq_false_iff.mpr (fun ht => step ⟨j, hj, x, hxy, hcard, ht⟩)

private theorem solve (n T K : ℕ) (h : Fin T → (Fin n → Bool) → Bool) (hm : ∀ j, Monotone (h j)) :
    ∃ (y : Fin n → Bool) (D : Finset (Fin T)), (∀ j1 ∈ D, h j1 y = true) ∧
    (∀ j2 : Fin T, j2 ∉ D → ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) →
      (univ.filter (fun i : Fin n => x i = true ∧ y i = false)).card ≤ K → h j2 x = false) ∧
    (univ.filter (fun i : Fin n => y i = true)).card ≤ K * D.card := by
  obtain ⟨y, hy, stable⟩ := enlarge (K := K) hm _ (fun _ => false) rfl (by simp [support])
  refine ⟨y, enabled h y, (fun j hj => (mem_filter.mp hj).2), ?_, hy⟩
  intro j hj x hxy hcard
  apply stable j hj x _ (by rwa [newBits])
  intro i
  cases hval : y i
  · exact Bool.false_le _
  · rw [hxy i hval]

end PEqualNP.Outside.L_meta_750

theorem PEqualNP.Outside.L_meta_750 : ∀ (n T K : ℕ) (h : Fin T → (Fin n → Bool) → Bool), 1 ≤ K → (∀ j : Fin T, Monotone (h j)) → ∃ (y : Fin n → Bool) (D : Finset (Fin T)), (∀ j1 ∈ D, h j1 y = true) ∧ (∀ j2 : Fin T, j2 ∉ D → ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) → (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)).card ≤ K → h j2 x = false) ∧ (Finset.univ.filter (fun i2 : Fin n => y i2 = true)).card ≤ K * D.card := by
  intro n T K h _ hm
  exact PEqualNP.Outside.L_meta_750.solve n T K h hm
