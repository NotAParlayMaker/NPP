import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_750

theorem step (n T K : ℕ) (h : Fin T → (Fin n → Bool) → Bool) (hm : ∀ j : Fin T, Monotone (h j))
    (y : Fin n → Bool)
    (hy : (Finset.univ.filter (fun i2 : Fin n => y i2 = true)).card ≤
      K * (Finset.univ.filter (fun j : Fin T => h j y = true)).card)
    (hbad : ¬ ∀ j2 : Fin T, j2 ∉ Finset.univ.filter (fun j : Fin T => h j y = true) →
      ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) →
      (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)).card ≤ K → h j2 x = false) :
    ∃ x : Fin n → Bool,
      (Finset.univ.filter (fun j : Fin T => h j y = true)).card <
        (Finset.univ.filter (fun j : Fin T => h j x = true)).card ∧
      (Finset.univ.filter (fun i2 : Fin n => x i2 = true)).card ≤
        K * (Finset.univ.filter (fun j : Fin T => h j x = true)).card := by
  push Not at hbad
  obtain ⟨j, hj, x, hyx, hcard, hx⟩ := hbad
  have hxt : h j x = true := by simpa using hx
  have hle : y ≤ x := by
    intro i
    cases hyi : y i
    · exact Bool.false_le _
    · rw [hyx i hyi]
  have hlt : (Finset.univ.filter (fun j : Fin T => h j y = true)).card <
      (Finset.univ.filter (fun j : Fin T => h j x = true)).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨j, by simp [hxt], hj⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      have := hm k hle
      rw [hk] at this
      exact le_antisymm (Bool.le_true _) this
  refine ⟨x, hlt, ?_⟩
  have h1 : (Finset.univ.filter (fun i2 : Fin n => x i2 = true)) ⊆
      (Finset.univ.filter (fun i2 : Fin n => y i2 = true)) ∪
      (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    cases hyi : y i
    · exact Or.inr ⟨hi, rfl⟩
    · exact Or.inl rfl
  have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
  have h3 : K * ((Finset.univ.filter (fun j : Fin T => h j y = true)).card + 1) ≤
      K * (Finset.univ.filter (fun j : Fin T => h j x = true)).card := Nat.mul_le_mul_left K hlt
  rw [Nat.mul_add, Nat.mul_one] at h3
  omega

theorem main (n T K : ℕ) (h : Fin T → (Fin n → Bool) → Bool) (hm : ∀ j : Fin T, Monotone (h j)) :
    ∀ (c : ℕ) (y : Fin n → Bool),
      T - (Finset.univ.filter (fun j : Fin T => h j y = true)).card ≤ c →
      (Finset.univ.filter (fun i2 : Fin n => y i2 = true)).card ≤
        K * (Finset.univ.filter (fun j : Fin T => h j y = true)).card →
      ∃ (y : Fin n → Bool) (D : Finset (Fin T)), (∀ j1 ∈ D, h j1 y = true) ∧ (∀ j2 : Fin T, j2 ∉ D → ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) → (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)).card ≤ K → h j2 x = false) ∧ (Finset.univ.filter (fun i2 : Fin n => y i2 = true)).card ≤ K * D.card := by
  intro c
  induction c with
  | zero =>
    intro y hc hy
    by_cases hgood : ∀ j2 : Fin T, j2 ∉ Finset.univ.filter (fun j : Fin T => h j y = true) →
      ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) →
      (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)).card ≤ K → h j2 x = false
    · exact ⟨y, _, fun j1 hj1 => by simpa using hj1, hgood, hy⟩
    · obtain ⟨x, hlt, hx⟩ := step n T K h hm y hy hgood
      have hT : (Finset.univ.filter (fun j : Fin T => h j x = true)).card ≤ T := by
        simpa using Finset.card_le_univ (Finset.univ.filter (fun j : Fin T => h j x = true))
      omega
  | succ c ih =>
    intro y hc hy
    by_cases hgood : ∀ j2 : Fin T, j2 ∉ Finset.univ.filter (fun j : Fin T => h j y = true) →
      ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) →
      (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)).card ≤ K → h j2 x = false
    · exact ⟨y, _, fun j1 hj1 => by simpa using hj1, hgood, hy⟩
    · obtain ⟨x, hlt, hx⟩ := step n T K h hm y hy hgood
      have hT : (Finset.univ.filter (fun j : Fin T => h j x = true)).card ≤ T := by
        simpa using Finset.card_le_univ (Finset.univ.filter (fun j : Fin T => h j x = true))
      exact ih x (by omega) hx

end PEqualNP.Outside.L_meta_750

open PEqualNP.Outside.L_meta_750 in
theorem PEqualNP.Outside.L_meta_750 : ∀ (n T K : ℕ) (h : Fin T → (Fin n → Bool) → Bool), 1 ≤ K → (∀ j : Fin T, Monotone (h j)) → ∃ (y : Fin n → Bool) (D : Finset (Fin T)), (∀ j1 ∈ D, h j1 y = true) ∧ (∀ j2 : Fin T, j2 ∉ D → ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) → (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)).card ≤ K → h j2 x = false) ∧ (Finset.univ.filter (fun i2 : Fin n => y i2 = true)).card ≤ K * D.card := by
  intro n T K h _ hm
  exact main n T K h hm T (fun _ => false) (by omega) (by simp)
