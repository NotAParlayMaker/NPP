import Mathlib

namespace PEqualNP.Outside.L_lib_119

private theorem short_strings (k : ℕ) :
    Fintype.card (Σ l : Fin k, List.Vector Bool l) + 1 = 2 ^ k := by
  rw [Fintype.card_sigma]
  simp only [card_vector, Fintype.card_bool]
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => 2 ^ l)]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega

end PEqualNP.Outside.L_lib_119

theorem PEqualNP.Outside.L_lib_119 :
    ∀ n : ℕ, 1 ≤ n → ∀ g : (Σ l : Fin (n - 1), List.Vector Bool l) → List.Vector Bool n,
      2 ^ (n - 1) + 1 ≤ (Finset.univ.filter (fun y : List.Vector Bool n => ∀ x, g x ≠ y)).card := by
  intro n hn g
  let reached := Finset.univ.image g
  have hmissed :
      Finset.univ.filter (fun y : List.Vector Bool n => ∀ x, g x ≠ y) =
        Finset.univ \ reached := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      reached, Finset.mem_image, not_exists]
  have hreached : reached.card ≤ Fintype.card (Σ l : Fin (n - 1), List.Vector Bool l) := by
    simpa only [reached, Finset.card_univ] using
      (Finset.card_image_le (s := Finset.univ) (f := g))
  have hpart := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ reached)
  rw [Finset.card_univ, card_vector, Fintype.card_bool] at hpart
  have hn' : n - 1 + 1 = n := by omega
  have hpow : (2 : ℕ) ^ n = 2 ^ (n - 1) * 2 :=
    (congrArg (fun k => (2 : ℕ) ^ k) hn'.symm).trans (pow_succ 2 (n - 1))
  have hshort := PEqualNP.Outside.L_lib_119.short_strings (n - 1)
  rw [hmissed]
  omega
