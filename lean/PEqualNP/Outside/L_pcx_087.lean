import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_087

private def bitDifference (a b : Bool) : ℕ :=
  if a ≠ b then 1 else 0

private lemma hammingDist_eq_sum {n : ℕ} (x y : Fin n → Bool) :
    hammingDist x y = ∑ k, bitDifference (x k) (y k) := by
  exact (Finset.sum_boole (fun k => x k ≠ y k) Finset.univ).symm

private lemma bit_path_bound (a b c d : Bool) :
    bitDifference a b ≤ bitDifference a d + bitDifference c d + bitDifference c b := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

end PEqualNP.Outside.L_pcx_087

theorem PEqualNP.Outside.L_pcx_087 :
    ∀ (n : ℕ) (u u' v v' : Fin n → Bool),
      hammingDist u v ≤ hammingDist u v' + hammingDist u' v' + hammingDist u' v := by
  intro n u u' v v'
  simp only [L_pcx_087.hammingDist_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => L_pcx_087.bit_path_bound (u k) (v k) (u' k) (v' k)
