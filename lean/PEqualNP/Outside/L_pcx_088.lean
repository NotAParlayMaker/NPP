import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_088

private def bitDifference (a b : Bool) : ℕ :=
  if a ≠ b then 1 else 0

private lemma hammingDist_eq_sum {n : ℕ} (x y : Fin n → Bool) :
    hammingDist x y = ∑ k, bitDifference (x k) (y k) := by
  exact (Finset.sum_boole (fun k => x k ≠ y k) Finset.univ).symm

private lemma even_bit_cycle (a b c d : Bool) :
    Even (bitDifference a b + bitDifference a d + bitDifference c d + bitDifference c b) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

end PEqualNP.Outside.L_pcx_088

theorem PEqualNP.Outside.L_pcx_088 :
    ∀ (n : ℕ) (u u' v v' : Fin n → Bool),
      Even (hammingDist u v + hammingDist u v' + hammingDist u' v' + hammingDist u' v) := by
  intro n u u' v v'
  simp only [L_pcx_088.hammingDist_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.even_sum _ fun k _ => L_pcx_088.even_bit_cycle (u k) (v k) (u' k) (v' k)
