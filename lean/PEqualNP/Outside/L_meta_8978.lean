import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8978

private lemma tableIndex_bits_mod (k n : ℕ) :
    PEqualNP.MetaComplexity.tableIndex (fun i : Fin k => n.testBit i) = n % 2 ^ k := by
  induction k with
  | zero => simp [PEqualNP.MetaComplexity.tableIndex, Nat.mod_one]
  | succ k ih =>
    unfold PEqualNP.MetaComplexity.tableIndex
    rw [Fin.sum_univ_castSucc]
    change PEqualNP.MetaComplexity.tableIndex (fun i : Fin k => n.testBit i) +
      (if n.testBit k = true then 2 ^ k else 0) = n % 2 ^ (k + 1)
    rw [ih, Nat.mod_pow_succ, ← Nat.toNat_testBit]
    cases n.testBit k <;> simp

end PEqualNP.Outside.L_meta_8978

theorem PEqualNP.Outside.L_meta_8978 : ∀ (k : ℕ) (u : Fin (2 ^ k)), PEqualNP.MetaComplexity.tableIndex (fun i : Fin k => (u : ℕ).testBit i) = (u : ℕ) := by
  intro k u
  rw [L_meta_8978.tableIndex_bits_mod, Nat.mod_eq_of_lt u.isLt]
