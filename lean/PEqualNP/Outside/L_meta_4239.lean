import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4239

def incN : Nat := 0x1a086821a086831a046811a046811a046c119047411

def inc (p l : Fin 13) : Bool := incN.testBit (13 * p.val + l.val)

theorem hinc : ∀ p l : Fin 13,
    (∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + x4) ↔ inc p l = true := by
  decide

theorem mask_exists (S : Finset (Fin 13)) :
    ∃ m < 8192, ∀ i : Fin 13, i ∈ S ↔ m.testBit i.val = true := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by norm_num, by simp⟩
  | insert a S ha ih =>
    obtain ⟨m, hm, hmem⟩ := ih
    refine ⟨m ||| 2 ^ a.val, ?_, ?_⟩
    · have h2 : 2 ^ a.val < 2 ^ 13 := Nat.pow_lt_pow_right (by norm_num) a.isLt
      exact Nat.or_lt_two_pow (by simpa using hm) h2
    · intro i
      rw [Finset.mem_insert, hmem i, Nat.testBit_or, Nat.testBit_two_pow]
      simp only [Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff, eq_comm (a := a.val)]
      tauto

set_option maxHeartbeats 20000000 in
theorem core : ∀ k : Fin 16, ∀ mm : Fin 512, let m := 512 * k.val + mm.val;
    (∀ x5 : Fin 13, ¬m.testBit x5.val = true → ∃ x7 : Fin 13,
        (∀ x5 : Fin 13, m.testBit x5.val = true → ¬inc x5 x7 = true) ∧ inc x5 x7 = true) →
      (((∃ x6 : Fin 13, ∀ x7 : Fin 13, m.testBit x7.val = true → inc x7 x6 = true) ∨
          ∃ x6 : Fin 13, ∀ x7 : Fin 13,
            (∀ x5 : Fin 13, m.testBit x5.val = true → ¬inc x5 x7 = true) → inc x6 x7 = true) ↔
        (Finset.univ.filter fun i : Fin 13 => m.testBit i.val = true).card ≤ 2 ∨
          (Finset.univ.filter fun x : Fin 13 =>
            ∀ x5 : Fin 13, m.testBit x5.val = true → ¬inc x5 x = true).card ≤ 2 ∨
          (Finset.univ.filter fun i : Fin 13 => m.testBit i.val = true).card = 3 ∧
            ∃ x6 : Fin 13, ∀ x7 : Fin 13, m.testBit x7.val = true → inc x7 x6 = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_4239

theorem PEqualNP.Outside.L_meta_4239 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; ∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), x3 x4 x7 ∧ x2 x5 x7) → (((∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x2 x7 x6) ∨ ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x3 x4 x7 → x2 x6 x7) ↔ x4.card ≤ (2 : ℕ) ∨ Nat.card { x6 : Fin (13 : ℕ) // x3 x4 x6 } ≤ (2 : ℕ) ∨ x4.card = (3 : ℕ) ∧ ∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x2 x7 x6) := by
  dsimp only
  intro S
  obtain ⟨m, hm, hmem⟩ := PEqualNP.Outside.L_meta_4239.mask_exists S
  have hS : S = Finset.univ.filter fun i : Fin 13 => m.testBit i.val = true := by
    ext i
    simp [hmem]
  subst hS
  simp only [PEqualNP.Outside.L_meta_4239.hinc, Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcore := PEqualNP.Outside.L_meta_4239.core ⟨m / 512, by omega⟩ ⟨m % 512, Nat.mod_lt _ (by norm_num)⟩
  have hm' : 512 * (m / 512) + m % 512 = m := Nat.div_add_mod m 512
  simp only [hm'] at hcore
  exact hcore
