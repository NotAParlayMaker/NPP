import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1554_aux

def enc (n : Fin 8192) : Fin 13 → Bool := fun v => n.val.testBit v.val

theorem enc_inj : Function.Injective enc := by
  intro n m h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 13
  · exact congrFun h ⟨i, hi⟩
  · have h1 : n.val < 2 ^ i := lt_of_lt_of_le n.isLt (by
      have : (8192 : Nat) = 2 ^ 13 := by norm_num
      rw [this]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : m.val < 2 ^ i := lt_of_lt_of_le m.isLt (by
      have : (8192 : Nat) = 2 ^ 13 := by norm_num
      rw [this]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

theorem enc_bij : Function.Bijective enc := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨enc_inj, ?_⟩
  simp

theorem all_iff (P : (Fin 13 → Bool) → Prop) : (∀ x, P x) ↔ ∀ n, P (enc n) := by
  constructor
  · intro h n; exact h _
  · intro h x
    obtain ⟨n, rfl⟩ := enc_bij.2 x
    exact h n

theorem card_eq (P : (Fin 13 → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter (fun n => P (enc n))).card := by
  rw [← Finset.card_map ⟨enc, enc_inj⟩]
  apply congrArg Finset.card
  ext x
  obtain ⟨n, rfl⟩ := enc_bij.2 x
  simp

def Ln (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def lineB (s v : Fin 13) : Bool := v == s || v == s + 1 || v == s + 3 || v == s + 9

theorem memL (s v : Fin 13) : v ∈ Ln s ↔ lineB s v = true := by
  simp [Ln, lineB, or_assoc]

def cl : List (Fin 13 × Fin 13) := [(1, 2), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 10), (1, 11), (1, 12), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 9), (2, 10), (2, 11), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 10), (3, 11), (3, 12), (4, 1), (4, 2), (4, 3), (4, 6), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, 1), (5, 2), (5, 3), (5, 6), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (6, 12), (7, 1), (7, 2), (7, 3), (7, 6), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 1), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 9), (8, 10), (8, 11), (9, 2), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 10), (9, 11), (9, 12), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 7), (10, 8), (10, 9), (10, 12), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 7), (11, 8), (11, 9), (11, 12), (12, 1), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 9), (12, 10), (12, 11)]

theorem hcl0 : ∀ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), lineB t a = true ∧ lineB t b = true) ↔ (a, b) ∈ cl := by
  decide +kernel

theorem hcl (a b : Fin 13) : (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ Ln t ∧ b ∈ Ln t) ↔ (a, b) ∈ cl := by
  simp only [memL]; exact hcl0 a b

def bD (x : Fin 13 → Bool) : Bool := cl.any fun p => x p.1 && x p.2

theorem hD (x : Fin 13 → Bool) : (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ Ln t ∧ b ∈ Ln t) ∧ x a = true ∧ x b = true) ↔ bD x = true := by
  simp only [hcl, bD, List.any_eq_true, Bool.and_eq_true, Prod.exists]

def bL (x : Fin 13 → Bool) : Bool := ([0, 4, 10, 12] : List (Fin 13)).any fun t => (List.finRange 13).all fun v => !x v || lineB t v

theorem hL (x : Fin 13 → Bool) : (∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), ∀ v : Fin 13, x v = true → v ∈ Ln t) ↔ bL x = true := by
  simp only [bL, memL, List.any_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.or_eq_true, Bool.not_eq_true', Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.mem_nil_iff, or_false]
  apply exists_congr
  intro t
  apply and_congr Iff.rfl
  apply forall_congr'
  intro v
  cases x v <;> simp

theorem t1 : (List.range 8192).all (fun n => bD (fun v => n.testBit v.val) == !bL (fun v => n.testBit v.val)) = true := by
  decide +kernel

theorem t1b (x : Fin 13 → Bool) : bD x = !bL x := by
  revert x
  rw [all_iff]
  intro n
  have := List.all_eq_true.1 t1 n.val (List.mem_range.2 n.isLt)
  have h2 : (bD (enc n) == !bL (enc n)) = true := this
  simpa using h2

theorem t2 : (Finset.univ.filter (fun n : Fin 8192 => bD (enc n) = true)).card = 8134 := by
  unfold enc; decide +kernel

theorem part1 (x : Fin 13 → Bool) : (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ Ln t ∧ b ∈ Ln t) ∧ x a = true ∧ x b = true) ↔ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), ∀ v : Fin 13, x v = true → v ∈ Ln t := by
  rw [hD, hL, t1b]
  cases bL x <;> simp

theorem t4 : ∀ t : Fin 13, bD (fun v : Fin 13 => decide (lineB t v = false)) = true ∧ ∀ p : Fin 13, lineB t p = true → bD (fun v : Fin 13 => decide (lineB t v = false ∨ v = p)) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_1554_aux

open PEqualNP.Outside.L_meta_1554_aux in
theorem PEqualNP.Outside.L_meta_1554 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x : Fin 13 → Bool, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true) ↔ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), ∀ v : Fin 13, x v = true → v ∈ L t) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true))).card = 8134 ∧
    (∀ x y : Fin 13 → Bool, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true) → (∀ v : Fin 13, x v = true → y v = true) → (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ y a = true ∧ y b = true)) ∧
    (∀ t : Fin 13, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ (fun v : Fin 13 => decide (v ∉ L t)) a = true ∧ (fun v : Fin 13 => decide (v ∉ L t)) b = true) ∧ ∀ p ∈ L t, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ (fun v : Fin 13 => decide (v ∉ L t ∨ v = p)) a = true ∧ (fun v : Fin 13 => decide (v ∉ L t ∨ v = p)) b = true)) := by
  intro L hL
  obtain rfl : L = Ln := funext hL
  refine ⟨part1, ?_, ?_, ?_⟩
  · rw [card_eq]
    simp only [hD]
    exact t2
  · intro x y hx hxy
    rw [part1] at hx ⊢
    rintro ⟨t, ht, h⟩
    exact hx ⟨t, ht, fun v hv => h v (hxy v hv)⟩
  · intro t
    obtain ⟨h1, h2⟩ := t4 t
    refine ⟨?_, ?_⟩
    · rw [hD]
      convert h1 using 3
      simp [memL]
    · intro p hp
      rw [hD]
      convert h2 p ((memL t p).1 hp) using 3
      simp [memL]
