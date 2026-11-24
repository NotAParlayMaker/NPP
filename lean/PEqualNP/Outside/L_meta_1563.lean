import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1563_aux

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

theorem card_eq (P : (Fin 13 → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter (fun n => P (enc n))).card := by
  rw [← Finset.card_map ⟨enc, enc_inj⟩]
  apply congrArg Finset.card
  ext x
  obtain ⟨n, rfl⟩ := enc_bij.2 x
  simp

def Ln (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def lineB (v : Fin 13) : Bool := v == 0 || v == 1 || v == 3 || v == 9
def bo (n : Nat) : Bool := (List.finRange 13).all fun v => lineB v || n.testBit v.val
def bf (n : Nat) : Bool := n.testBit 0 || n.testBit 1 || bo n

theorem t1 : (Finset.univ.filter (fun n : Fin 8192 => bf n.val = true)).card = 6148 := by decide +kernel
theorem t2 : (Finset.univ.filter (fun n : Fin 8192 => (n.val.testBit 0 || n.val.testBit 1) = true)).card = 6144 := by decide +kernel

theorem hB (n : Fin 8192) : (∀ v : Fin 13, v ∉ Ln 0 → enc n v = true) ↔ bo n.val = true := by
  simp only [bo, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.or_eq_true, lineB, beq_iff_eq, Ln, Finset.mem_insert, Finset.mem_singleton, enc]
  apply forall_congr'
  intro v
  cases n.val.testBit v.val <;> simp [or_assoc] <;> tauto

theorem coline : ∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ Ln t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ Ln t)) 1 = true ∨ ∀ v : Fin 13, v ∉ Ln 0 → (fun v : Fin 13 => decide (v ∉ Ln t)) v = true) := by
  unfold Ln; decide +kernel

theorem charz (x : Fin 13 → Bool) : (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ Ln 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ Ln 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ Ln 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ Ln 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ Ln 0 ∨ v = 3 ∨ v = 9))) := by
  constructor
  · rintro (h | h | hy)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    by_cases h0 : x 0 = true
    · exact Or.inl h0
    by_cases h1 : x 1 = true
    · exact Or.inr (Or.inl h1)
    simp only [Bool.not_eq_true] at h0 h1
    right; right
    by_cases h3 : x 3 = true <;> by_cases h9 : x 9 = true <;> (try simp only [Bool.not_eq_true] at h3) <;> (try simp only [Bool.not_eq_true] at h9)
    · right; right; right
      funext v
      by_cases hv : v ∈ Ln 0
      · simp only [Ln, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl
        all_goals (simp only [zero_add, h0, h1, h3, h9]; decide)
      · rw [hy v hv]; simp [hv]
    · right; left
      funext v
      by_cases hv : v ∈ Ln 0
      · simp only [Ln, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl
        all_goals (simp only [zero_add, h0, h1, h3, h9]; decide)
      · rw [hy v hv]; simp [hv]
    · right; right; left
      funext v
      by_cases hv : v ∈ Ln 0
      · simp only [Ln, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl
        all_goals (simp only [zero_add, h0, h1, h3, h9]; decide)
      · rw [hy v hv]; simp [hv]
    · left
      funext v
      by_cases hv : v ∈ Ln 0
      · simp only [Ln, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl
        all_goals (simp only [zero_add, h0, h1, h3, h9]; decide)
      · rw [hy v hv]; simp [hv]
  · rintro (h | h | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    all_goals (right; right; intro v hv; rw [h]; simp [hv])

end PEqualNP.Outside.L_meta_1563_aux

open PEqualNP.Outside.L_meta_1563_aux in
theorem PEqualNP.Outside.L_meta_1563 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)))) := by
  intro L hL
  obtain rfl : L = Ln := funext hL
  refine ⟨?_, ?_, coline, ?_, charz⟩
  · rintro x y (h | h | h) hxy
    · exact Or.inl (hxy _ h)
    · exact Or.inr (Or.inl (hxy _ h))
    · exact Or.inr (Or.inr (fun v hv => hxy v (h v hv)))
  · rw [card_eq]
    simp only [hB]
    rw [← t1]
    simp [bf, enc, or_assoc]
  · rw [card_eq]
    rw [← t2]
    simp [enc]
