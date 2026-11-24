import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4932

def X1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]

def X2 (i : ℕ) (j : Fin (14 : ℕ)) : Bool := (X1.getD (↑j) (0 : BitVec (58 : ℕ))).getLsbD i

def CL : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112, 127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

def C (i : ℕ) : ℕ := CL.getD i 0

def anyBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | n + 1, p => anyBelow n p || p n

def ok (m : ℕ) : Bool :=
  anyBelow 21 (fun i => C i &&& m == C i) || anyBelow 37 (fun k => m &&& C (21 + k) == m)

def chk : ℕ → ℕ → Bool
  | 0, b => ok b
  | k + 1, b => chk k b && chk k (b + 2 ^ k)

lemma chk_all : chk 14 0 = true := by decide +kernel

lemma col_eq : ∀ i : Fin 58, ∀ j : Fin 14, X2 i j = (C i).testBit j := by decide +kernel

lemma anyBelow_true {n : ℕ} {p : ℕ → Bool} (h : anyBelow n p = true) :
    ∃ i < n, p i = true := by
  induction n with
  | zero => simp [anyBelow] at h
  | succ n ih =>
    simp only [anyBelow, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨i, hi, hp⟩ := ih h
      exact ⟨i, by omega, hp⟩
    · exact ⟨n, by omega, h⟩

lemma chk_spec : ∀ k b, chk k b = true → ∀ m < 2 ^ k, ok (b + m) = true := by
  intro k
  induction k with
  | zero =>
    intro b h m hm
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    simpa [chk] using h
  | succ k ih =>
    intro b h m hm
    simp only [chk, Bool.and_eq_true] at h
    by_cases hlt : m < 2 ^ k
    · exact ih b h.1 m hlt
    · have h2 : m - 2 ^ k < 2 ^ k := by rw [pow_succ] at hm; omega
      have h3 := ih (b + 2 ^ k) h.2 (m - 2 ^ k) h2
      have e : b + 2 ^ k + (m - 2 ^ k) = b + m := by omega
      rwa [e] at h3

lemma code : ∀ n (f : Fin n → Bool), ∃ m < 2 ^ n, ∀ j : Fin n, m.testBit j = f j := by
  intro n
  induction n with
  | zero => intro f; exact ⟨0, by simp, fun j => j.elim0⟩
  | succ n ih =>
    intro f
    obtain ⟨m, hm, hb⟩ := ih (fun j => f j.succ)
    refine ⟨Nat.bit (f 0) m, ?_, ?_⟩
    · rw [Nat.bit_val, pow_succ]
      cases f 0 <;> simp <;> omega
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · have hs := Nat.testBit_bit_succ (j : ℕ) (f 0) m
        simp only [Fin.val_succ, Nat.succ_eq_add_one] at hs ⊢
        rw [hs, hb j]

lemma le_of_and {a b : Bool} (h : (a && b) = a) : a ≤ b := by
  cases a <;> cases b <;> simp_all

lemma core : ∀ (x3 : Fin (14 : ℕ) → Bool), (∀ (x4 : Fin (21 : ℕ)), ¬X2 ↑x4 ≤ x3) →
    ∃ (x5 : Fin (37 : ℕ)), x3 ≤ X2 ((21 : ℕ) + ↑x5) := by
  intro x3 h
  obtain ⟨m, hm, hb⟩ := code 14 x3
  have hok : ok m = true := by simpa using chk_spec 14 0 chk_all m hm
  simp only [ok, Bool.or_eq_true] at hok
  rcases hok with he | hbig
  · obtain ⟨i, hi, hp⟩ := anyBelow_true he
    exfalso
    apply h ⟨i, hi⟩
    intro j
    have hand : C i &&& m = C i := by simpa using hp
    have hj := congrArg (fun t => Nat.testBit t j) hand
    simp only [Nat.testBit_and] at hj
    have hc := col_eq ⟨i, by omega⟩ j
    simp only at hc
    show X2 i j ≤ x3 j
    rw [hc, ← hb j]
    exact le_of_and hj
  · obtain ⟨k, hk, hp⟩ := anyBelow_true hbig
    refine ⟨⟨k, hk⟩, ?_⟩
    intro j
    have hand : m &&& C (21 + k) = m := by simpa using hp
    have hj := congrArg (fun t => Nat.testBit t j) hand
    simp only [Nat.testBit_and] at hj
    have hc := col_eq ⟨21 + k, by omega⟩ j
    simp only at hc
    show x3 j ≤ X2 (21 + k) j
    rw [hc, ← hb j]
    exact le_of_and hj

end PEqualNP.Outside.L_meta_4932

theorem PEqualNP.Outside.L_meta_4932 : have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]; have x2 : ℕ → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 : Fin (14 : ℕ)) => (x1.getD ↑x3 (0 : BitVec (58 : ℕ))).getLsbD x2; ∀ (x3 : Fin (14 : ℕ) → Bool), (∀ (x4 : Fin (21 : ℕ)), ¬x2 ↑x4 ≤ x3) → ∃ (x5 : Fin (37 : ℕ)), x3 ≤ x2 ((21 : ℕ) + ↑x5) := by
  exact PEqualNP.Outside.L_meta_4932.core
