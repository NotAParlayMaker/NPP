import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3332 : ∀ (x1 : (Fin (9 : ℕ) → Bool) → Bool),   (∀ (x2 : Fin (9 : ℕ)) (x3 : Bool), (x1 fun (x4 : Fin (9 : ℕ)) => Decidable.decide (x4 = x2) && x3) = Bool.false ∧ (x1 fun (x4 : Fin (9 : ℕ)) => !Decidable.decide (x4 = x2) || x3) = Bool.true) →     ∀ (x3 : ℕ) (x4 : Fin x3 → Bool) (x5 x6 : Fin x3 → ℕ × Bool) (x7 : ℕ × Bool) (x8 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),       x7.1 < (10 : ℕ) + x3 →         (∀ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ)), x8 x10 ↑x11 = x10 x11) →           (∀ (x11 : Fin (9 : ℕ) → Bool), x8 x11 (9 : ℕ) = Bool.false) →             (∀ (x12 : Fin (9 : ℕ) → Bool) (x13 : Fin x3),                 have x14 : ℕ × Bool → Bool := fun (x14 : ℕ × Bool) => x8 x12 x14.1 ^^ x14.2;                 x8 x12 ((10 : ℕ) + ↑x13) = if x4 x13 = Bool.true then x14 (x5 x13) && x14 (x6 x13) else x14 (x5 x13) || x14 (x6 x13)) →               (∀ (x13 : Fin (9 : ℕ) → Bool), (x8 x13 x7.1 ^^ x7.2) = x1 x13) → ∃ (x14 : Fin x3), x7.1 = (10 : ℕ) + ↑x14 ∧ (9 : ℕ) ≤ (x5 x14).1 ∧ (9 : ℕ) ≤ (x6 x14).1 := by
  intro f hf n op s1 s2 out W hout hin h9 hgate hcomp
  have two : ∀ (v : Fin 9) (a : Bool), ∃ y z : Fin 9 → Bool,
      y v = a ∧ z v = a ∧ f y = false ∧ f z = true := by
    intro v a
    exact ⟨fun x4 => decide (x4 = v) && a, fun x4 => !decide (x4 = v) || a,
      by simp, by simp, (hf v a).1, (hf v a).2⟩
  have kill : ∀ (v : Fin 9) (a c : Bool), (∀ x : Fin 9 → Bool, x v = a → f x = c) → False := by
    intro v a c h
    obtain ⟨y, z, hy, hz, fy, fz⟩ := two v a
    have e1 := h y hy
    have e2 := h z hz
    rw [fy] at e1
    rw [fz, ← e1] at e2
    cases e2
  have lit : ∀ (x : Fin 9 → Bool) (k : ℕ) (hk : k < 9), W x k = x ⟨k, hk⟩ := by
    intro x k hk
    exact hin x ⟨k, hk⟩
  by_contra hne
  simp only [not_exists, not_and, not_le] at hne
  rcases Nat.lt_or_ge out.1 9 with h | h
  · apply kill ⟨out.1, h⟩ false (false ^^ out.2)
    intro x hx
    rw [← hcomp x, lit x out.1 h, hx]
  rcases Nat.lt_or_ge out.1 10 with h' | h'
  · have e9 : out.1 = 9 := by omega
    apply kill 0 false (false ^^ out.2)
    intro x _
    rw [← hcomp x, e9, h9 x]
  let i : Fin n := ⟨out.1 - 10, by omega⟩
  have hi : out.1 = 10 + i.val := by simp only [i]; omega
  have gval : ∀ x : Fin 9 → Bool, f x = ((if op i = true then
      (W x (s1 i).1 ^^ (s1 i).2) && (W x (s2 i).1 ^^ (s2 i).2)
      else (W x (s1 i).1 ^^ (s1 i).2) || (W x (s2 i).1 ^^ (s2 i).2)) ^^ out.2) := by
    intro x
    rw [← hcomp x, hi, hgate x i]
  by_cases h1 : 9 ≤ (s1 i).1
  · have h2 : (s2 i).1 < 9 := hne i hi h1
    cases hop : op i
    · apply kill ⟨(s2 i).1, h2⟩ (!(s2 i).2) (true ^^ out.2)
      intro x hx
      rw [gval x, hop, lit x _ h2, hx]
      cases (s2 i).2 <;> simp
    · apply kill ⟨(s2 i).1, h2⟩ (s2 i).2 (false ^^ out.2)
      intro x hx
      rw [gval x, hop, lit x _ h2, hx]
      simp
  · have h1' : (s1 i).1 < 9 := by omega
    cases hop : op i
    · apply kill ⟨(s1 i).1, h1'⟩ (!(s1 i).2) (true ^^ out.2)
      intro x hx
      rw [gval x, hop, lit x _ h1', hx]
      cases (s1 i).2 <;> simp
    · apply kill ⟨(s1 i).1, h1'⟩ (s1 i).2 (false ^^ out.2)
      intro x hx
      rw [gval x, hop, lit x _ h1', hx]
      simp
