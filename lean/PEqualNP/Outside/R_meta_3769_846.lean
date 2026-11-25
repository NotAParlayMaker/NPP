import Mathlib
import PEqualNP.Defs

-- Split on whether some select gate that reads its own bit has two operands sharing an input.
-- If none does, the program is multilinear and multi has a checked proof: free families,
-- greedy choice bits, stars and a Nechiporuk count give N (q + 1) at most twice the gates.
theorem PEqualNP.Outside.R_meta_3769_846
    (multi : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      ∀ (s o : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ), o < N + N + s →
      (∀ z : Fin s → Bool, ∀ v < N + N, D z v = {v}) →
      (∀ j : Fin s, ∃ a < N + N + j.val, ∃ b < N + N + j.val,
      (∀ z, D z (N + N + j.val) = D z a ∪ D z b) ∨
      (∀ z, D z (N + N + j.val) = if z j = true then D z a else D z b) ∨
      ∀ z, D z (N + N + j.val) = ∅) →
      ¬ (∃ j : Fin s, ∃ a < N + N + j.val, ∃ b < N + N + j.val, ∃ z w y : Fin s → Bool,
      (∀ x, D x (N + N + j.val) = if x j = true then D x a else D x b) ∧
      ¬ Disjoint (D z a) (D w b) ∧ D y a ≠ D y b) →
      (∀ (z : Fin s → Bool) (p l : Fin N), I p l → p.val ∈ D z o ∨ N + l.val ∈ D z o) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ z : Fin s → Bool, ∀ p : Fin N,
      (p.val ∈ D z o ↔ ∃ l ∈ T, I p l) ∧ (N + p.val ∈ D z o ↔ p ∉ T)) →
      N * (q + 1) ≤ 2 * s)
    (rest : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      300 ≤ q ∧ N = q ^ 2 + q + 1 → (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) ∧
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      ∀ (s o : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ), o < N + N + s ∧ 3 * N ≤ s + 1 →
      (∀ z : Fin s → Bool, ∀ v < N + N, D z v = {v}) →
      (∀ j : Fin s, ∃ a < N + N + j.val, ∃ b < N + N + j.val,
        (∀ z, D z (N + N + j.val) = D z a ∪ D z b) ∨
        (∀ z, D z (N + N + j.val) = if z j = true then D z a else D z b) ∨
        ∀ z, D z (N + N + j.val) = ∅) ∧
      (∃ j : Fin s, ∃ a < N + N + j.val, ∃ b < N + N + j.val, ∃ z w y : Fin s → Bool,
      (∀ x, D x (N + N + j.val) = if x j = true then D x a else D x b) ∧
      ¬ Disjoint (D z a) (D w b) ∧ D y a ≠ D y b) →
      (∀ (z : Fin s → Bool) (p l : Fin N), I p l → p.val ∈ D z o ∨ N + l.val ∈ D z o) ∧
      (∀ p : Fin N, p.val ∉ D (fun _ => false) o ∧ N + p.val ∈ D (fun _ => false) o) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ z : Fin s → Bool, ∀ p : Fin N,
        (p.val ∈ D z o ↔ ∃ l ∈ T, I p l) ∧ (N + p.val ∈ D z o ↔ p ∉ T)) →
      N * q ≤ 100 * s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : (Fin x9 → Bool) → ℕ → Finset ℕ), x10 < x2 + x2 + x9 → (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) → (∀ (x14 : Fin x9 → Bool), ∀ x15 < x2 + x2, x11 x14 x15 = {x15}) → (∀ (x15 : Fin x9), ∃ x16 < x2 + x2 + ↑x15, ∃ x17 < x2 + x2 + ↑x15, (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = x11 x18 x16 ∪ x11 x18 x17) ∨ (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = if x18 x15 = Bool.true then x11 x18 x16 else x11 x18 x17) ∨ ∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = ∅) → (∀ (x16 : Fin x9 → Bool) (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x11 x16 x10 ∨ x2 + ↑x18 ∈ x11 x16 x10) → (∀ (x17 : Fin x2), ↑x17 ∉ x11 (fun (x18 : Fin x9) => Bool.false) x10 ∧ x2 + ↑x17 ∈ x11 (fun (x18 : Fin x9) => Bool.false) x10) → (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ (x20 : Fin x9 → Bool), ∀ (x21 : Fin x2), (↑x21 ∈ x11 x20 x10 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ (x2 + ↑x21 ∈ x11 x20 x10 ↔ x21 ∉ x18)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q N I decI hq hN hdeg hpl s o D ho hs hin hgate hsafe hzero hreal
  refine (Classical.em _).elim (fun c =>
    rest q N I ⟨hq, hN⟩ ⟨hdeg, hpl⟩ s o D ⟨ho, hs⟩ hin ⟨hgate, c⟩ ⟨hsafe, hzero⟩ hreal) (fun c => ?_)
  have h := multi q N I (by omega) hN hdeg hpl s o D ho hin hgate c hsafe hreal
  have h2 : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (Nat.le_succ q)
  omega
