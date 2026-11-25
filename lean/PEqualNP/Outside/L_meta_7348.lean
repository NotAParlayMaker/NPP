import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7348_aux

abbrev E (a b : Fin 7) : Prop := a = b ∨ a = b + 1 ∨ a = b + 3

abbrev Bad (g : Fin 14 → Bool) : Prop :=
  ∃ a b : Fin 7, E a b ∧ g (Fin.castAdd 7 a) = true ∧ g (Fin.natAdd 7 b) = true

def L : List ℕ := [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539, 2126, 2244, 2376,
  2626, 3008, 3078, 4125, 4244, 4361, 4625, 5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250,
  9632, 10250, 11778, 12312, 12944, 14600, 16256]

abbrev Q (g : Fin 14 → Bool) : Prop :=
  ¬Bad g → (∀ i, g i = false → Bad (Function.update g i true)) → ∃ x5 ∈ L, ∀ i : Fin 14, g i = x5.testBit i

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool,
    Q ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13] := by
  decide +kernel

theorem key2 (g : Fin 14 → Bool) : Q g := by
  have h := key (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9) (g 10) (g 11) (g 12) (g 13)
  have hg : ![g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9, g 10, g 11, g 12, g 13] = g := by
    funext i; fin_cases i <;> rfl
  rw [hg] at h
  exact h

end PEqualNP.Outside.L_meta_7348_aux

open PEqualNP.Outside.L_meta_7348_aux in
theorem PEqualNP.Outside.L_meta_7348 : have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true; ∀ (x3 : Fin (14 : ℕ) → Bool),   Maximal (fun (x4 : Fin (14 : ℕ) → Bool) => ¬x2 x4) x3 →     ∃       x5 ∈         have x6 : List ℕ :=           have x6 : List ℕ :=             have x6 : List ℕ := [(11778 : ℕ), (12312 : ℕ), (12944 : ℕ), (14600 : ℕ), (16256 : ℕ)];             (8488 : ℕ) :: (8722 : ℕ) :: (9250 : ℕ) :: (9632 : ℕ) :: (10250 : ℕ) :: x6;           have x7 : List ℕ := (5889 : ℕ) :: (6156 : ℕ) :: (7300 : ℕ) :: (8250 : ℕ) :: (8368 : ℕ) :: x6;           (4244 : ℕ) :: (4361 : ℕ) :: (4625 : ℕ) :: (5125 : ℕ) :: x7;         have x7 : List ℕ :=           have x7 : List ℕ := (2376 : ℕ) :: (2626 : ℕ) :: (3008 : ℕ) :: (3078 : ℕ) :: (4125 : ℕ) :: x6;           (1313 : ℕ) :: (1539 : ℕ) :: (2126 : ℕ) :: (2244 : ℕ) :: x7;         have x8 : List ℕ := (595 : ℕ) :: (720 : ℕ) :: (833 : ℕ) :: (1063 : ℕ) :: (1188 : ℕ) :: x7;         (127 : ℕ) :: (244 : ℕ) :: (361 : ℕ) :: (480 : ℕ) :: x8,       ∀ (x6 : Fin (14 : ℕ)), x3 x6 = x5.testBit ↑x6 := by
  intro x1 x2 x3 hm
  obtain ⟨hP, hmax⟩ := hm
  have hk := key2 x3 hP (by
    intro i hi
    by_contra hc
    have hle := hmax hc (by
      intro j
      by_cases h : j = i
      · subst h
        simp
      · simp [Function.update_of_ne h]) i
    simp [hi] at hle
    exact (not_le.mpr Bool.false_lt_true) hle)
  exact hk
