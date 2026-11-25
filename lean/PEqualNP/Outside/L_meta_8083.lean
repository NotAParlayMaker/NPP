import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8083

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def MS : List ℕ := [127, 245, 361, 481, 595, 721, 1063, 1189, 2127, 2245, 2377, 2627, 3009, 3079, 4125, 4245, 6157, 7301, 8251, 8369, 8489, 8723, 9251, 9633, 10251, 11779, 12313, 12945, 14601, 16257]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8083

theorem PEqualNP.Outside.L_meta_8083 : ∀ (x1 : Fin (14 : ℕ) → Bool), (∃ (x2 : Fin (7 : ℕ)) (x3 : Fin (7 : ℕ)), x2 ≠ (0 : Fin (7 : ℕ)) ∧ (x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ))) ∧ x1 (Fin.castAdd (7 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (7 : ℕ) x3) = Bool.true) ↔ ∀ x2 ∈ [(127 : ℕ), (245 : ℕ), (361 : ℕ), (481 : ℕ), (595 : ℕ), (721 : ℕ), (1063 : ℕ), (1189 : ℕ), (2127 : ℕ), (2245 : ℕ), (2377 : ℕ), (2627 : ℕ), (3009 : ℕ), (3079 : ℕ), (4125 : ℕ), (4245 : ℕ), (6157 : ℕ), (7301 : ℕ), (8251 : ℕ), (8369 : ℕ), (8489 : ℕ), (8723 : ℕ), (9251 : ℕ), (9633 : ℕ), (10251 : ℕ), (11779 : ℕ), (12313 : ℕ), (12945 : ℕ), (14601 : ℕ), (16257 : ℕ)], ¬x1 ≤ fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4 := by
  intro x
  constructor
  · rintro ⟨a, b, h0, hab, ha, hb⟩ c hc hle
    have key : ∀ c ∈ PEqualNP.Outside.L_meta_8083.MS, ∀ a b : Fin 7, a ≠ 0 → (a = b ∨ a = b + 1 ∨ a = b + 3) → ¬(c.testBit (a : ℕ) = true ∧ c.testBit (7 + (b : ℕ)) = true) := by decide +kernel
    have h1 := hle (Fin.castAdd 7 a)
    have h2 := hle (Fin.natAdd 7 b)
    rw [ha] at h1
    rw [hb] at h2
    exact key c hc a b h0 hab ⟨Bool.le_iff_imp.1 h1 rfl, Bool.le_iff_imp.1 h2 rfl⟩
  · intro h
    by_contra hcon
    have key : ∀ y : Fin 7 → Bool, ∃ c ∈ PEqualNP.Outside.L_meta_8083.MS, (∀ a : Fin 7, y a = true → c.testBit (a : ℕ) = true) ∧ ∀ b : Fin 7, (∀ a : Fin 7, a ≠ 0 → (a = b ∨ a = b + 1 ∨ a = b + 3) → y a = false) → c.testBit (7 + (b : ℕ)) = true := by decide +kernel
    obtain ⟨c, hc, h1, h2⟩ := key fun a => x (Fin.castAdd 7 a)
    refine h c hc fun i => ?_
    refine Fin.addCases (m := 7) (n := 7) (motive := fun i => x i ≤ c.testBit (i : ℕ)) (fun a => ?_) (fun b => ?_) i
    · exact Bool.le_iff_imp.2 (h1 a)
    · refine Bool.le_iff_imp.2 fun hb => h2 b fun a h0 hab => ?_
      cases hx : x (Fin.castAdd 7 a)
      · rfl
      · exact absurd ⟨a, b, h0, hab, hx, hb⟩ hcon
