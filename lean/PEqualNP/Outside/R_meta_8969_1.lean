import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_8969_1
    (normalize : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : Circuit),
      0 < s → (∀ r ∈ rows, r < 2^n) → Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) →
      ∃ k < enc2CubeCount n s, FormulaSat (enc2 n s g rows ++ enc2Cube n s k))
    (certificates : ∀ k < 54, ¬ FormulaSat (enc2 8 10
      (fun r => (13726 : ℕ).testBit (4 * Nat.log2 (r % 16) + Nat.log2 (r / 16)))
      [17, 33, 65, 129, 18, 34, 66, 130, 20, 36, 68, 132, 24, 40, 72, 136] ++
      enc2Cube 8 10 k)) :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (13726 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  intro hre
  obtain ⟨C, hC, hs, hr⟩ := hre
  have hr' : ∀ (u v : Fin 4), C.eval (PEqualNP.Represents.oneEach u v) =
      (13726 : ℕ).testBit (4 * u.val + v.val) := hr
  have powrepr : ∀ r ∈ [17, 33, 65, 129, 18, 34, 66, 130, 20, 36, 68, 132, 24, 40, 72, 136],
      ∃ (u : Fin 4) (v : Fin 4), r = (2:ℕ)^u.val + 2^(4+v.val) := by
    decide +kernel
  have bound : ∀ r ∈ [17, 33, 65, 129, 18, 34, 66, 130, 20, 36, 68, 132, 24, 40, 72, 136], r < 2^8 := by
    decide +kernel
  have agree : ∀ r ∈ [17, 33, 65, 129, 18, 34, 66, 130, 20, 36, 68, 132, 24, 40, 72, 136],
      C.eval (List.ofFn fun i : Fin 8 => r.testBit i.val) =
        (fun r => (13726 : ℕ).testBit (4 * Nat.log2 (r % 16) + Nat.log2 (r / 16))) r := by
    intro r hr
    obtain ⟨u, v, rfl⟩ := powrepr r hr
    have bs : ∀ (u : Fin 4) (v : Fin 4),
        List.ofFn (fun i : Fin 8 => ((2:ℕ)^u.val + 2^(4+v.val)).testBit i.val) =
          PEqualNP.Represents.oneEach u v := by
      decide +kernel
    rw [bs u v, hr' u v]
    fin_cases u <;> fin_cases v <;> decide
  obtain ⟨k, hk0, sat⟩ := normalize 8 10
    (fun r => (13726 : ℕ).testBit (4 * Nat.log2 (r % 16) + Nat.log2 (r / 16)))
    [17, 33, 65, 129, 18, 34, 66, 130, 20, 36, 68, 132, 24, 40, 72, 136] C
    (by decide) bound hC hs agree
  have hk : k < 54 := by
    have cnt : enc2CubeCount 8 10 = 54 := by decide
    exact cnt ▸ hk0
  exact certificates k hk sat
