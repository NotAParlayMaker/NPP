import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_6131 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (65535 : ℕ).testBit (4 * u.val + v.val)) 1 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (65535 : ℕ).testBit (4 * u.val + v.val)) 0 := by
  constructor
  · refine ⟨⟨[⟨.and, []⟩], 8⟩, ?_, by decide, by decide +kernel⟩
    intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    simp
  · rintro ⟨⟨gs, out⟩, _, hs, hr⟩
    have hgs : gs = [] := by
      cases gs with
      | nil => rfl
      | cons g gs => simp [Circuit.size] at hs
    subst gs
    have hbit : ∀ u v : Fin 4, (65535 : ℕ).testBit (4 * u.val + v.val) = true := by
      decide +kernel
    have hzero : (oneEach (0 : Fin 4) (0 : Fin 4)).getD out false = true := by
      simpa only [hbit, Circuit.eval, Circuit.wires, List.foldl_nil] using hr 0 0
    have hone : (oneEach (1 : Fin 4) (1 : Fin 4)).getD out false = true := by
      simpa only [hbit, Circuit.eval, Circuit.wires, List.foldl_nil] using hr 1 1
    have hdisjoint : ∀ i : Fin 8,
        (oneEach (0 : Fin 4) (0 : Fin 4)).getD i.val false = false ∨
        (oneEach (1 : Fin 4) (1 : Fin 4)).getD i.val false = false := by
      decide +kernel
    by_cases h : out < 8
    · rcases hdisjoint ⟨out, h⟩ with hz | ho
      · have heq : true = false := hzero.symm.trans hz
        cases heq
      · have heq : true = false := hone.symm.trans ho
        cases heq
    · have hlength : (oneEach (0 : Fin 4) (0 : Fin 4)).length ≤ out := by
        simpa [oneEach] using Nat.le_of_not_gt h
      rw [List.getD_eq_default _ _ hlength] at hzero
      contradiction
