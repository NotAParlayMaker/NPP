import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5475_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- the graph: left vertices 0 and 1 are joined to everything, 2 and 3 to nothing
def A : Fin 4 → Fin 4 → Bool := fun u v => (255 : ℕ).testBit (4 * u.val + v.val)

-- one OR gate reading the left wires 0 and 1
def C1 : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩], 8⟩

theorem up : RepSizeAtMost A 1 := by
  refine ⟨C1, ?_, by decide, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · intro u v
    fin_cases u <;> fin_cases v <;> rfl

-- with no gate the output is an input wire or a missing wire
theorem low : ¬ RepSizeAtMost A 0 := by
  rintro ⟨C, -, hs, hr⟩
  obtain ⟨gates, o⟩ := C
  have hg : gates = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)
  subst hg
  by_cases ho : o < 8
  · interval_cases o <;> exact absurd hr (by decide)
  · have h00 := hr 0 0
    have e : Circuit.eval ⟨[], o⟩ (oneEach (0 : Fin 4) (0 : Fin 4)) = false := by
      show (oneEach (0 : Fin 4) (0 : Fin 4)).getD o false = false
      exact List.getD_eq_default _ _ (by simp [oneEach]; omega)
    rw [e] at h00
    exact absurd h00 (by decide)

end PEqualNP.Outside.L_meta_5475_aux

theorem PEqualNP.Outside.L_meta_5475 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (255 : ℕ).testBit (4 * u.val + v.val)) 1 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (255 : ℕ).testBit (4 * u.val + v.val)) 0 :=
  ⟨PEqualNP.Outside.L_meta_5475_aux.up, PEqualNP.Outside.L_meta_5475_aux.low⟩
