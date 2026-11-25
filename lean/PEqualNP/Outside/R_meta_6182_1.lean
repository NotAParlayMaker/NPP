import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6182_1
    (h1 : PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 4 => (893 : ℕ).testBit (4 * u.val + v.val)) 9)
    (h2 : ¬ PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 4 => (893 : ℕ).testBit (4 * u.val + v.val)) 8) :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (893 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
      ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (893 : ℕ).testBit (4 * u.val + v.val)) 8 :=
  ⟨h1, h2⟩
