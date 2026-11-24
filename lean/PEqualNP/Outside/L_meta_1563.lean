import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1563

/-- The line through `t` in the plane of order 3 on `Fin 13`. -/
def lineSet (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

end PEqualNP.Outside.L_meta_1563

open PEqualNP.Outside.L_meta_1563

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

theorem PEqualNP.Outside.L_meta_1563 :
  ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9))))
  := by
  intro L hL
  have hLfun : L = lineSet := funext hL
  subst hLfun
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with h | h | h
    · exact Or.inl (hxy 0 h)
    · exact Or.inr (Or.inl (hxy 1 h))
    · exact Or.inr (Or.inr (fun v hv => hxy v (h v hv)))
  · decide
  · decide
  · decide
  · decide
