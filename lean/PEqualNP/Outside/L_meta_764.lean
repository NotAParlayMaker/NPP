import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The edge function of a triangle, in the form of `L100`. -/
def g : (Fin 3 → Bool) → Bool :=
  fun y => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)

lemma g_nonconstant : ∃ y y' : Fin 3 → Bool, g y ≠ g y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

/-- The triangle-and-edge function is the `L153` shape: one rigid AND followed by the triangle. -/
lemma fun_eq :
    (fun x : Fin 5 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4))
      = (fun x : Fin 5 → Bool =>
        (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
          g (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
  funext x
  revert x
  decide

end PEqualNP.Outside.L_meta_764_aux

open PEqualNP.Outside.L_meta_764_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_764 :
    ∀ s : ℕ,
      PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔
        6 ≤ s := by
  intro s
  have hmain : ∀ t : ℕ,
      PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) (t + 2) ↔
        6 ≤ t + 2 := by
    intro t
    rw [fun_eq]
    rw [L153 3 t g g_nonconstant]
    change HasCircuitSize 3 (fun y : Fin 3 → Bool =>
      (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)) t ↔ 6 ≤ t + 2
    rw [L100 t]
    omega
  by_cases hs : 2 ≤ s
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hs
    subst ht
    simpa [Nat.add_comm] using hmain t
  · have hs2 : s < 2 := by omega
    constructor
    · intro h
      obtain ⟨C, hfan, hsize, heval⟩ := h
      have h2 : PEqualNP.MetaComplexity.HasCircuitSize 5
          (fun x : Fin 5 → Bool =>
            (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) 2 :=
        ⟨C, hfan, le_trans hsize (by omega), heval⟩
      have := (hmain 0).mp h2
      omega
    · intro h6
      omega
