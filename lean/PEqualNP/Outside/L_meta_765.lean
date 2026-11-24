import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The edge function of a 4-cycle, in the form of `L112`. -/
def g : (Fin 4 → Bool) → Bool :=
  fun y => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)

/-- The 4-cycle-and-edge function. -/
def f : (Fin 6 → Bool) → Bool :=
  fun x => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)

lemma g_nonconstant : ∃ y y' : Fin 4 → Bool, g y ≠ g y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

/-- The 4-cycle-and-edge function is the `L153` shape: one rigid AND followed by the 4-cycle. -/
lemma fun_eq :
    f = (fun x : Fin 6 → Bool =>
      (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) ||
        g (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
  funext x
  revert x
  decide

end PEqualNP.Outside.L_meta_765_aux

open PEqualNP.Outside.L_meta_765_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_765 :
    ∀ s : ℕ,
      PEqualNP.MetaComplexity.HasCircuitSize 6
        (fun x : Fin 6 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
            (x 5 && x 2)) s ↔
        5 ≤ s := by
  change ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 f s ↔ 5 ≤ s
  intro s
  have hmain : ∀ t : ℕ,
      PEqualNP.MetaComplexity.HasCircuitSize 6 f (t + 2) ↔ 5 ≤ t + 2 := by
    intro t
    rw [fun_eq]
    rw [L153 4 t g g_nonconstant]
    change PEqualNP.MetaComplexity.HasCircuitSize 4 (fun y : Fin 4 → Bool =>
      (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)) t ↔ 5 ≤ t + 2
    rw [L112 t]
    omega
  by_cases hs : 2 ≤ s
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hs
    subst ht
    simpa [Nat.add_comm] using hmain t
  · have hs2 : s < 2 := by omega
    constructor
    · intro h
      obtain ⟨C, hfan, hsize, heval⟩ := h
      have h2 : PEqualNP.MetaComplexity.HasCircuitSize 6 f 2 :=
        ⟨C, hfan, le_trans hsize (by omega), heval⟩
      have := (hmain 0).mp h2
      omega
    · intro h5
      omega
