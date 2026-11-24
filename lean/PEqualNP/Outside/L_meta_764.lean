import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_764

def G : (Fin 3 → Bool) → Bool :=
  fun y => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)

theorem G_nonconst : ∃ y y' : Fin 3 → Bool, G y ≠ G y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

theorem G_size (t : ℕ) : HasCircuitSize 3 G t ↔ 4 ≤ t := by
  unfold G
  exact PEqualNP.MetaComplexity.L100 t

theorem Gform :
    (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4))
      = (fun x : Fin 5 → Bool =>
          (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
            G (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
  funext x
  unfold G
  beta_reduce
  ac_rfl

end PEqualNP.Outside.L_meta_764

theorem PEqualNP.Outside.L_meta_764 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  intro s
  rw [PEqualNP.Outside.L_meta_764.Gform]
  by_cases hs : 2 ≤ s
  · obtain ⟨t, ht⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    rw [ht]
    have h153 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool =>
          (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
            PEqualNP.Outside.L_meta_764.G (fun j : Fin 3 => x (Fin.natAdd 2 j))) (t + 2) ↔
        PEqualNP.MetaComplexity.HasCircuitSize 3 PEqualNP.Outside.L_meta_764.G t :=
      PEqualNP.MetaComplexity.L153 3 t PEqualNP.Outside.L_meta_764.G PEqualNP.Outside.L_meta_764.G_nonconst
    rw [h153, PEqualNP.Outside.L_meta_764.G_size t]
    omega
  · have hnot : ¬ 6 ≤ s := by omega
    constructor
    · intro h
      have h2 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool =>
          (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
            PEqualNP.Outside.L_meta_764.G (fun j : Fin 3 => x (Fin.natAdd 2 j))) 2 := by
        obtain ⟨C, hfan, hsize, hval⟩ := h
        exact ⟨C, hfan, by omega, hval⟩
      have h153 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool =>
          (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
            PEqualNP.Outside.L_meta_764.G (fun j : Fin 3 => x (Fin.natAdd 2 j))) (0 + 2) ↔
        PEqualNP.MetaComplexity.HasCircuitSize 3 PEqualNP.Outside.L_meta_764.G 0 :=
        PEqualNP.MetaComplexity.L153 3 0 PEqualNP.Outside.L_meta_764.G PEqualNP.Outside.L_meta_764.G_nonconst
      have h30 : PEqualNP.MetaComplexity.HasCircuitSize 3 PEqualNP.Outside.L_meta_764.G 0 :=
        h153.mp (by simpa using h2)
      have hzero : 4 ≤ 0 := (PEqualNP.Outside.L_meta_764.G_size 0).mp h30
      omega
    · intro h6
      exact absurd h6 hnot
