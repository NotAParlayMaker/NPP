import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764_aux

open PEqualNP.MetaComplexity

private def g : (Fin 3 → Bool) → Bool :=
  fun y => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)

private lemma g_nc : ∃ y y' : Fin 3 → Bool, g y ≠ g y' := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  decide

private lemma fun_eq :
    (fun x : Fin 5 → Bool =>
      (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
        g (fun j : Fin 3 => x (Fin.natAdd 2 j))) =
      (fun x : Fin 5 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) := by
  funext x
  simp [g, Fin.natAdd, Fin.castAdd]
  simp [Bool.or_assoc]

private lemma not_two :
    ¬ HasCircuitSize 5
      (fun x : Fin 5 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) 2 := by
  intro h2
  have h153 := PEqualNP.MetaComplexity.L153 3 0 g g_nc
  rw [fun_eq] at h153
  have hg : HasCircuitSize 3 g 0 := h153.mp h2
  have h100 := PEqualNP.MetaComplexity.L100 0
  exact (by omega : ¬ 4 ≤ 0) (h100.mp hg)

private lemma mono {s : ℕ} (hs : s ≤ 2) :
    HasCircuitSize 5
      (fun x : Fin 5 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s →
    HasCircuitSize 5
      (fun x : Fin 5 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) 2 := by
  rintro ⟨C, hfan, hsize, hev⟩
  exact ⟨C, hfan, by omega, hev⟩

end PEqualNP.Outside.L_meta_764_aux

open PEqualNP.Outside.L_meta_764_aux

theorem PEqualNP.Outside.L_meta_764 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔
      6 ≤ s := by
  intro s
  by_cases hs : 2 ≤ s
  · have h153 := PEqualNP.MetaComplexity.L153 3 (s - 2) g g_nc
    rw [fun_eq] at h153
    rw [show s - 2 + 2 = s by omega] at h153
    rw [h153]
    change PEqualNP.MetaComplexity.HasCircuitSize 3
      (fun y : Fin 3 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)) (s - 2) ↔ 6 ≤ s
    rw [PEqualNP.MetaComplexity.L100 (s - 2)]
    omega
  · have hs01 : s = 0 ∨ s = 1 := by omega
    rcases hs01 with rfl | rfl
    · constructor
      · intro h0
        exfalso
        exact not_two (mono (by omega) h0)
      · omega
    · constructor
      · intro h1
        exfalso
        exact not_two (mono (by omega) h1)
      · omega
