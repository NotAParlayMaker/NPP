import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765_aux

open PEqualNP.MetaComplexity

private def g : (Fin 4 → Bool) → Bool :=
  fun y => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)

private lemma g_nc : ∃ y y' : Fin 4 → Bool, g y ≠ g y' := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  decide

private lemma fun_eq :
    (fun x : Fin 6 → Bool =>
      (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) ||
        g (fun j : Fin 4 => x (Fin.natAdd 2 j))) =
      (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) := by
  funext x
  simp [g, Fin.natAdd, Fin.castAdd]
  simp [Bool.or_assoc]

private lemma not_two :
    ¬ HasCircuitSize 6
      (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) 2 := by
  intro h2
  have h153 := PEqualNP.MetaComplexity.L153 4 0 g g_nc
  rw [fun_eq] at h153
  have hg : HasCircuitSize 4 g 0 := h153.mp h2
  have h112 := PEqualNP.MetaComplexity.L112 0
  exact (by omega : ¬ 3 ≤ 0) (h112.mp hg)

private lemma mono {s : ℕ} (hs : s ≤ 2) :
    HasCircuitSize 6
      (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s →
    HasCircuitSize 6
      (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) 2 := by
  rintro ⟨C, hfan, hsize, hev⟩
  exact ⟨C, hfan, by omega, hev⟩

end PEqualNP.Outside.L_meta_765_aux

open PEqualNP.Outside.L_meta_765_aux

theorem PEqualNP.Outside.L_meta_765 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔
      5 ≤ s := by
  intro s
  by_cases hs : 2 ≤ s
  · have h153 := PEqualNP.MetaComplexity.L153 4 (s - 2) g g_nc
    rw [fun_eq] at h153
    rw [show s - 2 + 2 = s by omega] at h153
    rw [h153]
    change PEqualNP.MetaComplexity.HasCircuitSize 4
      (fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)) (s - 2) ↔ 5 ≤ s
    rw [PEqualNP.MetaComplexity.L112 (s - 2)]
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
