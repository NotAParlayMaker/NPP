import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.ExactMaj3

theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ,
    PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔
      6 ≤ s := by
  intro s
  have hnc : ∃ y y' : Fin 3 → Bool, maj3 y ≠ maj3 y' := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    decide
  have hF :
      (fun x : Fin (2 + 3) → Bool =>
          (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
            maj3 (fun j : Fin 3 => x (Fin.natAdd 2 j))) =
        (fun x : Fin 5 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) := by
    funext x
    simp [maj3, Bool.or_assoc]
  have mono : ∀ {a b : ℕ}, a ≤ b →
      PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) a →
      PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) b := by
    rintro a b hab ⟨C, hC, hsz, hev⟩
    exact ⟨C, hC, le_trans hsz hab, hev⟩
  by_cases hs : 2 ≤ s
  · have h := PEqualNP.MetaComplexity.L153 3 (s - 2) maj3 hnc
    rw [hF] at h
    unfold maj3 at h
    have h100 := PEqualNP.MetaComplexity.L100 (s - 2)
    rw [h100] at h
    have hs' : s = (s - 2) + 2 := by omega
    have h' : PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4))
        ((s - 2) + 2) ↔ 4 ≤ s - 2 := by
      simpa using h
    rw [hs', h']
    omega
  · have hno : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s := by
      intro hc
      have hc2 : PEqualNP.MetaComplexity.HasCircuitSize 5
          (fun x : Fin 5 → Bool =>
            (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) 2 :=
        mono (by omega) hc
      have h := PEqualNP.MetaComplexity.L153 3 0 maj3 hnc
      rw [hF] at h
      unfold maj3 at h
      have h100 := PEqualNP.MetaComplexity.L100 0
      rw [h100] at h
      have : 4 ≤ 0 := h.mp (by simpa using hc2)
      omega
    exact iff_of_false hno (by omega)
