import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.ExactCycle4

theorem PEqualNP.Outside.L_meta_765 : ∀ s : ℕ,
    PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔
      5 ≤ s := by
  intro s
  have hnc : ∃ y y' : Fin 4 → Bool, cyc4 y ≠ cyc4 y' := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    decide
  have hF :
      (fun x : Fin (2 + 4) → Bool =>
          (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) ||
            cyc4 (fun j : Fin 4 => x (Fin.natAdd 2 j))) =
        (fun x : Fin 6 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) := by
    funext x
    simp [cyc4, Bool.or_assoc]
  have mono : ∀ {a b : ℕ}, a ≤ b →
      PEqualNP.MetaComplexity.HasCircuitSize 6
        (fun x : Fin 6 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) a →
      PEqualNP.MetaComplexity.HasCircuitSize 6
        (fun x : Fin 6 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) b := by
    rintro a b hab ⟨C, hC, hsz, hev⟩
    exact ⟨C, hC, le_trans hsz hab, hev⟩
  by_cases hs : 2 ≤ s
  · have h := PEqualNP.MetaComplexity.L153 4 (s - 2) cyc4 hnc
    rw [hF] at h
    unfold cyc4 at h
    have h112 := PEqualNP.MetaComplexity.L112 (s - 2)
    rw [h112] at h
    have hs' : s = (s - 2) + 2 := by omega
    have h' : PEqualNP.MetaComplexity.HasCircuitSize 6
        (fun x : Fin 6 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2))
        ((s - 2) + 2) ↔ 3 ≤ s - 2 := by
      simpa using h
    rw [hs', h']
    omega
  · have hno : ¬ PEqualNP.MetaComplexity.HasCircuitSize 6
        (fun x : Fin 6 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s := by
      intro hc
      have hc2 : PEqualNP.MetaComplexity.HasCircuitSize 6
          (fun x : Fin 6 → Bool =>
            (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) 2 :=
        mono (by omega) hc
      have h := PEqualNP.MetaComplexity.L153 4 0 cyc4 hnc
      rw [hF] at h
      unfold cyc4 at h
      have h112 := PEqualNP.MetaComplexity.L112 0
      rw [h112] at h
      have : 3 ≤ 0 := h.mp (by simpa using hc2)
      omega
    exact iff_of_false hno (by omega)
