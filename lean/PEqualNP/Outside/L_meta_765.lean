import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765

theorem hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ}
    (h : PEqualNP.MetaComplexity.HasCircuitSize n f s) (hst : s ≤ t) :
    PEqualNP.MetaComplexity.HasCircuitSize n f t := by
  dsimp only [PEqualNP.MetaComplexity.HasCircuitSize] at h ⊢
  rcases h with ⟨C, hfan, hsize, heval⟩
  exact ⟨C, hfan, le_trans hsize hst, heval⟩

theorem g4_nonconst :
    ∃ y y' : Fin 4 → Bool,
      (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)) y ≠
      (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)) y' := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  decide

theorem target_eq :
    (fun x : Fin (2 + 4) → Bool =>
      (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) ||
        (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0))
          (fun j : Fin 4 => x (Fin.natAdd 2 j))) =
    (fun x : Fin 6 → Bool =>
      (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) := by
  funext x
  dsimp only
  have h0 : Fin.castAdd 4 (0 : Fin 2) = (0 : Fin 6) := by decide
  have h1 : Fin.castAdd 4 (1 : Fin 2) = (1 : Fin 6) := by decide
  have h2 : Fin.natAdd 2 (0 : Fin 4) = (2 : Fin 6) := by decide
  have h3 : Fin.natAdd 2 (1 : Fin 4) = (3 : Fin 6) := by decide
  have h4 : Fin.natAdd 2 (2 : Fin 4) = (4 : Fin 6) := by decide
  have h5 : Fin.natAdd 2 (3 : Fin 4) = (5 : Fin 6) := by decide
  rw [h0, h1, h2, h3, h4, h5]
  have hbool : ∀ a0 a1 a2 a3 a4 a5 : Bool,
      ((a0 && a1) || ((a2 && a3) || (a3 && a4) || (a4 && a5) || (a5 && a2))) =
      ((a0 && a1) || (a2 && a3) || (a3 && a4) || (a4 && a5) || (a5 && a2)) := by
    decide
  exact hbool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

theorem step_iff (s : ℕ) :
    PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2))
      (s + 2) ↔
    PEqualNP.MetaComplexity.HasCircuitSize 4
      (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0))
      s := by
  have h := PEqualNP.MetaComplexity.L153 4 s
    (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0))
    g4_nonconst
  rw [target_eq] at h
  exact h

theorem size_add_two_iff (s : ℕ) :
    PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2))
      (s + 2) ↔
    3 ≤ s :=
  (step_iff s).trans (PEqualNP.MetaComplexity.L112 s)

end PEqualNP.Outside.L_meta_765

theorem PEqualNP.Outside.L_meta_765 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s := by
  intro s
  constructor
  · intro hs
    by_contra hlt
    have hs4 : s ≤ 4 := by omega
    have h32 : 3 ≤ 2 := (PEqualNP.Outside.L_meta_765.size_add_two_iff 2).mp
      (PEqualNP.Outside.L_meta_765.hasCircuitSize_mono hs hs4)
    omega
  · intro hs
    have h3 : 3 ≤ s - 2 := by omega
    have hadd : (s - 2) + 2 = s := by omega
    rw [← hadd]
    exact (PEqualNP.Outside.L_meta_765.size_add_two_iff (s - 2)).mpr h3
