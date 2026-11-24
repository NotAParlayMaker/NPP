import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764

theorem hasCircuitSize_mono {n s₁ s₂ : ℕ} {f : (Fin n → Bool) → Bool}
    (h : PEqualNP.MetaComplexity.HasCircuitSize n f s₁) (hle : s₁ ≤ s₂) :
    PEqualNP.MetaComplexity.HasCircuitSize n f s₂ := by
  unfold PEqualNP.MetaComplexity.HasCircuitSize at h
  unfold PEqualNP.MetaComplexity.HasCircuitSize
  rcases h with ⟨C, hfan, hsize, heval⟩
  exact ⟨C, hfan, Nat.le_trans hsize hle, heval⟩

def g : (Fin 3 → Bool) → Bool :=
  fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

theorem g_nonconst : ∃ y y' : Fin 3 → Bool, g y ≠ g y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

theorem bool_eq :
    ∀ a0 a1 a2 a3 a4 : Bool,
      ((a0 && a1) || (a2 && a3) || (a3 && a4) || (a2 && a4)) =
        ((a0 && a1) || ((a2 && a3) || (a3 && a4) || (a2 && a4))) := by
  decide

theorem target_eq :
    (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) =
      (fun x : Fin (2 + 3) → Bool =>
        (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
          g (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
  have hc0 : Fin.castAdd 3 (0 : Fin 2) = (0 : Fin 5) := by decide
  have hc1 : Fin.castAdd 3 (1 : Fin 2) = (1 : Fin 5) := by decide
  have hn0 : Fin.natAdd 2 (0 : Fin 3) = (2 : Fin 5) := by decide
  have hn1 : Fin.natAdd 2 (1 : Fin 3) = (3 : Fin 5) := by decide
  have hn2 : Fin.natAdd 2 (2 : Fin 3) = (4 : Fin 5) := by decide
  funext x
  dsimp only [g]
  rw [hc0, hc1, hn0, hn1, hn2]
  exact bool_eq (x 0) (x 1) (x 2) (x 3) (x 4)

theorem target_iff (t : ℕ) :
    PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4))
        (t + 2) ↔
      4 ≤ t := by
  rw [target_eq]
  have h1 :
      PEqualNP.MetaComplexity.HasCircuitSize (2 + 3)
          (fun x : Fin (2 + 3) → Bool =>
            (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
              g (fun j : Fin 3 => x (Fin.natAdd 2 j)))
          (t + 2) ↔
        PEqualNP.MetaComplexity.HasCircuitSize 3 g t :=
    PEqualNP.MetaComplexity.L153 3 t g g_nonconst
  have h2 : PEqualNP.MetaComplexity.HasCircuitSize 3 g t ↔ 4 ≤ t :=
    PEqualNP.MetaComplexity.L100 t
  exact h1.trans h2

end PEqualNP.Outside.L_meta_764

theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  intro s
  constructor
  · intro hs
    by_contra hnot
    have hle : s ≤ 3 + 2 := by omega
    have hs5 :
        PEqualNP.MetaComplexity.HasCircuitSize 5
          (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4))
          (3 + 2) :=
      PEqualNP.Outside.L_meta_764.hasCircuitSize_mono hs hle
    have h43 : 4 ≤ 3 := (PEqualNP.Outside.L_meta_764.target_iff 3).mp hs5
    omega
  · intro hs
    have h4 : 4 ≤ s - 2 := by omega
    have hs2 :
        PEqualNP.MetaComplexity.HasCircuitSize 5
          (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4))
          ((s - 2) + 2) :=
      (PEqualNP.Outside.L_meta_764.target_iff (s - 2)).mpr h4
    have heq : (s - 2) + 2 = s := by omega
    rw [heq] at hs2
    exact hs2
