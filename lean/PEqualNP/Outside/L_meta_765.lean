import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765

def g : (Fin 4 → Bool) → Bool :=
  fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)

def f : (Fin 6 → Bool) → Bool :=
  fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)

lemma g_nonconstant : ∃ y y' : Fin 4 → Bool, g y ≠ g y' := by
  use (fun _ => false), (fun _ => true)
  decide

lemma f_eq (x : Fin 6 → Bool) :
    f x = ((x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || g (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
  dsimp [f, g]
  simp [Bool.or_assoc]

lemma f_fun_eq :
    f = (fun x : Fin (2 + 4) → Bool => (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || g (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
  ext x
  exact f_eq x

theorem size_iff (s : ℕ) :
    PEqualNP.MetaComplexity.HasCircuitSize 6 f s ↔ 5 ≤ s := by
  rcases s with _ | _ | s'
  · have hmono : ¬ PEqualNP.MetaComplexity.HasCircuitSize 6 f 0 := by
      intro h
      have h2 : PEqualNP.MetaComplexity.HasCircuitSize 6 f (0 + 2) := by
        obtain ⟨C, hC, hsz, heval⟩ := h
        refine ⟨C, hC, by omega, heval⟩
      rw [f_fun_eq] at h2
      have hg := (PEqualNP.MetaComplexity.L153 4 0 g g_nonconstant).1 h2
      change PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)) 0 at hg
      have h3 := (PEqualNP.MetaComplexity.L112 0).1 hg
      omega
    simp [hmono]
  · have hmono : ¬ PEqualNP.MetaComplexity.HasCircuitSize 6 f 1 := by
      intro h
      have h2 : PEqualNP.MetaComplexity.HasCircuitSize 6 f (0 + 2) := by
        obtain ⟨C, hC, hsz, heval⟩ := h
        refine ⟨C, hC, by omega, heval⟩
      rw [f_fun_eq] at h2
      have hg := (PEqualNP.MetaComplexity.L153 4 0 g g_nonconstant).1 h2
      change PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)) 0 at hg
      have h3 := (PEqualNP.MetaComplexity.L112 0).1 hg
      omega
    simp [hmono]
  · rw [f_fun_eq]
    rw [PEqualNP.MetaComplexity.L153 4 s' g g_nonconstant]
    change PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)) s' ↔ 5 ≤ s' + 2
    rw [PEqualNP.MetaComplexity.L112 s']
    omega

end PEqualNP.Outside.L_meta_765

theorem PEqualNP.Outside.L_meta_765 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s :=
  PEqualNP.Outside.L_meta_765.size_iff
