import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764

def tri : (Fin 3 → Bool) → Bool :=
  fun y => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)

def big : (Fin 5 → Bool) → Bool :=
  fun x => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)

lemma big_eq (x : Fin 5 → Bool) :
    big x = ((x 0 && x 1) || tri (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
  simp only [big, tri, Fin.natAdd, Fin.castAdd]
  simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

lemma tri_nonconst : ∃ y y' : Fin 3 → Bool, tri y ≠ tri y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

lemma step (t : ℕ) :
    PEqualNP.MetaComplexity.HasCircuitSize 5 big (t + 2) ↔ 4 ≤ t := by
  have hfun : big = (fun x : Fin (2 + 3) → Bool =>
      (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || tri (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
    funext x
    exact big_eq x
  rw [hfun, PEqualNP.MetaComplexity.L153 3 t tri tri_nonconst]
  exact PEqualNP.MetaComplexity.L100 t

lemma mono (s : ℕ) (hs : PEqualNP.MetaComplexity.HasCircuitSize 5 big s) :
    PEqualNP.MetaComplexity.HasCircuitSize 5 big (s + 2) := by
  obtain ⟨C, hfan, hsize, hfun⟩ := hs
  exact ⟨C, hfan, Nat.le_trans hsize (Nat.le_add_right s 2), hfun⟩

end PEqualNP.Outside.L_meta_764

theorem PEqualNP.Outside.L_meta_764 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  show ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 PEqualNP.Outside.L_meta_764.big s ↔ 6 ≤ s
  intro s
  rcases Nat.lt_or_ge s 2 with hs | hs
  · have hs01 : s = 0 ∨ s = 1 := by omega
    rcases hs01 with rfl | rfl
    · constructor
      · intro h
        have h2 : PEqualNP.MetaComplexity.HasCircuitSize 5 PEqualNP.Outside.L_meta_764.big (0 + 2) :=
          PEqualNP.Outside.L_meta_764.mono 0 h
        have h4 : 4 ≤ (0 : ℕ) := (PEqualNP.Outside.L_meta_764.step 0).1 h2
        omega
      · intro h6
        omega
    · constructor
      · intro h
        have h2 : PEqualNP.MetaComplexity.HasCircuitSize 5 PEqualNP.Outside.L_meta_764.big (1 + 2) :=
          PEqualNP.Outside.L_meta_764.mono 1 h
        have h4 : 4 ≤ (1 : ℕ) := (PEqualNP.Outside.L_meta_764.step 1).1 h2
        omega
      · intro h6
        omega
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    rw [PEqualNP.Outside.L_meta_764.step t]
    omega
