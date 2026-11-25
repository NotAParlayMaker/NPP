import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765

def quad : (Fin 4 → Bool) → Bool :=
  fun y => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)

def big : (Fin 6 → Bool) → Bool :=
  fun x => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)

lemma big_eq (x : Fin 6 → Bool) :
    big x = ((x 0 && x 1) || quad (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
  simp only [big, quad, Fin.natAdd, Fin.castAdd]
  simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

lemma quad_nonconst : ∃ y y' : Fin 4 → Bool, quad y ≠ quad y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

lemma step (t : ℕ) :
    PEqualNP.MetaComplexity.HasCircuitSize 6 big (t + 2) ↔ 3 ≤ t := by
  have hfun : big = (fun x : Fin (2 + 4) → Bool =>
      (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || quad (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
    funext x
    exact big_eq x
  rw [hfun, PEqualNP.MetaComplexity.L153 4 t quad quad_nonconst]
  exact PEqualNP.MetaComplexity.L112 t

lemma mono (s : ℕ) (hs : PEqualNP.MetaComplexity.HasCircuitSize 6 big s) :
    PEqualNP.MetaComplexity.HasCircuitSize 6 big (s + 2) := by
  obtain ⟨C, hfan, hsize, hfun⟩ := hs
  exact ⟨C, hfan, Nat.le_trans hsize (Nat.le_add_right s 2), hfun⟩

end PEqualNP.Outside.L_meta_765

theorem PEqualNP.Outside.L_meta_765 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s := by
  show ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 PEqualNP.Outside.L_meta_765.big s ↔ 5 ≤ s
  intro s
  rcases Nat.lt_or_ge s 2 with hs | hs
  · have hs01 : s = 0 ∨ s = 1 := by omega
    rcases hs01 with rfl | rfl
    · constructor
      · intro h
        have h2 : PEqualNP.MetaComplexity.HasCircuitSize 6 PEqualNP.Outside.L_meta_765.big (0 + 2) :=
          PEqualNP.Outside.L_meta_765.mono 0 h
        have h3 : 3 ≤ (0 : ℕ) := (PEqualNP.Outside.L_meta_765.step 0).1 h2
        omega
      · intro h5
        omega
    · constructor
      · intro h
        have h2 : PEqualNP.MetaComplexity.HasCircuitSize 6 PEqualNP.Outside.L_meta_765.big (1 + 2) :=
          PEqualNP.Outside.L_meta_765.mono 1 h
        have h3 : 3 ≤ (1 : ℕ) := (PEqualNP.Outside.L_meta_765.step 1).1 h2
        omega
      · intro h5
        omega
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    rw [PEqualNP.Outside.L_meta_765.step t]
    omega
