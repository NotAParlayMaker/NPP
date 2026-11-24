import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764

open PEqualNP.MetaComplexity

private def g : (Fin 3 → Bool) → Bool :=
  fun y => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)

private lemma g_nonconstant : ∃ y y' : Fin 3 → Bool, g y ≠ g y' := by
  refine ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), ?_⟩
  decide

private lemma arg0 : (Fin.castAdd 3 (0 : Fin 2) : Fin 5) = 0 := by decide
private lemma arg1 : (Fin.castAdd 3 (1 : Fin 2) : Fin 5) = 1 := by decide
private lemma nat0 : (Fin.natAdd 2 (0 : Fin 3) : Fin 5) = 2 := by decide
private lemma nat1 : (Fin.natAdd 2 (1 : Fin 3) : Fin 5) = 3 := by decide
private lemma nat2 : (Fin.natAdd 2 (2 : Fin 3) : Fin 5) = 4 := by decide

private def shifted : (Fin 5 → Bool) → Bool :=
  fun x => (x (Fin.castAdd 3 (0 : Fin 2)) && x (Fin.castAdd 3 (1 : Fin 2))) ||
    g (fun j : Fin 3 => x (Fin.natAdd 2 j))

private lemma shape :
    (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) =
      shifted := by
  funext x
  apply Bool.eq_iff_iff.2
  simp only [shifted, g, arg0, arg1, nat0, nat1, nat2, Bool.and_eq_true, Bool.or_eq_true]
  tauto

end PEqualNP.Outside.L_meta_764

theorem PEqualNP.Outside.L_meta_764 :
    ∀ s : ℕ,
      PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔
        6 ≤ s := by
  intro s
  rw [PEqualNP.Outside.L_meta_764.shape]
  constructor
  · rintro ⟨C, hfan, hsz, hev⟩
    have hbig : PEqualNP.MetaComplexity.HasCircuitSize 5 PEqualNP.Outside.L_meta_764.shifted
        (max s 2) := ⟨C, hfan, le_trans hsz (le_max_left s 2), hev⟩
    obtain ⟨t, ht⟩ : ∃ t, max s 2 = t + 2 := ⟨max s 2 - 2, by omega⟩
    rw [ht] at hbig
    have h3 := (PEqualNP.MetaComplexity.L153 3 t PEqualNP.Outside.L_meta_764.g
      PEqualNP.Outside.L_meta_764.g_nonconstant).1 hbig
    have h4 : 4 ≤ t := (PEqualNP.MetaComplexity.L100 t).1 h3
    omega
  · intro hs
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    have ht : 4 ≤ t := by omega
    have h3 : PEqualNP.MetaComplexity.HasCircuitSize 3 PEqualNP.Outside.L_meta_764.g t :=
      (PEqualNP.MetaComplexity.L100 t).2 ht
    exact (PEqualNP.MetaComplexity.L153 3 t PEqualNP.Outside.L_meta_764.g
      PEqualNP.Outside.L_meta_764.g_nonconstant).2 h3
