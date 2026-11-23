import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764

def g (y : Fin 3 → Bool) : Bool := (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)

def f (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)

lemma g_nonconst : ∃ y y' : Fin 3 → Bool, g y ≠ g y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

lemma g_size (t : ℕ) :
    PEqualNP.MetaComplexity.HasCircuitSize 3 g t ↔ 4 ≤ t := by
  unfold g
  exact PEqualNP.MetaComplexity.L100 t

lemma cast0 : (Fin.castAdd 3 (0 : Fin 2) : Fin 5) = 0 := by decide

lemma cast1 : (Fin.castAdd 3 (1 : Fin 2) : Fin 5) = 1 := by decide

lemma nat0 : (Fin.natAdd 2 (0 : Fin 3) : Fin 5) = 2 := by decide

lemma nat1 : (Fin.natAdd 2 (1 : Fin 3) : Fin 5) = 3 := by decide

lemma nat2 : (Fin.natAdd 2 (2 : Fin 3) : Fin 5) = 4 := by decide

lemma bor_reassoc (a b c d e : Bool) :
    ((a && b) || (c && d) || (d && e) || (c && e)) =
      ((a && b) || ((c && d) || (d && e) || (c && e))) := by
  decide +revert

lemma f_eval (x : Fin 5 → Bool) :
    f x =
      ((x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
        g (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
  have hg :
      g (fun j : Fin 3 => x (Fin.natAdd 2 j)) =
        ((x (Fin.natAdd 2 (0 : Fin 3)) && x (Fin.natAdd 2 (1 : Fin 3))) ||
          (x (Fin.natAdd 2 (1 : Fin 3)) && x (Fin.natAdd 2 (2 : Fin 3))) ||
          (x (Fin.natAdd 2 (0 : Fin 3)) && x (Fin.natAdd 2 (2 : Fin 3)))) := by
    unfold g
    rfl
  rw [hg, nat0, nat1, nat2, cast0, cast1]
  simpa [f] using bor_reassoc (x 0) (x 1) (x 2) (x 3) (x 4)

lemma mono {n t u : ℕ} {h : (Fin n → Bool) → Bool}
    (hs : PEqualNP.MetaComplexity.HasCircuitSize n h t) (hle : t ≤ u) :
    PEqualNP.MetaComplexity.HasCircuitSize n h u := by
  rcases hs with ⟨C, hF, hsz, hev⟩
  exact ⟨C, hF, le_trans hsz hle, hev⟩

lemma link (t : ℕ) :
    PEqualNP.MetaComplexity.HasCircuitSize 5 f (t + 2) ↔ 4 ≤ t := by
  constructor
  · intro hs
    have hfun :
        PEqualNP.MetaComplexity.HasCircuitSize 5
          (fun x : Fin 5 → Bool =>
            (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
              g (fun j : Fin 3 => x (Fin.natAdd 2 j))) (t + 2) := by
      rcases hs with ⟨C, hF, hsz, hev⟩
      refine ⟨C, hF, hsz, ?_⟩
      intro x
      rw [hev x, f_eval x]
    have hg := (PEqualNP.MetaComplexity.L153 3 t g g_nonconst).mp hfun
    exact (g_size t).mp hg
  · intro ht
    have hg := (g_size t).mpr ht
    have hfun := (PEqualNP.MetaComplexity.L153 3 t g g_nonconst).mpr hg
    rcases hfun with ⟨C, hF, hsz, hev⟩
    refine ⟨C, hF, hsz, ?_⟩
    intro x
    rw [hev x, f_eval x]

end PEqualNP.Outside.L_meta_764

theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  intro s
  have hdef :
      (fun x : Fin 5 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) =
        PEqualNP.Outside.L_meta_764.f := by
    rfl
  rw [hdef]
  by_cases h2 : 2 ≤ s
  · have hs : s = (s - 2) + 2 := by omega
    rw [hs]
    have hlink := PEqualNP.Outside.L_meta_764.link (s - 2)
    have hnum : 4 ≤ s - 2 ↔ 6 ≤ (s - 2) + 2 := by omega
    exact Iff.trans hlink hnum
  · constructor
    · intro hs
      have hle : s ≤ 2 := by omega
      have h2sz := PEqualNP.Outside.L_meta_764.mono hs hle
      have : 4 ≤ 0 := (PEqualNP.Outside.L_meta_764.link 0).mp h2sz
      omega
    · intro h6
      omega
