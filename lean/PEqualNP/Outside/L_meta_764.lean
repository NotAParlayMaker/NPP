import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764

private abbrev g (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

private lemma g_nonconst : ∃ y y' : Fin 3 → Bool, g y ≠ g y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

private lemma f_eq :
    (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) =
    (fun x : Fin (2 + 3) → Bool =>
      (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || g (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
  funext x
  change ((x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) =
    ((x 0 && x 1) || ((x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)))
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> rfl

private lemma main (s : ℕ) :
    PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔
      6 ≤ s := by
  rw [f_eq]
  by_cases hs : 2 ≤ s
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    rw [PEqualNP.MetaComplexity.L153 3 t g g_nonconst]
    exact (PEqualNP.MetaComplexity.L100 t).trans (by omega)
  · constructor
    · rintro ⟨C, hft, hsz, hev⟩
      have h2 : PEqualNP.MetaComplexity.HasCircuitSize (2 + 3)
          (fun x : Fin (2 + 3) → Bool =>
            (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || g (fun j : Fin 3 => x (Fin.natAdd 2 j)))
          (0 + 2) :=
        ⟨C, hft, by omega, hev⟩
      rw [PEqualNP.MetaComplexity.L153 3 0 g g_nonconst] at h2
      have h4 := (PEqualNP.MetaComplexity.L100 0).mp h2
      omega
    · intro h6; omega

end PEqualNP.Outside.L_meta_764

theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s :=
  PEqualNP.Outside.L_meta_764.main
