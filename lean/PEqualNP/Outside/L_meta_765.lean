import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765

private abbrev g (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)

private lemma g_nonconst : ∃ y y' : Fin 4 → Bool, g y ≠ g y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

private lemma f_eq :
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) =
    (fun x : Fin (2 + 4) → Bool =>
      (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || g (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
  funext x
  change ((x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) =
    ((x 0 && x 1) || ((x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)))
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl

private lemma main (s : ℕ) :
    PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔
      5 ≤ s := by
  rw [f_eq]
  by_cases hs : 2 ≤ s
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    rw [PEqualNP.MetaComplexity.L153 4 t g g_nonconst]
    exact (PEqualNP.MetaComplexity.L112 t).trans (by omega)
  · constructor
    · rintro ⟨C, hft, hsz, hev⟩
      have h2 : PEqualNP.MetaComplexity.HasCircuitSize (2 + 4)
          (fun x : Fin (2 + 4) → Bool =>
            (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || g (fun j : Fin 4 => x (Fin.natAdd 2 j)))
          (0 + 2) :=
        ⟨C, hft, by omega, hev⟩
      rw [PEqualNP.MetaComplexity.L153 4 0 g g_nonconst] at h2
      have h3 := (PEqualNP.MetaComplexity.L112 0).mp h2
      omega
    · intro h5; omega

end PEqualNP.Outside.L_meta_765

theorem PEqualNP.Outside.L_meta_765 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s :=
  PEqualNP.Outside.L_meta_765.main
