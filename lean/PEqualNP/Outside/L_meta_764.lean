import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764_aux

private def tri : (Fin 3 → Bool) → Bool :=
  fun x => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

private def triEdge : (Fin 5 → Bool) → Bool :=
  fun x => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)

private lemma tri_nonconst : ∃ y y' : Fin 3 → Bool, tri y ≠ tri y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

private lemma triEdge_eq :
    triEdge =
      (fun x : Fin (2 + 3) → Bool =>
        (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) ||
          tri (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
  funext x
  simp [triEdge, tri, Bool.or_assoc]

private lemma hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ}
    (h : PEqualNP.MetaComplexity.HasCircuitSize n f s) (hst : s ≤ t) :
    PEqualNP.MetaComplexity.HasCircuitSize n f t := by
  rcases h with ⟨C, hfan, hsize, heval⟩
  exact ⟨C, hfan, le_trans hsize hst, heval⟩

end PEqualNP.Outside.L_meta_764_aux

open PEqualNP.Outside.L_meta_764_aux in
theorem PEqualNP.Outside.L_meta_764 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔
      6 ≤ s := by
  intro s
  have hiff : ∀ k : ℕ,
      PEqualNP.MetaComplexity.HasCircuitSize 5 triEdge (k + 2) ↔ 4 ≤ k := by
    intro k
    rw [triEdge_eq, PEqualNP.MetaComplexity.L153 3 k tri tri_nonconst]
    exact PEqualNP.MetaComplexity.L100 k
  by_cases hs : 2 ≤ s
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hs
    change PEqualNP.MetaComplexity.HasCircuitSize 5 triEdge (k + 2) ↔ 6 ≤ k + 2
    rw [hiff k]
    omega
  · constructor
    · intro h
      have h2 : PEqualNP.MetaComplexity.HasCircuitSize 5 triEdge (0 + 2) :=
        hasCircuitSize_mono h (by omega)
      have h4 : 4 ≤ 0 := (hiff 0).mp h2
      omega
    · intro h
      omega
