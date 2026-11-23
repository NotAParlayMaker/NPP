import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765_aux

private def cyc4 : (Fin 4 → Bool) → Bool :=
  fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)

private def cyc4Edge : (Fin 6 → Bool) → Bool :=
  fun x => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)

private lemma cyc4_nonconst : ∃ y y' : Fin 4 → Bool, cyc4 y ≠ cyc4 y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

private lemma cyc4Edge_eq :
    cyc4Edge =
      (fun x : Fin (2 + 4) → Bool =>
        (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) ||
          cyc4 (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
  funext x
  simp [cyc4Edge, cyc4, Bool.or_assoc]

private lemma hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ}
    (h : PEqualNP.MetaComplexity.HasCircuitSize n f s) (hst : s ≤ t) :
    PEqualNP.MetaComplexity.HasCircuitSize n f t := by
  rcases h with ⟨C, hfan, hsize, heval⟩
  exact ⟨C, hfan, le_trans hsize hst, heval⟩

end PEqualNP.Outside.L_meta_765_aux

open PEqualNP.Outside.L_meta_765_aux in
theorem PEqualNP.Outside.L_meta_765 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔
      5 ≤ s := by
  intro s
  have hiff : ∀ k : ℕ,
      PEqualNP.MetaComplexity.HasCircuitSize 6 cyc4Edge (k + 2) ↔ 3 ≤ k := by
    intro k
    rw [cyc4Edge_eq, PEqualNP.MetaComplexity.L153 4 k cyc4 cyc4_nonconst]
    exact PEqualNP.MetaComplexity.L112 k
  by_cases hs : 2 ≤ s
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hs
    change PEqualNP.MetaComplexity.HasCircuitSize 6 cyc4Edge (k + 2) ↔ 5 ≤ k + 2
    rw [hiff k]
    omega
  · constructor
    · intro h
      have h2 : PEqualNP.MetaComplexity.HasCircuitSize 6 cyc4Edge (0 + 2) :=
        hasCircuitSize_mono h (by omega)
      have h3 : 3 ≤ 0 := (hiff 0).mp h2
      omega
    · intro h
      omega
