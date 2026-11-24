import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

theorem PEqualNP.Outside.L_meta_764 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔
      6 ≤ s := by
  intro s
  let g : (Fin 3 → Bool) → Bool := fun y => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)
  let F : (Fin 5 → Bool) → Bool :=
    fun x => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)
  have hnc : ∃ y y' : Fin 3 → Bool, g y ≠ g y' := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    simp [g]
  have hf : F = (fun x : Fin 5 → Bool =>
      (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || g (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
    funext x
    simp only [F, g, Fin.castAdd, Fin.natAdd, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.add_mod_mod]
    simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  have key : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 F (t + 2) ↔ 4 ≤ t := by
    intro t
    rw [hf]
    exact (PEqualNP.MetaComplexity.L153 3 t g hnc).trans (PEqualNP.MetaComplexity.L100 t)
  have mono : ∀ {a b : ℕ}, a ≤ b → PEqualNP.MetaComplexity.HasCircuitSize 5 F a →
      PEqualNP.MetaComplexity.HasCircuitSize 5 F b := by
    rintro a b hab ⟨C, hfan, hsize, hev⟩
    exact ⟨C, hfan, hsize.trans hab, hev⟩
  constructor
  · intro h
    by_contra h6
    push_neg at h6
    rcases Nat.lt_or_ge s 2 with hs | hs
    · have h2 : PEqualNP.MetaComplexity.HasCircuitSize 5 F 2 := mono (by omega) h
      have := (key 0).mp (by simpa using h2)
      omega
    · have hs' : s - 2 + 2 = s := by omega
      have h' : PEqualNP.MetaComplexity.HasCircuitSize 5 F ((s - 2) + 2) := by
        rw [hs']; exact h
      have := (key (s - 2)).mp h'
      omega
  · intro h6
    have h4 : 4 ≤ s - 2 := by omega
    have hs' : s - 2 + 2 = s := by omega
    have : PEqualNP.MetaComplexity.HasCircuitSize 5 F ((s - 2) + 2) := (key (s - 2)).mpr h4
    rw [hs'] at this
    exact this
