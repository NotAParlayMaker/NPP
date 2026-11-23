import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1452 : ∀ (n f k w : ℕ) (L : Finset (Fin n)) (c : Fin f → Fin n → Fin k) (T : Fin f → Fin k → (Fin n → Bool) → Bool), (∀ S : Finset (Fin n), S.card ≤ w → ∃ j0 : Fin f, Set.InjOn (c j0) (S : Set (Fin n))) → (∀ (j1 : Fin f) (a1 : Fin k) (u v : Fin n → Bool), u ≤ v → T j1 a1 u ≤ T j1 a1 v) → (∀ (j2 : Fin f) (a2 : Fin k) (z : Fin n → Bool), (∀ p2 : Fin n, z p2 = true → c j2 p2 ≠ a2) → T j2 a2 z = false) → (∀ (j3 : Fin f) (a3 : Fin k) (y : Fin n → Bool) (p3 : Fin n), y p3 = true → c j3 p3 = a3 → (∀ q3 : Fin n, y q3 = true → c j3 q3 = a3 → q3 = p3) → (T j3 a3 y = true ↔ p3 ∈ L)) → ∀ x : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ w → ((∀ j : Fin f, ∃ a : Fin k, T j a x = true) ↔ ∃ p : Fin n, x p = true ∧ p ∈ L) := by
  intro n f k w L c T split mono empty single x size
  let S := Finset.univ.filter (fun i : Fin n => x i = true)
  have memS (p : Fin n) : p ∈ S ↔ x p = true := by simp [S]
  constructor
  · intro h
    obtain ⟨j, inj⟩ := split S size
    obtain ⟨a, ha⟩ := h j
    by_cases present : ∃ p : Fin n, x p = true ∧ c j p = a
    · obtain ⟨p, hp, col⟩ := present
      refine ⟨p, hp, (single j a x p hp col ?_).mp ha⟩
      intro q hq hcol
      exact inj ((memS q).mpr hq) ((memS p).mpr hp) (hcol.trans col.symm)
    · have off := empty j a x (fun p hp col => present ⟨p, hp, col⟩)
      simp [ha] at off
  · rintro ⟨p, hp, inL⟩ j
    let y : Fin n → Bool := fun i => decide (i = p)
    have yp : y p = true := by simp [y]
    have test := (single j (c j p) y p yp rfl (fun q hq _ => by simpa [y] using hq)).mpr inL
    have le : y ≤ x := by
      intro i
      by_cases e : i = p
      · subst i
        simp [yp, hp]
      · simp [y, e]
    refine ⟨c j p, ?_⟩
    have raised := mono j (c j p) y x le
    rw [test] at raised
    exact le_antisymm (by cases T j (c j p) x <;> decide) raised
