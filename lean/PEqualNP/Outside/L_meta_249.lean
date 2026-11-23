import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta249

private lemma walk_ge {N k : ℕ} {E : Fin N → Fin N → Prop} {pos : Fin N → ℕ}
    (hk : 1 ≤ k)
    (hsym : ∀ u v : Fin N, E u v → E v u)
    (hnohub : ∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0)
    (hinner : ∀ v : Fin N, pos v ≠ 0 →
      pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧
        pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) :
    ∀ (L : ℕ) (w : ℕ → Fin N),
      pos (w 0) = 0 → pos (w L) = 0 → w 0 ≠ w L →
      (∀ i : ℕ, i < L → E (w i) (w (i + 1))) → 2 * k + 1 ≤ L := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro w h0 hL hne hedge
    have hLpos : 0 < L := by
      cases L with
      | zero => exact absurd rfl hne
      | succ n => exact Nat.succ_pos n
    by_cases hmid : ∃ i : ℕ, 0 < i ∧ i < L ∧ pos (w i) = 0
    · rcases hmid with ⟨i, hi0, hiL, hpi⟩
      by_cases hwi : w 0 = w i
      · have hsub := ih (L - i) (by omega) (fun t => w (i + t)) hpi
          (by simpa [Nat.add_sub_cancel' (le_of_lt hiL)] using hL)
          (by simpa [Nat.add_sub_cancel' (le_of_lt hiL), ← hwi] using hne)
          (fun t ht => by simpa [Nat.add_assoc] using hedge (i + t) (by omega))
        omega
      · have hsub := ih i hiL w h0 hpi hwi (fun t ht => hedge t (by omega))
        omega
    · by_cases hbt : ∃ i : ℕ, 0 < i ∧ i < L ∧ w (i - 1) = w (i + 1)
      · rcases hbt with ⟨i, hi0, hiL, hback⟩
        let w' : ℕ → Fin N := fun t => if t < i then w t else w (t + 2)
        have hL2 : 2 ≤ L := by omega
        have hw'0 : w' 0 = w 0 := by simp [w', hi0]
        have hw'L : w' (L - 2) = w L := by
          dsimp only [w']
          split_ifs with hlt
          · have hiEq : i = L - 1 := by omega
            have h1 : L - 2 = i - 1 := by omega
            have h2 : i + 1 = L := by omega
            rw [h1, hback, h2]
          · congr 1
            omega
        have hw'edge : ∀ t : ℕ, t < L - 2 → E (w' t) (w' (t + 1)) := by
          intro t ht
          dsimp only [w']
          split_ifs with h1 h2 h3
          · exact hedge t (by omega)
          · have htEq : t = i - 1 := by omega
            rw [htEq, hback]
            have hidx : i - 1 + 1 + 2 = i + 2 := by omega
            rw [hidx]
            exact hedge (i + 1) (by omega)
          · omega
          · have hidx : t + 1 + 2 = t + 2 + 1 := by omega
            rw [hidx]
            exact hedge (t + 2) (by omega)
        have hsub := ih (L - 2) (by omega) w' (hw'0 ▸ h0) (hw'L ▸ hL)
          (by rw [hw'0, hw'L]; exact hne) hw'edge
        omega
      · have hno_mid : ∀ i : ℕ, 0 < i → i < L → pos (w i) ≠ 0 := by
          intro i hi0 hiL hpi
          exact hmid ⟨i, hi0, hiL, hpi⟩
        have hno_bt : ∀ i : ℕ, 0 < i → i < L → w (i - 1) ≠ w (i + 1) := by
          intro i hi0 hiL hback
          exact hbt ⟨i, hi0, hiL, hback⟩
        have he01 : E (w 0) (w 1) := hedge 0 hLpos
        have hp1_ne : pos (w 1) ≠ 0 := by
          rcases hnohub (w 0) (w 1) he01 with h | h
          · exact absurd h0 h
          · exact h
        have h1ltL : 1 < L := by
          by_contra hle
          have hL1 : L = 1 := by omega
          rw [hL1] at hL
          exact hp1_ne hL
        rcases hinner (w 1) hp1_ne with ⟨hp1_le, a1, b1, h1adj, ha1, hb1⟩
        have hw0_in : w 0 = a1 ∨ w 0 = b1 := (h1adj (w 0)).mp (hsym _ _ he01)
        rcases hw0_in with h0a | h0b
        · have hp1 : pos (w 1) = 1 := by
            rw [← h0a, h0] at ha1
            omega
          have hup : ∀ i : ℕ, 1 ≤ i → i ≤ 2 * k → i < L ∧ pos (w i) = i := by
            intro i
            induction i using Nat.strong_induction_on with
            | _ i ih =>
              intro hi1 hi2k
              rcases Nat.eq_or_lt_of_le hi1 with rfl | hgt1
              · exact ⟨h1ltL, hp1⟩
              · obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
                rcases ih (m + 1) (by omega) (by omega) (by omega) with ⟨hmL, hpm⟩
                have hpm_ne : pos (w (m + 1)) ≠ 0 := by omega
                rcases hinner (w (m + 1)) hpm_ne with ⟨_, a, b, hadj, ha, hb⟩
                have hprev_mem : w m = a ∨ w m = b :=
                  (hadj (w m)).mp (hsym _ _ (hedge m (by omega)))
                have hnext_mem : w (m + 2) = a ∨ w (m + 2) = b :=
                  (hadj (w (m + 2))).mp (hedge (m + 1) hmL)
                have hpm_prev : pos (w m) = m := by
                  cases m with
                  | zero => exact h0
                  | succ r => exact (ih (r + 1) (by omega) (by omega) (by omega)).2
                have hb_val : pos b = m + 2 := by
                  rw [hpm] at hb
                  rw [hb, Nat.mod_eq_of_lt (by omega)]
                have hprev_eq_a : w m = a := by
                  rcases hprev_mem with h | h
                  · exact h
                  · exfalso
                    rw [h] at hpm_prev
                    omega
                have hnext_eq_b : w (m + 2) = b := by
                  rcases hnext_mem with h | h
                  · exfalso
                    exact hno_bt (m + 1) (by omega) hmL (hprev_eq_a.trans h.symm)
                  · exact h
                have hpm2 : pos (w (m + 2)) = m + 2 := by
                  rw [hnext_eq_b, hb_val]
                have hm2L : m + 2 < L := by
                  by_contra hge
                  have hEqL : m + 2 = L := by omega
                  rw [hEqL] at hpm2
                  omega
                exact ⟨hm2L, hpm2⟩
          have h2kL := (hup (2 * k) (by omega) (le_refl _)).1
          omega
        · have hp1 : pos (w 1) = 2 * k := by
            rw [← h0b, h0] at hb1
            have hdiv : (pos (w 1) + 1) % (2 * k + 1) = 0 := hb1.symm
            have hlt : pos (w 1) + 1 ≤ 2 * k + 1 := by omega
            rcases lt_or_eq_of_le hlt with hlt' | heq
            · rw [Nat.mod_eq_of_lt hlt'] at hdiv
              omega
            · omega
          have hdn : ∀ i : ℕ, 1 ≤ i → i ≤ 2 * k → i < L ∧ pos (w i) = 2 * k + 1 - i := by
            intro i
            induction i using Nat.strong_induction_on with
            | _ i ih =>
              intro hi1 hi2k
              rcases Nat.eq_or_lt_of_le hi1 with rfl | hgt1
              · exact ⟨h1ltL, by omega⟩
              · obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
                rcases ih (m + 1) (by omega) (by omega) (by omega) with ⟨hmL, hpm⟩
                have hpm_ne : pos (w (m + 1)) ≠ 0 := by omega
                rcases hinner (w (m + 1)) hpm_ne with ⟨_, a, b, hadj, ha, hb⟩
                have hprev_mem : w m = a ∨ w m = b :=
                  (hadj (w m)).mp (hsym _ _ (hedge m (by omega)))
                have hnext_mem : w (m + 2) = a ∨ w (m + 2) = b :=
                  (hadj (w (m + 2))).mp (hedge (m + 1) hmL)
                have hprev_ne_a : w m ≠ a := by
                  intro hEq
                  rw [← hEq] at ha
                  cases m with
                  | zero => omega
                  | succ r =>
                    have hpr := (ih (r + 1) (by omega) (by omega) (by omega)).2
                    omega
                have hprev_eq_b : w m = b := hprev_mem.resolve_left hprev_ne_a
                have hnext_eq_a : w (m + 2) = a := by
                  rcases hnext_mem with h | h
                  · exact h
                  · exfalso
                    exact hno_bt (m + 1) (by omega) hmL (hprev_eq_b.trans h.symm)
                have hpm2 : pos (w (m + 2)) = 2 * k + 1 - (m + 2) := by
                  rw [hnext_eq_a]
                  omega
                have hm2L : m + 2 < L := by
                  by_contra hge
                  have hEqL : m + 2 = L := by omega
                  rw [hEqL] at hpm2
                  omega
                exact ⟨hm2L, hpm2⟩
          have h2kL := (hdn (2 * k) (by omega) (le_refl _)).1
          omega

end PEqualNP.Outside.Meta249

open PEqualNP.Outside.Meta249 in
theorem PEqualNP.Outside.L_meta_249 :
    ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ (L : ℕ) (w : ℕ → Fin N), pos (w 0) = 0 → pos (w L) = 0 → w 0 ≠ w L → (∀ i : ℕ, i < L → E (w i) (w (i + 1))) → 2 * k + 1 ≤ L) ∧ ∀ v a b c : Fin N, E v a → E v b → E v c → a ≠ b → a ≠ c → b ≠ c → pos v = 0 := by
  intro N k E pos hk ⟨hsym, hnohub, hinner⟩
  constructor
  · exact walk_ge hk hsym hnohub hinner
  · intro v a b c hva hvb hvc hab hac hbc
    by_contra hpv
    rcases (hinner v hpv).2 with ⟨x, y, hxy, _, _⟩
    rcases (hxy a).mp hva with rfl | rfl <;>
      rcases (hxy b).mp hvb with rfl | rfl <;>
      rcases (hxy c).mp hvc with rfl | rfl <;>
      first | exact hab rfl | exact hac rfl | exact hbc rfl
