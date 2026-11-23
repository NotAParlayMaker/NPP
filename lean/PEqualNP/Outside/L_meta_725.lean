import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

theorem L_meta_725 :
    ∀ (n t t1 : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n),
      (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S) ∧ S.card = t) →
      (∀ T : Finset (Fin n), (∀ c d : Fin n, G.Adj c d → c ∈ T ∨ d ∈ T) → t ≤ T.card) →
      (∃ U : Finset (Fin n), (∀ e f : Fin n, G.Adj e f → e ≠ v → f ≠ v → e ∈ U ∨ f ∈ U) ∧ U.card = t1) →
      (∀ W : Finset (Fin n), (∀ g h : Fin n, G.Adj g h → g ≠ v → h ≠ v → g ∈ W ∨ h ∈ W) → t1 ≤ W.card) →
      t ≤ t1 + 1 ∧ t1 ≤ t ∧
        (t1 + 1 = t ↔ ∃ X : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ X ∨ j ∈ X) ∧ X.card = t ∧ v ∈ X) := by
  intro n t t1 G v hS ht hU ht1
  rcases hS with ⟨S, hS_cov, hS_card⟩
  rcases hU with ⟨U, hU_cov, hU_card⟩

  have ht1t : t1 ≤ t := by
    have h := ht1 S (by
      intro e f hadj hev hfv
      exact hS_cov e f hadj)
    simpa [hS_card] using h

  let V : Finset (Fin n) := insert v U

  have hV_cov : ∀ a b : Fin n, G.Adj a b → a ∈ V ∨ b ∈ V := by
    intro a b hab
    by_cases ha : a = v
    · left
      simp [V, ha]
    · by_cases hb : b = v
      · right
        simp [V, hb]
      · rcases hU_cov a b hab ha hb with h | h
        · left
          simp [V, h]
        · right
          simp [V, h]

  have hV_card_le : V.card ≤ t1 + 1 := by
    have hle : V.card ≤ U.card + 1 := by
      dsimp [V]
      by_cases h : v ∈ U
      · simp [h]
      · simp [h]
    calc
      V.card ≤ U.card + 1 := hle
      _ = t1 + 1 := by rw [hU_card]

  have htV : t ≤ V.card := ht V hV_cov
  have htt1 : t ≤ t1 + 1 := le_trans htV hV_card_le

  refine ⟨htt1, ht1t, ?_⟩
  constructor
  · intro hEq
    refine ⟨V, hV_cov, ?_, ?_⟩
    · omega
    · dsimp [V]
      simp
  · rintro ⟨X, hX_cov, hX_card, hvX⟩
    have hY_cov : ∀ e f : Fin n, G.Adj e f → e ≠ v → f ≠ v → e ∈ X.erase v ∨ f ∈ X.erase v := by
      intro e f hadj hev hfv
      rcases hX_cov e f hadj with h | h
      · left
        exact Finset.mem_erase.mpr ⟨hev, h⟩
      · right
        exact Finset.mem_erase.mpr ⟨hfv, h⟩
    have ht1Y : t1 ≤ (X.erase v).card := ht1 (X.erase v) hY_cov
    have hY_card : (X.erase v).card = t - 1 := by
      rw [Finset.card_erase_of_mem hvX, hX_card]
    have htpos : 0 < t := by
      rw [← hX_card]
      exact Finset.card_pos.mpr ⟨v, hvX⟩
    omega

end PEqualNP.Outside
