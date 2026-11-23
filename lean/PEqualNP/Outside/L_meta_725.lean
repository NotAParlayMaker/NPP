import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_725 :
    ∀ (n t t1 : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n), (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S) ∧ S.card = t) → (∀ T : Finset (Fin n), (∀ c d : Fin n, G.Adj c d → c ∈ T ∨ d ∈ T) → t ≤ T.card) → (∃ U : Finset (Fin n), (∀ e f : Fin n, G.Adj e f → e ≠ v → f ≠ v → e ∈ U ∨ f ∈ U) ∧ U.card = t1) → (∀ W : Finset (Fin n), (∀ g h : Fin n, G.Adj g h → g ≠ v → h ≠ v → g ∈ W ∨ h ∈ W) → t1 ≤ W.card) → t ≤ t1 + 1 ∧ t1 ≤ t ∧ (t1 + 1 = t ↔ ∃ X : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ X ∨ j ∈ X) ∧ X.card = t ∧ v ∈ X) := by
  intro n t t1 G v ⟨S, hS, hSc⟩ hmin ⟨U, hU, hUc⟩ hmin1
  have hvU : v ∉ U := by
    intro hvU
    have hcov : ∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ U.erase v ∨ b ∈ U.erase v := by
      intro a b hab hav hbv
      rcases hU a b hab hav hbv with ha | hb
      · exact Or.inl (Finset.mem_erase.mpr ⟨hav, ha⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hbv, hb⟩)
    have hle := hmin1 (U.erase v) hcov
    have hcard : (U.erase v).card + 1 = U.card := Finset.card_erase_add_one hvU
    omega
  have hins : ∀ a b : Fin n, G.Adj a b → a ∈ insert v U ∨ b ∈ insert v U := by
    intro a b hab
    by_cases hav : a = v
    · subst hav; exact Or.inl (Finset.mem_insert_self _ _)
    · by_cases hbv : b = v
      · subst hbv; exact Or.inr (Finset.mem_insert_self _ _)
      · rcases hU a b hab hav hbv with ha | hb
        · exact Or.inl (Finset.mem_insert_of_mem ha)
        · exact Or.inr (Finset.mem_insert_of_mem hb)
  have hinsc : (insert v U).card = t1 + 1 := by
    rw [Finset.card_insert_of_notMem hvU, hUc]
  have h1 : t ≤ t1 + 1 := by
    have hle := hmin (insert v U) hins
    omega
  have h2 : t1 ≤ t := by
    have hle := hmin1 S (fun g h hgh _ _ => hS g h hgh)
    omega
  refine ⟨h1, h2, ?_, ?_⟩
  · intro heq
    exact ⟨insert v U, hins, by omega, Finset.mem_insert_self _ _⟩
  · rintro ⟨X, hX, hXc, hvX⟩
    have hcov : ∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ X.erase v ∨ b ∈ X.erase v := by
      intro a b hab hav hbv
      rcases hX a b hab with ha | hb
      · exact Or.inl (Finset.mem_erase.mpr ⟨hav, ha⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hbv, hb⟩)
    have hle := hmin1 (X.erase v) hcov
    have hcard : (X.erase v).card + 1 = X.card := Finset.card_erase_add_one hvX
    omega
