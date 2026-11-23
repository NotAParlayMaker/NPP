import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_725 : ∀ (n t t1 : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n), (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S) ∧ S.card = t) → (∀ T : Finset (Fin n), (∀ c d : Fin n, G.Adj c d → c ∈ T ∨ d ∈ T) → t ≤ T.card) → (∃ U : Finset (Fin n), (∀ e f : Fin n, G.Adj e f → e ≠ v → f ≠ v → e ∈ U ∨ f ∈ U) ∧ U.card = t1) → (∀ W : Finset (Fin n), (∀ g h : Fin n, G.Adj g h → g ≠ v → h ≠ v → g ∈ W ∨ h ∈ W) → t1 ≤ W.card) → t ≤ t1 + 1 ∧ t1 ≤ t ∧ (t1 + 1 = t ↔ ∃ X : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ X ∨ j ∈ X) ∧ X.card = t ∧ v ∈ X) := by
  intro n t t1 G v ⟨S, hS, hSc⟩ hT ⟨U, hU, hUc⟩ hW
  -- Adding v to a set that meets every edge avoiding v gives a cover of G.
  have hcov : ∀ a b : Fin n, G.Adj a b → a ∈ insert v U ∨ b ∈ insert v U := by
    intro a b hab
    by_cases ha : a = v
    · exact Or.inl (Finset.mem_insert.2 (Or.inl ha))
    by_cases hb : b = v
    · exact Or.inr (Finset.mem_insert.2 (Or.inl hb))
    rcases hU a b hab ha hb with h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Finset.mem_insert_of_mem h)
  have hins : (insert v U).card ≤ t1 + 1 := hUc ▸ Finset.card_insert_le v U
  have h1 : t ≤ t1 + 1 := (hT _ hcov).trans hins
  have h2 : t1 ≤ t := hSc ▸ hW S (fun g h hgh _ _ => hS g h hgh)
  refine ⟨h1, h2, ⟨fun h => ?_, fun ⟨X, hX, hXc, hv⟩ => ?_⟩⟩
  · refine ⟨insert v U, hcov, ?_, Finset.mem_insert_self v U⟩
    have := hT _ hcov
    omega
  · -- Removing v from a cover that holds v leaves a set meeting every edge avoiding v.
    have hE : ∀ g h : Fin n, G.Adj g h → g ≠ v → h ≠ v → g ∈ X.erase v ∨ h ∈ X.erase v := by
      intro g h hgh hg hh
      rcases hX g h hgh with hx | hx
      · exact Or.inl (Finset.mem_erase.2 ⟨hg, hx⟩)
      · exact Or.inr (Finset.mem_erase.2 ⟨hh, hx⟩)
    have hle := hW _ hE
    rw [Finset.card_erase_of_mem hv, hXc] at hle
    have hpos : 0 < X.card := Finset.card_pos.2 ⟨v, hv⟩
    omega
