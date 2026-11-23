import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_725 : ∀ (n t t1 : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n), (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S) ∧ S.card = t) → (∀ T : Finset (Fin n), (∀ c d : Fin n, G.Adj c d → c ∈ T ∨ d ∈ T) → t ≤ T.card) → (∃ U : Finset (Fin n), (∀ e f : Fin n, G.Adj e f → e ≠ v → f ≠ v → e ∈ U ∨ f ∈ U) ∧ U.card = t1) → (∀ W : Finset (Fin n), (∀ g h : Fin n, G.Adj g h → g ≠ v → h ≠ v → g ∈ W ∨ h ∈ W) → t1 ≤ W.card) → t ≤ t1 + 1 ∧ t1 ≤ t ∧ (t1 + 1 = t ↔ ∃ X : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ X ∨ j ∈ X) ∧ X.card = t ∧ v ∈ X) := by
  intro n t t1 G v hS hmin hU hmin1
  obtain ⟨S, hScov, hScard⟩ := hS
  obtain ⟨U, hUcov, hUcard⟩ := hU
  have h1 : t1 ≤ t := by
    have h0 := hmin1 S (fun g h hgh _ _ => hScov g h hgh)
    omega
  have hins : ∀ a b : Fin n, G.Adj a b → a ∈ insert v U ∨ b ∈ insert v U := by
    intro a b hab
    by_cases ha : a = v
    · left
      simp [ha]
    · by_cases hb : b = v
      · right
        simp [hb]
      · rcases hUcov a b hab ha hb with h | h
        · left
          exact Finset.mem_insert_of_mem h
        · right
          exact Finset.mem_insert_of_mem h
  have hcard : (insert v U).card ≤ t1 + 1 := by
    have h0 := Finset.card_insert_le v U
    omega
  have hge := hmin _ hins
  have h2 : t ≤ t1 + 1 := le_trans hge hcard
  refine ⟨h2, h1, ⟨fun heq => ?_, fun hX => ?_⟩⟩
  · refine ⟨insert v U, hins, ?_, Finset.mem_insert_self v U⟩
    omega
  · obtain ⟨X, hXcov, hXcard, hvX⟩ := hX
    have hcov : ∀ g h : Fin n, G.Adj g h → g ≠ v → h ≠ v → g ∈ X.erase v ∨ h ∈ X.erase v := by
      intro g h hgh hg hh
      rcases hXcov g h hgh with h' | h'
      · left
        exact Finset.mem_erase.2 ⟨hg, h'⟩
      · right
        exact Finset.mem_erase.2 ⟨hh, h'⟩
    have h0 := hmin1 _ hcov
    have hc := Finset.card_erase_of_mem hvX
    have hpos : 0 < X.card := Finset.card_pos.2 ⟨v, hvX⟩
    omega
