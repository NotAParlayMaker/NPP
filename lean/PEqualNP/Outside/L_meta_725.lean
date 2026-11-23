import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_725

lemma cover_restrict {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (S : Finset (Fin n))
    (hS : ∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S) :
    ∀ g h : Fin n, G.Adj g h → g ≠ v → h ≠ v → g ∈ S ∨ h ∈ S :=
  fun g h hgh _ _ => hS g h hgh

lemma insert_cover {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (U : Finset (Fin n))
    (hU : ∀ e f : Fin n, G.Adj e f → e ≠ v → f ≠ v → e ∈ U ∨ f ∈ U) :
    ∀ c d : Fin n, G.Adj c d → c ∈ insert v U ∨ d ∈ insert v U := by
  intro c d hcd
  by_cases hc : c = v
  · left
    rw [hc]
    exact Finset.mem_insert_self v U
  · by_cases hd : d = v
    · right
      rw [hd]
      exact Finset.mem_insert_self v U
    · rcases hU c d hcd hc hd with hm | hm
      · exact Or.inl (Finset.mem_insert_of_mem hm)
      · exact Or.inr (Finset.mem_insert_of_mem hm)

lemma erase_cover {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (X : Finset (Fin n))
    (hX : ∀ i j : Fin n, G.Adj i j → i ∈ X ∨ j ∈ X) :
    ∀ g h : Fin n, G.Adj g h → g ≠ v → h ≠ v → g ∈ X.erase v ∨ h ∈ X.erase v := by
  intro g h hgh hg hh
  rcases hX g h hgh with hx | hx
  · exact Or.inl (Finset.mem_erase.mpr ⟨hg, hx⟩)
  · exact Or.inr (Finset.mem_erase.mpr ⟨hh, hx⟩)

end PEqualNP.Outside.L_meta_725

theorem PEqualNP.Outside.L_meta_725 : ∀ (n t t1 : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n), (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S) ∧ S.card = t) → (∀ T : Finset (Fin n), (∀ c d : Fin n, G.Adj c d → c ∈ T ∨ d ∈ T) → t ≤ T.card) → (∃ U : Finset (Fin n), (∀ e f : Fin n, G.Adj e f → e ≠ v → f ≠ v → e ∈ U ∨ f ∈ U) ∧ U.card = t1) → (∀ W : Finset (Fin n), (∀ g h : Fin n, G.Adj g h → g ≠ v → h ≠ v → g ∈ W ∨ h ∈ W) → t1 ≤ W.card) → t ≤ t1 + 1 ∧ t1 ≤ t ∧ (t1 + 1 = t ↔ ∃ X : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ X ∨ j ∈ X) ∧ X.card = t ∧ v ∈ X) := by
  intro n t t1 G v hS hT hU hW
  obtain ⟨S, hSc, hScard⟩ := hS
  obtain ⟨U, hUc, hUcard⟩ := hU
  have hcov := PEqualNP.Outside.L_meta_725.insert_cover G v U hUc
  have hins := hT (insert v U) hcov
  have hle := Finset.card_insert_le v U
  have h1 : t1 ≤ t := by
    have hs := hW S (PEqualNP.Outside.L_meta_725.cover_restrict G v S hSc)
    omega
  have h2 : t ≤ t1 + 1 := by
    omega
  refine ⟨h2, h1, ?_⟩
  constructor
  · intro heq
    refine ⟨insert v U, hcov, ?_, Finset.mem_insert_self v U⟩
    omega
  · rintro ⟨X, hXc, hXcard, hvX⟩
    have he := hW (X.erase v) (PEqualNP.Outside.L_meta_725.erase_cover G v X hXc)
    have hcard := Finset.card_erase_of_mem hvX
    have hpos : 0 < X.card := Finset.card_pos.mpr ⟨v, hvX⟩
    omega
