import Mathlib
import PEqualNP.Defs

-- A cover missing v must contain every neighbour of v, so it has at least deg v > t vertices.
theorem PEqualNP.Outside.L_meta_727 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n), (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S) ∧ S.card = t) → (∀ T : Finset (Fin n), (∀ c d : Fin n, G.Adj c d → c ∈ T ∨ d ∈ T) → t ≤ T.card) → t < (Finset.univ.filter (fun u : Fin n => G.Adj v u)).card → ∀ U : Finset (Fin n), (∀ e f : Fin n, G.Adj e f → e ∈ U ∨ f ∈ U) → U.card = t → v ∈ U := by
  intro n t G _ v _ _ hdeg U hU hcard
  by_contra hv
  have hsub : (Finset.univ.filter (fun u : Fin n => G.Adj v u)) ⊆ U := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rcases hU v u hu.2 with h | h
    · exact absurd h hv
    · exact h
  have hle := Finset.card_le_card hsub
  omega
