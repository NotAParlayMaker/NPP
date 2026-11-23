import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_727

end PEqualNP.Outside.L_meta_727

theorem PEqualNP.Outside.L_meta_727 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n), (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S) ∧ S.card = t) → (∀ T : Finset (Fin n), (∀ c d : Fin n, G.Adj c d → c ∈ T ∨ d ∈ T) → t ≤ T.card) → t < (Finset.univ.filter (fun u : Fin n => G.Adj v u)).card → ∀ U : Finset (Fin n), (∀ e f : Fin n, G.Adj e f → e ∈ U ∨ f ∈ U) → U.card = t → v ∈ U := by
  intro n t G _ v _ _ hdeg U hcov hcard
  by_contra hv
  have hsub : Finset.univ.filter (fun u : Fin n => G.Adj v u) ⊆ U := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rcases hcov v u hu.2 with h | h
    · exact (hv h).elim
    · exact h
  have hle : (Finset.univ.filter (fun u : Fin n => G.Adj v u)).card ≤ U.card :=
    Finset.card_le_card hsub
  omega
