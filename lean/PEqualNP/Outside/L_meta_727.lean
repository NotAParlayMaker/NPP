import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_727 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n), (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S) ∧ S.card = t) → (∀ T : Finset (Fin n), (∀ c d : Fin n, G.Adj c d → c ∈ T ∨ d ∈ T) → t ≤ T.card) → t < (Finset.univ.filter (fun u : Fin n => G.Adj v u)).card → ∀ U : Finset (Fin n), (∀ e f : Fin n, G.Adj e f → e ∈ U ∨ f ∈ U) → U.card = t → v ∈ U := by
  intro n t G _ v _ _ degree U cover size
  by_contra absent
  have neighbors : Finset.univ.filter (fun u : Fin n => G.Adj v u) ⊆ U := by
    intro u hu
    exact (cover v u (Finset.mem_filter.mp hu).2).resolve_left absent
  exact (Nat.not_le_of_lt degree) (size ▸ Finset.card_le_card neighbors)
