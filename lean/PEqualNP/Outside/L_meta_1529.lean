import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1529

/-- The statement with "no 4-cycle" in the plain form: two different vertices have no two
different common neighbours. -/
theorem core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False)
    (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) :
    (∀ w ∈ W, w ∈ P → w ∉ Q ∧ ∀ q ∈ Q, G.Adj w q) ∧
    (∀ w ∈ W, w ∈ Q → w ∉ P ∧ ∀ p ∈ P, G.Adj w p) ∧
    (∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w) ∧ (∀ s ∈ P ∩ Q, s ∉ W) ∧
    (2 ≤ (P ∩ Q).card → W.card ≤ 1) := by
  have h3 : ∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w := by
    intro s hs w hw
    obtain ⟨hsP, hsQ⟩ := Finset.mem_inter.1 hs
    rcases (hW w).1 hw s hsP s hsQ with h | h | h
    · exact absurd h (G.loopless.irrefl s)
    · exact h
    · exact h
  refine ⟨?_, ?_, h3, ?_, ?_⟩
  · intro w hw hwP
    have key : ∀ q ∈ Q, G.Adj w q := by
      intro q hq
      rcases (hW w).1 hw w hwP q hq with h | h | h
      · exact h
      · exact absurd h (G.loopless.irrefl w)
      · exact h.symm
    exact ⟨fun hwQ => G.loopless.irrefl w (key w hwQ), key⟩
  · intro w hw hwQ
    have key : ∀ p ∈ P, G.Adj w p := by
      intro p hp
      rcases (hW w).1 hw p hp w hwQ with h | h | h
      · exact h.symm
      · exact h.symm
      · exact absurd h (G.loopless.irrefl w)
    exact ⟨fun hwP => G.loopless.irrefl w (key w hwP), key⟩
  · intro s hs hsW
    exact G.loopless.irrefl s (h3 s hs s hsW)
  · intro h2
    obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.1 h2
    apply Finset.card_le_one.2
    intro w hw w' hw'
    by_contra hne
    exact hno s t w w' hst hne (h3 s hs w hw) (h3 t ht w hw) (h3 s hs w' hw') (h3 t ht w' hw')

end PEqualNP.Outside.L_meta_1529

theorem PEqualNP.Outside.L_meta_1529 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (∀ w ∈ W, w ∈ P → w ∉ Q ∧ ∀ q ∈ Q, G.Adj w q) ∧
    (∀ w ∈ W, w ∈ Q → w ∉ P ∧ ∀ p ∈ P, G.Adj w p) ∧
    (∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w) ∧ (∀ s ∈ P ∩ Q, s ∉ W) ∧
    (2 ≤ (P ∩ Q).card → W.card ≤ 1) := by
  intro n G _ hnf P Q W hW
  have hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False := by
    intro s t w w' hst hww h1 h2 h3 h4
    exact hww (Finset.card_le_one.1 (hnf s t hst) w (by simp [h1, h2]) w' (by simp [h3, h4]))
  exact PEqualNP.Outside.L_meta_1529.core n G hno P Q W hW
