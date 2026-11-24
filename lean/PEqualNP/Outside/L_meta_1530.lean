import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1530

theorem cn_of_h4 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) :
    ∀ u v : Fin n, u ≠ v → ∀ x y : Fin n, G.Adj u x → G.Adj v x → G.Adj u y → G.Adj v y → x = y := by
  intro u v huv x y hux hvx huy hvy
  rcases h4 u x v y hux hvx.symm hvy huy.symm with h | h
  · exact absurd h huv
  · exact h

theorem h4_of_cn (n : ℕ) (G : SimpleGraph (Fin n))
    (hcn : ∀ u v : Fin n, u ≠ v → ∀ x y : Fin n,
      G.Adj u x → G.Adj v x → G.Adj u y → G.Adj v y → x = y) :
    ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d := by
  intro a b c d hab hbc hcd hda
  by_cases hac : a = c
  · exact Or.inl hac
  · exact Or.inr (hcn a c hac b d hab hbc.symm hda.symm hcd)

theorem h4_of_card (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : ∀ u v : Fin n, u ≠ v →
      ((Finset.univ.filter fun x => G.Adj u x ∧ G.Adj v x)).card ≤ 1) :
    ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d := by
  apply h4_of_cn
  intro u v huv x y hux hvx huy hvy
  exact Finset.card_le_one.1 (hc u v huv) x (by simp [hux, hvx]) y (by simp [huy, hvy])

theorem core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) :
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s →
      ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) := by
  have hPQ : ∀ w ∈ W, w ∈ P → ∀ q ∈ Q, G.Adj w q := by
    intro w hw hwP q hq
    rcases (hW w).1 hw w hwP q hq with h | h | h
    · exact h
    · exact absurd rfl (G.ne_of_adj h)
    · exact h.symm
  have hQP : ∀ w ∈ W, w ∈ Q → ∀ p ∈ P, G.Adj w p := by
    intro w hw hwQ p hp
    rcases (hW w).1 hw p hp w hwQ with h | h | h
    · exact h.symm
    · exact h.symm
    · exact absurd rfl (G.ne_of_adj h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hQ
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_inter] at hx hy
    obtain ⟨q1, hq1, q2, hq2, hne⟩ := Finset.one_lt_card.1 hQ
    rcases h4 x q1 y q2 (hPQ x hx.1 hx.2 q1 hq1) (hPQ y hy.1 hy.2 q1 hq1).symm
      (hPQ y hy.1 hy.2 q2 hq2) (hPQ x hx.1 hx.2 q2 hq2).symm with h | h
    · exact h
    · exact absurd h hne
  · intro hP
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_inter] at hx hy
    obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.1 hP
    rcases h4 x p1 y p2 (hQP x hx.1 hx.2 p1 hp1) (hQP y hy.1 hy.2 p1 hp1).symm
      (hQP y hy.1 hy.2 p2 hp2) (hQP x hx.1 hx.2 p2 hp2).symm with h | h
    · exact h
    · exact absurd h hne
  · intro a b _ hP hQ haW
    have hnot : ¬ (a ∈ P ∧ a ∈ Q) := fun h => G.ne_of_adj (hPQ a haW h.1 a h.2) rfl
    refine ⟨fun haP => ?_, fun haQ => ?_, fun haP haQ => ?_⟩
    · rcases hQ with h | h
      · exact absurd ⟨haP, h⟩ hnot
      · exact h
    · rcases hP with h | h
      · exact absurd ⟨h, haQ⟩ hnot
      · exact h
    · exact Finset.mem_inter.2 ⟨hP.resolve_left haP, hQ.resolve_left haQ⟩
  · intro s hs u hus
    have hsPQ : s ∈ P ∩ Q := by
      rw [hs]
      exact Finset.mem_singleton_self s
    have hsP : s ∈ P ∧ s ∈ Q := Finset.mem_inter.1 hsPQ
    have hsW : ∀ w ∈ W, G.Adj s w := by
      intro w hw
      rcases (hW w).1 hw s hsP.1 s hsP.2 with h | h | h
      · exact absurd rfl (G.ne_of_adj h)
      · exact h
      · exact h
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_inter, Finset.mem_filter] at hx hy
    rcases h4 u x s y hx.1.2 (hsW x hx.2).symm (hsW y hy.2) hy.1.2.symm with h | h
    · exact absurd h hus
    · exact h

end PEqualNP.Outside.L_meta_1530

theorem PEqualNP.Outside.L_meta_1530 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s → ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) := by
  intro n G _ h4 P Q W hW
  exact PEqualNP.Outside.L_meta_1530.core n G (PEqualNP.Outside.L_meta_1530.h4_of_card n G (fun u v huv => h4 u v huv)) P Q W hW
