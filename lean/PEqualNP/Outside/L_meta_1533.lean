import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1533

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

theorem core (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (U : Finset (Sym2 (Fin n))) (hU : ∀ e ∈ U, e ∈ G.edgeSet) (x : Fin n) (Y : Finset (Fin n))
    (hY : ∀ y ∈ Y, s(x, y) ∈ U) (B : Finset (Fin n))
    (hB : 2 ≤ B.card ∧ ∃ c : Fin n, (∀ y ∈ B, G.Adj c y) ∧ ∀ y ∈ B, s(c, y) ∉ U) :
    (B ∩ Y).card ≤ 1 ∧ ((∀ b ∈ B, G.Adj x b) → B ∩ Y = ∅) := by
  obtain ⟨hB2, c, hcB, hcU⟩ := hB
  have key : ∀ y ∈ B ∩ Y, G.Adj x y ∧ G.Adj c y ∧ x ≠ c := by
    intro y hy
    rw [Finset.mem_inter] at hy
    refine ⟨(SimpleGraph.mem_edgeSet G).1 (hU _ (hY y hy.2)), hcB y hy.1, ?_⟩
    intro hxc
    apply hcU y hy.1
    rw [← hxc]
    exact hY y hy.2
  refine ⟨?_, ?_⟩
  · rw [Finset.card_le_one]
    intro y1 h1 y2 h2
    obtain ⟨hx1, hc1, hne⟩ := key y1 h1
    obtain ⟨hx2, hc2, _⟩ := key y2 h2
    rcases h4 x y1 c y2 hx1 hc1.symm hc2 hx2.symm with h | h
    · exact absurd h hne
    · exact h
  · intro hxB
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
    obtain ⟨hxy, hcy, hxc⟩ := key y hy
    obtain ⟨b, hb, hby⟩ := Finset.exists_mem_ne (Nat.lt_of_lt_of_le Nat.one_lt_two hB2) y
    rcases h4 x y c b hxy hcy.symm (hcB b hb) (hxB b hb).symm with h | h
    · exact hxc h
    · exact hby h.symm

end PEqualNP.Outside.L_meta_1533

theorem PEqualNP.Outside.L_meta_1533 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G →
    ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) →
    ∀ (B : Finset (Fin n)), (2 ≤ B.card ∧ ∃ c : Fin n, (∀ y ∈ B, G.Adj c y) ∧ ∀ y ∈ B, s(c, y) ∉ U) →
    (B ∩ Y).card ≤ 1 ∧ ((∀ b ∈ B, G.Adj x b) → B ∩ Y = ∅) := by
  intro n G _ h4 U hU x Y hY B hB
  exact PEqualNP.Outside.L_meta_1533.core n G
    (PEqualNP.Outside.L_meta_1533.h4_of_card n G h4) U hU x Y hY B hB
