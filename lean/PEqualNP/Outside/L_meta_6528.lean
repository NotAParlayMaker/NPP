import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6528

lemma quad : ∀ a b c d : Fin 13, a < b → b < c → c < d →
    (Finset.univ.filter (fun y : Fin 13 =>
      (a.val + y.val) % 13 ∉ [0, 1, 3, 9] ∧ (b.val + y.val) % 13 ∉ [0, 1, 3, 9] ∧
      (c.val + y.val) % 13 ∉ [0, 1, 3, 9] ∧ (d.val + y.val) % 13 ∉ [0, 1, 3, 9])).card ≤ 3 := by
  decide +kernel

end PEqualNP.Outside.L_meta_6528

theorem PEqualNP.Outside.L_meta_6528 : ∀ (x1 : Finset (Fin (13 : ℕ))),   (4 : ℕ) ≤ x1.card →     have x3 : Finset (Fin (13 : ℕ)) := {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x1, (↑x4 + ↑x3) % (13 : ℕ) ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]};     x3.card ≤ (3 : ℕ) := by
  intro A h4
  have hmem : ∀ i : Fin 4, A.orderEmbOfCardLe h4 i ∈ A := fun i => Finset.orderEmbOfCardLe_mem A h4 i
  have hmono := (A.orderEmbOfCardLe h4).strictMono
  have hq := PEqualNP.Outside.L_meta_6528.quad (A.orderEmbOfCardLe h4 0) (A.orderEmbOfCardLe h4 1)
    (A.orderEmbOfCardLe h4 2) (A.orderEmbOfCardLe h4 3)
    (hmono (by decide)) (hmono (by decide)) (hmono (by decide))
  refine le_trans (Finset.card_le_card ?_) hq
  intro y hy
  rw [Finset.mem_filter] at hy ⊢
  exact ⟨Finset.mem_univ _, hy.2 _ (hmem 0), hy.2 _ (hmem 1), hy.2 _ (hmem 2), hy.2 _ (hmem 3)⟩
