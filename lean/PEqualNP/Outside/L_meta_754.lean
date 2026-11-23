import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_754_aux

/-- The fork: centre 0 with neighbours 1, 2, 3, and the extra edge 1 - 4. -/
def E : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4)]

def G : SimpleGraph (Fin 5) where
  Adj a b := a ≠ b ∧ (((a : ℕ), (b : ℕ)) ∈ E ∨ ((b : ℕ), (a : ℕ)) ∈ E)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ (((a : ℕ), (b : ℕ)) ∈ E ∨ ((b : ℕ), (a : ℕ)) ∈ E)))

theorem edges : G.edgeFinset.card = 4 := by decide +kernel

theorem reach0 : ∀ v : Fin 5, G.Reachable 0 v := by
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact (SimpleGraph.Adj.reachable (show G.Adj 0 1 by decide)).trans
      (SimpleGraph.Adj.reachable (show G.Adj 1 4 by decide))

theorem acyclic : G.IsAcyclic := by
  have h : G.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨(SimpleGraph.connected_iff_exists_forall_reachable G).2 ⟨0, reach0⟩, ?_⟩
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, edges]
    simp
  exact h.isAcyclic

theorem cover : ∀ T : Finset (Fin 5), (∀ i j : Fin 5, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide +kernel

theorem fn_eq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) =
    (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  revert x
  decide +kernel

end PEqualNP.Outside.L_meta_754_aux

open PEqualNP.Outside.L_meta_754_aux in
theorem PEqualNP.Outside.L_meta_754 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 5 ≤ s := by
  intro s
  constructor
  · -- Lower bound: the fork is a forest with 4 edges and cover number 2 (L-meta-104).
    intro hc
    rw [fn_eq] at hc
    have h := PEqualNP.MetaComplexity.L104 5 2 s G acyclic ⟨0, 1, by decide⟩ cover hc
    rw [edges] at h
    omega
  · -- Upper bound: x0 AND (x2 OR x3 OR x1), OR (x1 AND x4): five gates.
    intro hs
    let C : Circuit :=
      ⟨[⟨.or, [2, 3]⟩, ⟨.or, [5, 1]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩
    refine ⟨C, ?_, hs, ?_⟩
    · simp [C, FanInTwo]
    · dsimp only [C]
      decide +kernel
