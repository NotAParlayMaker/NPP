import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

theorem PEqualNP.Outside.L_meta_754 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 5 ≤ s := by
  intro s
  constructor
  · intro hc
    let G : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun i j : Fin 5 =>
      (i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) ∨ (i = 1 ∧ j = 4)
    have hcard : G.edgeFinset.card = 4 := by
      decide
    have hconn : G.Connected := by
      refine ⟨fun u v => ?_⟩
      have h0 : ∀ w : Fin 5, G.Reachable w 0 := by
        intro w
        fin_cases w
        · exact SimpleGraph.Reachable.refl _
        · exact SimpleGraph.Adj.reachable (by decide)
        · exact SimpleGraph.Adj.reachable (by decide)
        · exact SimpleGraph.Adj.reachable (by decide)
        · exact (SimpleGraph.Adj.reachable (by decide : G.Adj 4 1)).trans
            (SimpleGraph.Adj.reachable (by decide : G.Adj 1 0))
      exact (h0 u).trans (h0 v).symm
    have hacyc : G.IsAcyclic := by
      have ht : G.IsTree := by
        rw [SimpleGraph.isTree_iff_connected_and_card]
        refine ⟨hconn, ?_⟩
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Set.toFinset_card]
        change G.edgeFinset.card + 1 = Fintype.card (Fin 5)
        rw [hcard]
        simp
      exact ht.isAcyclic
    have hcov : ∀ T : Finset (Fin 5), (∀ i j : Fin 5, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
      intro T hT
      have h02 : (0 : Fin 5) ∈ T ∨ (2 : Fin 5) ∈ T := hT 0 2 (by decide)
      have h14 : (1 : Fin 5) ∈ T ∨ (4 : Fin 5) ∈ T := hT 1 4 (by decide)
      rcases h02 with h0 | h2 <;> rcases h14 with h1 | h4
      · exact le_trans (by decide : 2 ≤ ({0, 1} : Finset (Fin 5)).card)
          (Finset.card_le_card (Finset.insert_subset h0 (Finset.singleton_subset_iff.2 h1)))
      · exact le_trans (by decide : 2 ≤ ({0, 4} : Finset (Fin 5)).card)
          (Finset.card_le_card (Finset.insert_subset h0 (Finset.singleton_subset_iff.2 h4)))
      · exact le_trans (by decide : 2 ≤ ({2, 1} : Finset (Fin 5)).card)
          (Finset.card_le_card (Finset.insert_subset h2 (Finset.singleton_subset_iff.2 h1)))
      · exact le_trans (by decide : 2 ≤ ({2, 4} : Finset (Fin 5)).card)
          (Finset.card_le_card (Finset.insert_subset h2 (Finset.singleton_subset_iff.2 h4)))
    have hfn :
        (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) =
        (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G.Adj i j ∧ x i = true ∧ x j = true)) := by
      funext x
      have h : ∀ a0 a1 a2 a3 a4 : Bool,
          ((a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4)) =
          decide (∃ i j : Fin 5, G.Adj i j ∧ ![a0, a1, a2, a3, a4] i = true ∧ ![a0, a1, a2, a3, a4] j = true) := by
        decide
      have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
        funext i
        fin_cases i <;> rfl
      conv_rhs => rw [hx]
      exact h (x 0) (x 1) (x 2) (x 3) (x 4)
    rw [hfn] at hc
    have hlb := PEqualNP.MetaComplexity.L104 5 2 s G hacyc ⟨0, 1, by decide⟩ hcov hc
    rw [hcard] at hlb
    omega
  · intro hs
    let C : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩
    refine ⟨C, ?_, hs, ?_⟩
    · simp [C, PEqualNP.MetaComplexity.FanInTwo]
    · intro x
      have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := rfl
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, C, hx]
      generalize x 0 = a0
      generalize x 1 = a1
      generalize x 2 = a2
      generalize x 3 = a3
      generalize x 4 = a4
      cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> rfl
