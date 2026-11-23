import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_755

private abbrev edgesFrom (i j : Fin 6) : Prop :=
  (i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) ∨ (i = 4 ∧ j = 5)

private abbrev G : SimpleGraph (Fin 6) where
  Adj i j := edgesFrom i j ∨ edgesFrom j i
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

private def circ : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩], output := 10 }

private theorem tuple (x : Fin 6 → Bool) :
    (![x 0, x 1, x 2, x 3, x 4, x 5] : Fin 6 → Bool) = x := by
  funext i
  fin_cases i <;> rfl

private theorem evalKey : ∀ a0 a1 a2 a3 a4 a5 : Bool,
    circ.eval [a0, a1, a2, a3, a4, a5] =
      ((a0 && a1) || (a0 && a2) || (a0 && a3) || (a4 && a5)) := by
  decide +kernel

private theorem evalOk (x : Fin 6 → Bool) :
    circ.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) := by
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hx]
  exact evalKey _ _ _ _ _ _

private theorem fanin : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
private theorem adjKey : ∀ a0 a1 a2 a3 a4 a5 : Bool,
    ((∃ i j : Fin 6, G.Adj i j ∧ (![a0, a1, a2, a3, a4, a5] : Fin 6 → Bool) i = true ∧
      (![a0, a1, a2, a3, a4, a5] : Fin 6 → Bool) j = true) ↔
      ((a0 && a1) || (a0 && a2) || (a0 && a3) || (a4 && a5)) = true) := by
  decide +kernel

private theorem funEq : (fun x : Fin 6 → Bool =>
      decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) =
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) := by
  funext x
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  have h := adjKey (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  rw [tuple] at h
  exact h

private theorem unique_nbr :
    ∀ v u w : Fin 6, v ≠ 0 → G.Adj v u → G.Adj v w → u = w := by decide

private theorem leafBridge {v w : Fin 6} (hv : v ≠ 0) (hvw : G.Adj v w) :
    G.IsBridge s(v, w) := by
  rw [SimpleGraph.isBridge_iff]
  rintro ⟨p⟩
  cases p with
  | nil => exact hvw.ne rfl
  | cons h q =>
    rw [SimpleGraph.deleteEdges_adj] at h
    have hu := unique_nbr _ _ _ hv h.1 hvw
    subst hu
    exact h.2 rfl

private theorem acyclic : G.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  by_cases hv : v = 0
  · rw [Sym2.eq_swap]
    exact leafBridge (fun hw => hvw.ne (hv.trans hw.symm)) hvw.symm
  · exact leafBridge hv hvw

private theorem cover2 : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) →
    2 ≤ T.card := by
  intro T hT
  have h1 := hT 0 1 (by decide)
  have h2 := hT 4 5 (by decide)
  have hsub : ∃ a b : Fin 6, a ∈ T ∧ b ∈ T ∧ ({a, b} : Finset (Fin 6)).card = 2 := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> exact ⟨_, _, h1, h2, by decide⟩
  obtain ⟨a, b, ha, hb, hcard⟩ := hsub
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> assumption

private theorem edges4 : 4 ≤ G.edgeFinset.card := by
  have hsub : ({s(0, 1), s(0, 2), s(0, 3), s(4, 5)} : Finset (Sym2 (Fin 6))) ⊆ G.edgeFinset := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rw [SimpleGraph.mem_edgeFinset]
    rcases he with rfl | rfl | rfl | rfl <;> rw [SimpleGraph.mem_edgeSet] <;> decide
  have h1 := Finset.card_le_card hsub
  have h2 : ({s(0, 1), s(0, 2), s(0, 3), s(4, 5)} : Finset (Sym2 (Fin 6))).card = 4 := by decide
  omega

private theorem main (s : ℕ) : PEqualNP.MetaComplexity.HasCircuitSize 6
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔
    5 ≤ s := by
  constructor
  · intro h
    rw [← funEq] at h
    have h1 := PEqualNP.MetaComplexity.L104 6 2 s G acyclic ⟨0, 1, by decide⟩ cover2 h
    have h2 := edges4
    omega
  · intro hs
    exact ⟨circ, fanin, le_trans (by decide) hs, evalOk⟩

end PEqualNP.Outside.L_meta_755

theorem PEqualNP.Outside.L_meta_755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s :=
  fun s => PEqualNP.Outside.L_meta_755.main s
