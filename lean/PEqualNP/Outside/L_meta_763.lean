import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_763

private abbrev graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun i j =>
    (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 4 ∧ j = 5)

private def position : Fin 6 → Fin 6 := ![1, 2, 0, 3, 4, 5]

private lemma forest : graph.IsAcyclic := by
  have preserves : ∀ i j, graph.Adj i j →
      (SimpleGraph.pathGraph 6).Adj (position i) (position j) := by decide
  let f : graph →g SimpleGraph.pathGraph 6 :=
    ⟨position, fun {i j} h => preserves i j h⟩
  have inj : Function.Injective position := by decide
  exact SimpleGraph.IsAcyclic.comap f inj (SimpleGraph.isAcyclic_pathGraph 6)

private lemma nonempty_edge : ∃ i j, graph.Adj i j := ⟨0, 1, by decide⟩

private lemma edge_count : graph.edgeFinset.card = 4 := by decide

private abbrev cover : Finset (Fin 6) := {0, 1, 4}

private lemma covers : ∀ i j, graph.Adj i j → i ∈ cover ∨ j ∈ cover := by decide

private lemma cover_lower : ∀ T : Finset (Fin 6),
    (∀ i j, graph.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by decide

private def graphFun (x : Fin 6 → Bool) : Bool :=
  decide (∃ i j, graph.Adj i j ∧ x i = true ∧ x j = true)

private lemma graphFun_spec : ∀ x : Fin 6 → Bool, graphFun x =
    ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) := by decide

end PEqualNP.Outside.L_meta_763

open PEqualNP.Outside.L_meta_763

theorem PEqualNP.Outside.L_meta_763 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  intro s
  rw [← funext graphFun_spec]
  constructor
  · intro h
    have lower := PEqualNP.MetaComplexity.L104 6 3 s graph forest nonempty_edge cover_lower h
    rw [edge_count] at lower
    omega
  · intro hs
    have upper := PEqualNP.MetaComplexity.L105 6 graph cover nonempty_edge covers
    have hcard : cover.card = 3 := by decide
    rw [edge_count, hcard] at upper
    obtain ⟨D, hD, hsize, heval⟩ := upper
    exact ⟨D, hD, hsize.trans hs, heval⟩
