import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3444
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core Finset

-- A four-leaf star with one additional pendant edge from leaf one to vertex five.
abbrev tree := SimpleGraph.fromRel (fun i j : Fin 6 => (i=0 ∧ j≠5) ∨ (i=5 ∧ j=1))

-- Wires six to eight form the disjunction of the four star leaves.
-- The last gate takes the union of the pendant branch and the star branch.
def circ : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.or,[6,3]⟩,⟨.or,[7,4]⟩,⟨.or,[0,1]⟩,
  ⟨.and,[5,9]⟩,⟨.and,[10,8]⟩,⟨.and,[0,8]⟩,⟨.or,[11,12]⟩],13⟩
def color (i : Fin 6) : Bool := decide (i=0 ∨ i=5)
def M := maximalCores tree circ
def U := M.biUnion (coneSet 6 circ)
def U0 := U.filter (fun w => w∈M ∨ ((readers 6 circ w).filter (fun k=>InOutputCone 6 circ k)) ⊆ U)
def D := M.biUnion (gammaE tree circ)
def T : Finset (Fin 6) := {0}

set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma coloring : ∀ u v, tree.Adj u v → color u ≠ color v := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma fourFree : NoFourCycle tree := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma fanin : IsAO2 6 circ := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma computes : circuitFun 6 circ = graphFun tree ∅ := by funext x; revert x; decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma fixed : IsLiftFixedPoint tree circ := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma live : ∀ k < circ.gates.length, InOutputCone 6 circ k := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma cores_eq : M={5} := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma U_eq : U={0,1,2,3,4,5} := by rw [U,cores_eq];decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma U0_eq : U0={0,1,3,4,5} := by rw [U0,U_eq,cores_eq];decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma D_eq : D={s((1:Fin 6),(5:Fin 6))} := by rw [D,cores_eq];decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma minCover : IsMinCover (tree.deleteEdges (D:Set (Sym2 (Fin 6)))) T := by
  rw [D_eq]
  constructor <;> unfold SimpleGraph.IsVertexCover <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma deficit : U0.card+(tree.edgeFinset \ D).card+T.card+M.card=11 ∧ circ.size+1=9 := by
  rw [U0_eq,D_eq,cores_eq]
  decide +kernel

-- Clamping any gate to false destroys at least one true edge input.
def clamped (i : Nat) : Circuit := ⟨circ.gates.set i ⟨.or,[]⟩,circ.output⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma allEssential : ∀ j<circ.size,∃ u v:Fin 6, tree.Adj u v ∧
    circuitFun 6 (clamped j) (pairInput u v)=false := by decide +kernel

-- Every wire has a different Boolean function, including the output and the raw inputs.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
lemma distinctWires : ∀ i j : Fin 14,i≠j → ∃ x:Fin 6→Bool,
    (circ.wires (List.ofFn x)).getD i false ≠ (circ.wires (List.ofFn x)).getD j false := by decide +kernel
end PEqualNP.Outside.L_meta_3444

open PEqualNP.Outside.L_meta_3444 in
theorem PEqualNP.Outside.L_meta_3444 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro bound
  have h := bound 6 tree circ color T coloring fourFree fanin computes fixed live minCover
  change U0.card+(tree.edgeFinset \ D).card+T.card+M.card≤circ.size+1 at h
  exact (by omega : ¬ (11 : Nat) ≤ 9) (deficit.1 ▸ deficit.2 ▸ h)
