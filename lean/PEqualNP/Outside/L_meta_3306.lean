import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.L_meta_3306 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  classical
  intro n C P L hC sides
  let ordered (g : Gate) := g.inputs.getD 0 0 ∈ L ∧ g.inputs.getD 1 0 ∈ P
  let orient (g : Gate) : Gate :=
    if g.op = GateOp.and ∧ ¬ ordered g then ⟨g.op,g.inputs.reverse⟩ else g
  let D : Circuit := ⟨C.gates.map orient,C.output⟩
  have op (g : Gate) : (orient g).op = g.op := by unfold orient; split <;> rfl
  have perm (g : Gate) : (orient g).inputs.Perm g.inputs := by
    unfold orient
    split
    · exact List.reverse_perm _
    · exact List.Perm.refl _
  have sameOr (g : Gate) (h : g.op = GateOp.or) : orient g = g := by simp [orient,h]
  have atGate (i : ℕ) : gateAt D i = orient (gateAt C i) := by
    simp only [D,gateAt,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases C.gates[i]? with
    | none => exact (sameOr ⟨.or,[]⟩ rfl).symm
    | some g => rfl
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have commutes (w : List Bool) (g : Gate) : step w (orient g) = step w g := by
    unfold orient
    split
    · rename_i h
      dsimp only [step]
      rw [h.1]
      congr 2
      apply Bool.eq_iff_iff.mpr
      simp [GateOp.eval,List.all_eq_true]
    · rfl
  have run (gs : List Gate) (w : List Bool) :
      (gs.map orient).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih => simp only [List.map_cons,List.foldl_cons,commutes,ih]
  have lengthD : D.gates.length = C.gates.length := List.length_map _
  refine ⟨D,⟨?_,?_,?_⟩,lengthD,?_,fun i => (atGate i) ▸ op _,?_,?_⟩
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    rw [op]
    exact hC.1 a ha
  · intro j hj i hi
    rw [atGate] at hi
    exact hC.2.1 j (hj.trans_eq lengthD) i ((perm _).mem_iff.mp hi)
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact (perm a).length_eq.trans (hC.2.2 a ha)
  · funext x
    exact congrArg (fun w : List Bool => w.getD C.output false) (run C.gates (List.ofFn x))
  · intro i hi
    exact (atGate i).trans (sameOr _ hi)
  · intro j hj hand
    rw [atGate,op] at hand
    obtain ⟨a,b,hab,hor⟩ := sides j (hj.trans_eq lengthD) hand
    rw [atGate]
    by_cases good : ordered (gateAt C j)
    · refine ⟨a,b,by simp [orient,good,hab],?_⟩
      simpa [ordered,hab] using good
    · have wrong : ¬ (a ∈ L ∧ b ∈ P) := by simpa [ordered,hab] using good
      obtain ⟨ap,bl⟩ := hor.resolve_right wrong
      exact ⟨b,a,by simp [orient,hand,good,hab],bl,ap⟩
