import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Set one input to false. The first hypothesis permits replacing gates by false
-- whenever the cofactor at the output stays the same. It then asks for four gate
-- functions that are constant or already present on earlier wires. The second
-- hypothesis compresses all such gates simultaneously.
theorem PEqualNP.Outside.R_meta_2631_319
    (aliases : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let readers (v : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v, (G.neighborSet v).ncard = if v ∈ A then 0 else 3) →
      7 ≤ G.egirth →
      IsMinimalCircuit n C → circuitFun n C = f →
      (∀ v ∉ A, (readers v).length = 2 ∨ ((readers v).length = 3 ∧ ∀ g ∈ readers v, g.op = .or)) →
      (∃ v ∉ A, ∃ g ∈ readers v, g.op = .and) →
      ∃ v ∉ A, ∃ T S : Finset ℕ,
        let D : Circuit := ⟨C.gates.mapIdx (fun i g => if i ∈ T then ⟨.or,[]⟩ else g), C.output⟩
        let y (x : Fin n → Bool) := Function.update x v false
        (circuitFun n D ∘ y = f ∘ y) ∧
          4 ≤ S.card ∧ ∀ j ∈ S, j < C.size ∧
          (let w (i : ℕ) (x : Fin n → Bool) := (D.wires (List.ofFn (y x))).getD i false;
          (∃ b : Bool, w (n+j) = fun _ => b) ∨ ∃ i < n+j, w (n+j) = w i))
    (compress : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (S : Finset ℕ), FanInTwo C →
      circuitFun n C (fun _ => false) = false →
      (∀ j ∈ S, j < C.size ∧ (let w (i : ℕ) (x : Fin n → Bool) := (C.wires (List.ofFn (Function.update x v false))).getD i false;
          (∃ b : Bool, w (n+j) = fun _ => b) ∨ ∃ i < n+j, w (n+j) = w i)) →
      ∃ s, s + S.card ≤ C.size ∧ HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  intro n G inst A C f readers deg girth iso edge fan computes least uses anchor
  obtain ⟨u,hu,_,gu⟩ := anchor
  have simpler (v : Fin n) (hv : v ∉ A) : (readers v).length = 2 ∨
      ((readers v).length = 3 ∧ ∀ g ∈ readers v, g.op = .or) := by
    obtain ⟨lo,hi,ops⟩ := uses v hv
    by_cases e : (readers v).length = 2
    · exact Or.inl e
    · have h : (readers v).length = 3 := by omega
      exact Or.inr ⟨h,ops h⟩
  have mn : IsMinimalCircuit n C := by
    refine ⟨fan,fun D df eq => least D.size ⟨D,df,le_rfl,?_⟩⟩
    exact congrFun (eq.trans computes)
  have gir : 7 ≤ G.egirth := SimpleGraph.le_egirth.mpr fun a w hw => by exact_mod_cast girth a w hw
  have degrees (w : Fin n) : (G.neighborSet w).ncard = if w ∈ A then 0 else 3 := by
    by_cases h : w ∈ A
    · have empty : G.neighborSet w = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun z e => iso w z e h
      simp [empty,h]
    · simpa [h] using deg w h
  obtain ⟨v,hv,T,S,equiv,four,cert⟩ := aliases n G A C degrees gir mn computes simpler ⟨u,hu,gu⟩
  let D : Circuit := ⟨C.gates.mapIdx (fun i g => if i ∈ T then ⟨.or,[]⟩ else g), C.output⟩
  have df : FanInTwo D := by
    intro g hg
    obtain ⟨i,hi,e⟩ := List.mem_mapIdx.mp hg
    by_cases h : i ∈ T
    · simp only [h,ite_true] at e
      subst g
      simp
    · simp only [h,ite_false] at e
      subst g
      exact fan _ (List.getElem_mem _)
  have dz : circuitFun n D (fun _ => false) = false := by
    have ev := congrFun equiv (fun _ => false)
    have up : Function.update (fun _ : Fin n => false) v false = fun _ => false := by
      ext i
      by_cases h : i = v <;> simp [h]
    change circuitFun n D (Function.update _ v false) = f (Function.update _ v false) at ev
    rw [up] at ev
    rw [ev]
    change (decide (∃ a ∈ A, false = true) || decide (∃ a b, G.Adj a b ∧ false = true ∧ false = true)) = false
    simp
  have ds : D.size = C.size := List.length_mapIdx
  obtain ⟨s,bound,hs⟩ := compress n D v S df dz (fun j hj => ⟨ds.symm ▸ (cert j hj).1,(cert j hj).2⟩)
  have eq : (fun x => circuitFun n D (Function.update x v false)) = fun x => f (Function.update x v false) := equiv
  exact ⟨v,hv,s,by omega,eq ▸ hs⟩
