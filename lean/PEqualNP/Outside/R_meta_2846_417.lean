import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_2846_417
    (noNesting :
      ∀ (p l : Nat) (I : Fin p → Fin l → Prop) [DecidableRel I] (C : Circuit),
      let n := p+l
      let f := fun z : Fin n → Bool => decide (∃ a b, I a b ∧ z (Fin.castAdd l a) = true ∧ z (Fin.natAdd p b) = true)
      let g := gateAt C
      let s := C.gates.length
      (∀ a b c d, a≠b → c≠d → ¬(I a c ∧ I a d ∧ I b c ∧ I b d)) →
      IsAO2 n C → circuitFun n C = f →
      (∀ D, IsAO2 n D → circuitFun n D = f → C.size ≤ D.size) →
      (∃ T : Finset Nat, (∀ i∈T, i<s ∧ (g i).op=.or ∧
        (n+i=C.output ∨ ∃ k∈T, ∀ j<s, n+i∈(g j).inputs ↔ j=k)) ∧
        ∀ w, (∀ z, (C.wires (List.ofFn z)).getD w false=true → f z=true) →
        (∃ k<s, (g k).op=.or ∧ w∈(g k).inputs) → ∀ k<s, w∈(g k).inputs → k∈T) →
      andPairs n C = 0)
    (noWaste :
      ∀ (n : Nat) (C : Circuit), IsAO2 n C →
          (∀ D, IsAO2 n D → circuitFun n D = circuitFun n C → C.size ≤ D.size) →
          ∀ i<C.gates.length, n+i=C.output ∨ ∃ j<C.gates.length, n+i∈(gateAt C j).inputs)
    (reconstruct :
      ∀ (p l : Nat) (C : Circuit),
      let n := p+l
      let s := C.gates.length
      let g := gateAt C
      IsAO2 n C → andPairs n C = 0 →
      (∀ i<s, n+i=C.output ∨ ∃ j<s, n+i∈(g j).inputs) →
      (∀ b : Bool, C.eval (List.ofFn (fun i : Fin n => decide (i.val<p) == b))=false) →
      ∃ P L : Finset Nat,
        (∀ w∈P, w<p ∨ ∃ i<s, w=n+i ∧ (g i).op=.or ∧ ∀ u∈(g i).inputs, u∈P) ∧
        (∀ w∈L, (p≤w ∧ w<n) ∨ ∃ i<s, w=n+i ∧ (g i).op=.or ∧ ∀ u∈(g i).inputs, u∈L) ∧
        ∀ i<s, (g i).op=.and → ∃ a b : Nat, (g i).inputs=[a,b] ∧ ((a∈P ∧ b∈L) ∨ (a∈L ∧ b∈P)))
    : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) ∧ ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  intro p l I inst C hc4 model correct least stuck
  let f := fun z : Fin (p+l) → Bool => decide (∃ a b, I a b ∧ z (Fin.castAdd l a) = true ∧ z (Fin.natAdd p b) = true)
  have eqf : circuitFun (p+l) C = f := funext correct
  have minimal (D : Circuit) (hd : IsAO2 (p+l) D) (hh : circuitFun (p+l) D = f) : C.size ≤ D.size :=
    least D hd (congrFun hh)
  have emptyPairs := noNesting p l I C hc4 model eqf minimal (by
    obtain ⟨T,hT,hR⟩ := stuck
    refine ⟨T,hT,?_⟩
    intro w hw
    apply hR w
    intro z hz
    exact of_decide_eq_true (hw z hz))
  refine reconstruct p l C model emptyPairs (noWaste _ C model (fun D hd hh => minimal D hd (hh.trans eqf))) ?_
  intro b
  have hr := correct (fun i => decide (i.val<p) == b)
  apply Eq.trans hr
  apply decide_eq_false
  rintro ⟨a,k,_,ha,hk⟩
  have hl : ¬p+k.val<p := by omega
  change (decide (a.val<p) == b) = true at ha
  change (decide (p+k.val<p) == b) = true at hk
  cases b <;> simp [a.isLt,hl] at ha hk
