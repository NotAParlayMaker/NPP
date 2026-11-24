import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.SplitCount

namespace PEqualNP.Outside.L_meta_3027_aux

def incident (p : Fin 3) (l : Fin 2) : Prop :=
  (p.val, l.val) ∈ [(0, 0), (1, 1), (2, 0)]

def decIncident : DecidableRel incident :=
  fun p l => inferInstanceAs (Decidable ((p.val, l.val) ∈ [(0, 0), (1, 1), (2, 0)]))

-- The first three gates combine the two disjoint edges with the two cross pairs.
-- A second branch filters out the cross pairs before the output.
def witness : Circuit := ⟨[
  ⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [2, 7]⟩,
  ⟨.or, [0, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [3, 4]⟩,
  ⟨.and, [11, 12]⟩, ⟨.and, [8, 13]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [14, 15]⟩], 16⟩

abbrev edgePresent (z : Fin 5 → Bool) : Prop :=
  ∃ (p : Fin 3) (l : Fin 2), incident p l ∧
    z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true

abbrev wire (w : ℕ) (z : Fin 5 → Bool) : Bool := (witness.wires (List.ofFn z)).getD w false

def safe (w : ℕ) : Prop := ∀ z : Fin 5 → Bool, wire w z = true → edgePresent z

def decSafe : DecidablePred safe := by
  letI : DecidableRel incident := decIncident
  intro w
  unfold safe
  infer_instance

abbrev unit (v : Fin 5) : Fin 5 → Bool := fun i => decide (i = v)

abbrev ray (p : Fin 3) (l : Fin 2) : Fin 5 → Bool :=
  fun i => decide (i = Fin.castAdd 2 p ∨ i = Fin.natAdd 3 l)

abbrev cleared : Circuit := ⟨witness.gates.set 3 ⟨.or, []⟩, witness.output⟩

abbrev lost (p : Fin 3) (l : Fin 2) : Prop :=
  incident p l ∧ wire 8 (unit (Fin.castAdd 2 p)) = false ∧
    wire 8 (unit (Fin.natAdd 3 l)) = false ∧ circuitFun 5 witness (ray p l) = true ∧
      circuitFun 5 cleared (ray p l) = false

theorem noCycle : ∀ (p p' : Fin 3) (l l' : Fin 2), p ≠ p' → l ≠ l' →
    ¬ (incident p l ∧ incident p l' ∧ incident p' l ∧ incident p' l') := by
  letI : DecidableRel incident := decIncident
  decide

theorem inModel : PEqualNP.TopForm.IsAO2 5 witness := by decide

set_option maxRecDepth 8192 in
theorem computes : letI : DecidableRel incident := decIncident
    ∀ z : Fin 5 → Bool, circuitFun 5 witness z = decide (edgePresent z) := by
  letI : DecidableRel incident := decIncident
  decide

set_option maxRecDepth 8192 in
theorem live : ∀ j < witness.gates.length,
    (∃ z : Fin 5 → Bool, wire (5 + j) z = true) ∧
      (5 + j = witness.output ∨ ∃ k < witness.gates.length, 5 + j ∈ (gateAt witness k).inputs) := by
  decide

set_option maxRecDepth 8192 in
theorem unsafeInputs : ∀ j < witness.gates.length, ((gateAt witness j).op = .and ∨
    ¬ safe (5 + j)) → ∀ w ∈ (gateAt witness j).inputs, ¬ safe w := by
  letI : DecidableEq GateOp := gateOpDecEq
  letI : DecidablePred safe := decSafe
  decide

set_option maxRecDepth 8192 in
theorem safeReads : ∀ j < witness.gates.length, safe (5 + j) →
    ((gateAt witness j).op = .or → ∀ w ∈ (gateAt witness j).inputs, safe w) ∧
    (5 + j ≠ witness.output → readsIn witness (Finset.range witness.gates.length) (5 + j) = 1 ∧
      ∀ k < witness.gates.length, 5 + j ∈ (gateAt witness k).inputs →
        (gateAt witness k).op = .or ∧ safe (5 + k)) := by
  letI : DecidableEq GateOp := gateOpDecEq
  letI : DecidablePred safe := decSafe
  have finite : ∀ j : Fin 12, safe (5 + j.val) →
      ((gateAt witness j.val).op = .or → ∀ w ∈ (gateAt witness j.val).inputs, safe w) ∧
      (5 + j.val ≠ witness.output →
        readsIn witness (Finset.range witness.gates.length) (5 + j.val) = 1 ∧
        ∀ k : Fin 12, 5 + j.val ∈ (gateAt witness k.val).inputs →
          (gateAt witness k.val).op = .or ∧ safe (5 + k.val)) := by decide
  intro j hj hs
  obtain ⟨hor, hreader⟩ := finite ⟨j, hj⟩ hs
  refine ⟨hor, ?_⟩
  intro hout
  obtain ⟨hcount, hcons⟩ := hreader hout
  exact ⟨hcount, fun k hk => hcons ⟨k, hk⟩⟩

set_option maxRecDepth 8192 in
theorem distinctSafeOperands : ∀ j < witness.gates.length, ∀ k < witness.gates.length,
    (gateAt witness j).op = .and → safe (5 + j) → (gateAt witness k).op = .and → safe (5 + k) →
    (gateAt witness j).inputs.Nodup ∧ ∀ w ∈ (gateAt witness j).inputs,
      w ∈ (gateAt witness k).inputs → j = k := by
  letI : DecidableEq GateOp := gateOpDecEq
  letI : DecidablePred safe := decSafe
  have finite : ∀ j k : Fin 12, (gateAt witness j.val).op = .and → safe (5 + j.val) →
      (gateAt witness k.val).op = .and → safe (5 + k.val) →
      (gateAt witness j.val).inputs.Nodup ∧ ∀ w ∈ (gateAt witness j.val).inputs,
        w ∈ (gateAt witness k.val).inputs → j.val = k.val := by decide
  intro j hj k hk
  exact finite ⟨j, hj⟩ ⟨k, hk⟩

theorem privateCone : ∀ k < witness.gates.length, ¬ InConeOrSelf 5 witness k 3 →
    ∀ g < witness.gates.length, InCone 5 witness g 3 → 5 + g ∉ (gateAt witness k).inputs := by
  have finite : ∀ k g : Fin 12, ¬ InConeOrSelf 5 witness k.val 3 → InCone 5 witness g.val 3 →
      5 + g.val ∉ (gateAt witness k.val).inputs := by decide +kernel
  intro k hk hout g hg hin
  exact finite ⟨k, hk⟩ ⟨g, hg⟩ hout hin

theorem rootUnsafe : ¬ safe 8 := by
  letI : DecidablePred safe := decSafe
  decide

theorem rootLinear : ∃ v : Fin 5, wire 8 (unit v) = true := ⟨2, by decide⟩

theorem rootLost : ∃ (p : Fin 3) (l : Fin 2), lost p l := by
  letI : DecidableRel incident := decIncident
  exact ⟨0, 0, by decide⟩

theorem badCount : letI : DecidableRel incident := decIncident
    ¬ ((Finset.univ.filter (fun v : Fin 5 => wire 8 (unit v) = true)).card +
        (Finset.univ.filter (fun p : Fin 3 => ∃ l : Fin 2, lost p l)).card +
        (Finset.univ.filter (fun l : Fin 2 => ∃ p : Fin 3, lost p l)).card ≤
        ((Finset.range witness.gates.length).filter (fun k => InConeOrSelf 5 witness k 3)).card) := by
  letI : DecidableRel incident := decIncident
  decide

end PEqualNP.Outside.L_meta_3027_aux

open PEqualNP.Outside.L_meta_3027_aux

theorem PEqualNP.Outside.L_meta_3027 : ¬ (∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (c : ℕ), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ j1 < C.gates.length, (∃ z2 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z2)).getD ((Np + Nl) + j1) false = true) ∧ ((Np + Nl) + j1 = C.output ∨ ∃ k3 < C.gates.length, (Np + Nl) + j1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k3).inputs)) → (∀ j4 < C.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ¬ (∀ z6 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z6)).getD ((Np + Nl) + j4) false = true → ∃ p7 : Fin Np, ∃ l8 : Fin Nl, I p7 l8 ∧ z6 (Fin.castAdd Nl p7) = true ∧ z6 (Fin.natAdd Np l8) = true)) → ∀ w5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs, ¬ (∀ z9 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z9)).getD (w5) false = true → ∃ p10 : Fin Np, ∃ l11 : Fin Nl, I p10 l11 ∧ z9 (Fin.castAdd Nl p10) = true ∧ z9 (Fin.natAdd Np l11) = true)) → (∀ j12 < C.gates.length, (∀ z15 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z15)).getD ((Np + Nl) + j12) false = true → ∃ p16 : Fin Np, ∃ l17 : Fin Nl, I p16 l17 ∧ z15 (Fin.castAdd Nl p16) = true ∧ z15 (Fin.natAdd Np l17) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j12).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ w13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j12).inputs, (∀ z18 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z18)).getD (w13) false = true → ∃ p19 : Fin Np, ∃ l20 : Fin Nl, I p19 l20 ∧ z18 (Fin.castAdd Nl p19) = true ∧ z18 (Fin.natAdd Np l20) = true)) ∧ ((Np + Nl) + j12 ≠ C.output → PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) ((Np + Nl) + j12) = 1 ∧ ∀ k14 < C.gates.length, (Np + Nl) + j12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ z21 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z21)).getD ((Np + Nl) + k14) false = true → ∃ p22 : Fin Np, ∃ l23 : Fin Nl, I p22 l23 ∧ z21 (Fin.castAdd Nl p22) = true ∧ z21 (Fin.natAdd Np l23) = true))) → (∀ j24 < C.gates.length, ∀ k25 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z28 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z28)).getD ((Np + Nl) + j24) false = true → ∃ p29 : Fin Np, ∃ l30 : Fin Nl, I p29 l30 ∧ z28 (Fin.castAdd Nl p29) = true ∧ z28 (Fin.natAdd Np l30) = true) → (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z31 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z31)).getD ((Np + Nl) + k25) false = true → ∃ p32 : Fin Np, ∃ l33 : Fin Nl, I p32 l33 ∧ z31 (Fin.castAdd Nl p32) = true ∧ z31 (Fin.natAdd Np l33) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs.Nodup ∧ ∀ w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs, w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).inputs → j24 = k25)) → c < C.gates.length → ¬ (∀ z34 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z34)).getD ((Np + Nl) + c) false = true → ∃ p35 : Fin Np, ∃ l36 : Fin Nl, I p35 l36 ∧ z34 (Fin.castAdd Nl p35) = true ∧ z34 (Fin.natAdd Np l36) = true) → (∀ k37 < C.gates.length, ¬ PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k37 c → ∀ g38 < C.gates.length, PEqualNP.EdgeOwnership.InCone (Np + Nl) C g38 c → (Np + Nl) + g38 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k37).inputs) → (∃ v39 : Fin (Np + Nl), (C.wires (List.ofFn (fun i40 : Fin (Np + Nl) => decide (i40 = v39)))).getD ((Np + Nl) + c) false = true) → (∃ p41 : Fin Np, ∃ l42 : Fin Nl, (I p41 l42 ∧ (C.wires (List.ofFn (fun i43 : Fin (Np + Nl) => decide (i43 = Fin.castAdd Nl p41)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i44 : Fin (Np + Nl) => decide (i44 = Fin.natAdd Np l42)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i45 : Fin (Np + Nl) => decide (i45 = Fin.castAdd Nl p41 ∨ i45 = Fin.natAdd Np l42)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i46 : Fin (Np + Nl) => decide (i46 = Fin.castAdd Nl p41 ∨ i46 = Fin.natAdd Np l42)) = false)) → (Finset.univ.filter fun v47 : Fin (Np + Nl) => (C.wires (List.ofFn (fun i53 : Fin (Np + Nl) => decide (i53 = v47)))).getD ((Np + Nl) + c) false = true).card + (Finset.univ.filter fun p48 : Fin Np => ∃ l49 : Fin Nl, (I p48 l49 ∧ (C.wires (List.ofFn (fun i54 : Fin (Np + Nl) => decide (i54 = Fin.castAdd Nl p48)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i55 : Fin (Np + Nl) => decide (i55 = Fin.natAdd Np l49)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i56 : Fin (Np + Nl) => decide (i56 = Fin.castAdd Nl p48 ∨ i56 = Fin.natAdd Np l49)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i57 : Fin (Np + Nl) => decide (i57 = Fin.castAdd Nl p48 ∨ i57 = Fin.natAdd Np l49)) = false)).card + (Finset.univ.filter fun l51 : Fin Nl => ∃ p50 : Fin Np, (I p50 l51 ∧ (C.wires (List.ofFn (fun i58 : Fin (Np + Nl) => decide (i58 = Fin.castAdd Nl p50)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i59 : Fin (Np + Nl) => decide (i59 = Fin.natAdd Np l51)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i60 : Fin (Np + Nl) => decide (i60 = Fin.castAdd Nl p50 ∨ i60 = Fin.natAdd Np l51)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i61 : Fin (Np + Nl) => decide (i61 = Fin.castAdd Nl p50 ∨ i61 = Fin.natAdd Np l51)) = false)).card ≤ ((Finset.range C.gates.length).filter fun k52 => PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k52 c).card) := by
  intro universal
  letI : DecidableRel incident := decIncident
  exact badCount (universal 3 2 incident witness 3 noCycle inModel computes live unsafeInputs
    safeReads distinctSafeOperands (by decide) rootUnsafe privateCone rootLinear rootLost)
