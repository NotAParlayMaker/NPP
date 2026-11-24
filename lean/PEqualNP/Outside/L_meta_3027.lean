import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_3027

def inc (p : Fin 3) (l : Fin 2) : Bool :=
  (p == 0 && l == 0) || (p == 1 && l == 1) || (p == 2 && l == 0)

def circ : Circuit where
  gates := [
    ⟨.or, [0, 1]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.and, [8, 13]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [14, 15]⟩]
  output := 16

-- Precisely wires 14, 15 and 16 imply that an incidence edge is present.
-- Larger wire indices evaluate to false on every input.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem below_table : ∀ w : Fin 17, (∀ z : Fin (3 + 2) → Bool, (circ.wires (List.ofFn z)).getD w.val false = true →
      ∃ p : Fin 3, ∃ l : Fin 2, inc p l = true ∧
        z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true) ↔ 14 ≤ w.val := by
  decide

theorem below_iff (w : ℕ) : (∀ z : Fin (3 + 2) → Bool, (circ.wires (List.ofFn z)).getD w false = true →
      ∃ p : Fin 3, ∃ l : Fin 2, inc p l = true ∧
        z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true) ↔ 14 ≤ w := by
  by_cases hw : w < 17
  · exact below_table ⟨w, hw⟩
  · have hn : 17 ≤ w := by omega
    have hx (z : Fin (3 + 2) → Bool) :
        (circ.wires (List.ofFn z)).getD w false = false := by
      apply List.getD_eq_default
      have length_eq : (circ.wires (List.ofFn z)).length = 17 := rfl
      omega
    constructor
    · intro _
      omega
    · intro _ z hz
      rw [hx z] at hz
      cases hz

end PEqualNP.Outside.L_meta_3027

open PEqualNP.Outside.L_meta_3027

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.L_meta_3027 : ¬ (∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (c : ℕ), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ j1 < C.gates.length, (∃ z2 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z2)).getD ((Np + Nl) + j1) false = true) ∧ ((Np + Nl) + j1 = C.output ∨ ∃ k3 < C.gates.length, (Np + Nl) + j1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k3).inputs)) → (∀ j4 < C.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ¬ (∀ z6 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z6)).getD ((Np + Nl) + j4) false = true → ∃ p7 : Fin Np, ∃ l8 : Fin Nl, I p7 l8 ∧ z6 (Fin.castAdd Nl p7) = true ∧ z6 (Fin.natAdd Np l8) = true)) → ∀ w5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs, ¬ (∀ z9 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z9)).getD (w5) false = true → ∃ p10 : Fin Np, ∃ l11 : Fin Nl, I p10 l11 ∧ z9 (Fin.castAdd Nl p10) = true ∧ z9 (Fin.natAdd Np l11) = true)) → (∀ j12 < C.gates.length, (∀ z15 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z15)).getD ((Np + Nl) + j12) false = true → ∃ p16 : Fin Np, ∃ l17 : Fin Nl, I p16 l17 ∧ z15 (Fin.castAdd Nl p16) = true ∧ z15 (Fin.natAdd Np l17) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j12).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ w13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j12).inputs, (∀ z18 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z18)).getD (w13) false = true → ∃ p19 : Fin Np, ∃ l20 : Fin Nl, I p19 l20 ∧ z18 (Fin.castAdd Nl p19) = true ∧ z18 (Fin.natAdd Np l20) = true)) ∧ ((Np + Nl) + j12 ≠ C.output → PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) ((Np + Nl) + j12) = 1 ∧ ∀ k14 < C.gates.length, (Np + Nl) + j12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ z21 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z21)).getD ((Np + Nl) + k14) false = true → ∃ p22 : Fin Np, ∃ l23 : Fin Nl, I p22 l23 ∧ z21 (Fin.castAdd Nl p22) = true ∧ z21 (Fin.natAdd Np l23) = true))) → (∀ j24 < C.gates.length, ∀ k25 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z28 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z28)).getD ((Np + Nl) + j24) false = true → ∃ p29 : Fin Np, ∃ l30 : Fin Nl, I p29 l30 ∧ z28 (Fin.castAdd Nl p29) = true ∧ z28 (Fin.natAdd Np l30) = true) → (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z31 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z31)).getD ((Np + Nl) + k25) false = true → ∃ p32 : Fin Np, ∃ l33 : Fin Nl, I p32 l33 ∧ z31 (Fin.castAdd Nl p32) = true ∧ z31 (Fin.natAdd Np l33) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs.Nodup ∧ ∀ w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs, w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).inputs → j24 = k25)) → c < C.gates.length → ¬ (∀ z34 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z34)).getD ((Np + Nl) + c) false = true → ∃ p35 : Fin Np, ∃ l36 : Fin Nl, I p35 l36 ∧ z34 (Fin.castAdd Nl p35) = true ∧ z34 (Fin.natAdd Np l36) = true) → (∀ k37 < C.gates.length, ¬ PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k37 c → ∀ g38 < C.gates.length, PEqualNP.EdgeOwnership.InCone (Np + Nl) C g38 c → (Np + Nl) + g38 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k37).inputs) → (∃ v39 : Fin (Np + Nl), (C.wires (List.ofFn (fun i40 : Fin (Np + Nl) => decide (i40 = v39)))).getD ((Np + Nl) + c) false = true) → (∃ p41 : Fin Np, ∃ l42 : Fin Nl, (I p41 l42 ∧ (C.wires (List.ofFn (fun i43 : Fin (Np + Nl) => decide (i43 = Fin.castAdd Nl p41)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i44 : Fin (Np + Nl) => decide (i44 = Fin.natAdd Np l42)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i45 : Fin (Np + Nl) => decide (i45 = Fin.castAdd Nl p41 ∨ i45 = Fin.natAdd Np l42)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i46 : Fin (Np + Nl) => decide (i46 = Fin.castAdd Nl p41 ∨ i46 = Fin.natAdd Np l42)) = false)) → (Finset.univ.filter fun v47 : Fin (Np + Nl) => (C.wires (List.ofFn (fun i53 : Fin (Np + Nl) => decide (i53 = v47)))).getD ((Np + Nl) + c) false = true).card + (Finset.univ.filter fun p48 : Fin Np => ∃ l49 : Fin Nl, (I p48 l49 ∧ (C.wires (List.ofFn (fun i54 : Fin (Np + Nl) => decide (i54 = Fin.castAdd Nl p48)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i55 : Fin (Np + Nl) => decide (i55 = Fin.natAdd Np l49)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i56 : Fin (Np + Nl) => decide (i56 = Fin.castAdd Nl p48 ∨ i56 = Fin.natAdd Np l49)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i57 : Fin (Np + Nl) => decide (i57 = Fin.castAdd Nl p48 ∨ i57 = Fin.natAdd Np l49)) = false)).card + (Finset.univ.filter fun l51 : Fin Nl => ∃ p50 : Fin Np, (I p50 l51 ∧ (C.wires (List.ofFn (fun i58 : Fin (Np + Nl) => decide (i58 = Fin.castAdd Nl p50)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i59 : Fin (Np + Nl) => decide (i59 = Fin.natAdd Np l51)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i60 : Fin (Np + Nl) => decide (i60 = Fin.castAdd Nl p50 ∨ i60 = Fin.natAdd Np l51)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i61 : Fin (Np + Nl) => decide (i61 = Fin.castAdd Nl p50 ∨ i61 = Fin.natAdd Np l51)) = false)).card ≤ ((Finset.range C.gates.length).filter fun k52 => PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k52 c).card) := by
  intro universal
  let _ : DecidableEq GateOp := gateOpDecEq
  have result := universal 3 2 (fun p l => inc p l = true) circ 3
    (by decide) (by decide) (by decide) (by decide)
    (by simp only [below_iff, Nat.forall_lt_iff_fin, List.forall_mem_iff_get]; decide)
    (by simp only [below_iff, Nat.forall_lt_iff_fin, List.forall_mem_iff_get]; decide)
    (by
      simp only [below_iff, Nat.forall_lt_iff_fin, List.forall_mem_iff_get]
      intro j k hoj hj hok hk
      have choices (u : Fin 12) (lo : 14 ≤ 3 + 2 + (u : ℕ)) :
          u = 9 ∨ u = 10 ∨ u = 11 := by
        have hi : u.val < 12 := u.isLt
        have eu : u.val = 9 ∨ u.val = 10 ∨ u.val = 11 := by omega
        rcases eu with h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext h))
      rcases choices j hj with rfl | rfl | rfl <;>
        rcases choices k hk with rfl | rfl | rfl <;>
        first
        | exact False.elim ((by decide : GateOp.or ≠ GateOp.and) hoj)
        | exact False.elim ((by decide : GateOp.or ≠ GateOp.and) hok)
        | decide)
    (by decide) (by decide)
    (by simp only [Nat.forall_lt_iff_fin]; decide)
    (by decide) (by decide)
  exact (by decide : ¬ _) result
