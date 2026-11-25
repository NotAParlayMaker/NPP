import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7350_aux
open PEqualNP.CircuitLowerBounds

def st (L : List (ℕ × ℕ)) (g : Gate) : List (ℕ × ℕ) :=
  L ++ [(if g.op.eval [false, true] = true then
      (L.getD (g.inputs.getD 0 0) (0, 0)).1 ||| (L.getD (g.inputs.getD 1 0) (0, 0)).1
    else (L.getD (g.inputs.getD 0 0) (0, 0)).1 &&& (L.getD (g.inputs.getD 1 0) (0, 0)).1,
    (L.getD (g.inputs.getD 0 0) (0, 0)).2 + (L.getD (g.inputs.getD 1 0) (0, 0)).2)]

theorem ga (k : ℕ) (L : List (ℕ × ℕ)) (i : ℕ) :
    (L.map (fun p => p.1.testBit k)).getD i false = (L.getD i (0, 0)).1.testBit k := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[i]? <;> simp

theorem key (k : ℕ) : ∀ (gs : List Gate) (L : List (ℕ × ℕ)),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    (gs.foldl st L).map (fun p => p.1.testBit k) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (L.map (fun p => p.1.testBit k))
  | [], _, _ => rfl
  | g :: gs, L, h => by
    simp only [List.foldl_cons]
    rw [key k gs (st L g) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    obtain ⟨hop, hlen⟩ := h g (by simp)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    rcases hop with hop | hop <;>
      simp [st, hab, hop, GateOp.eval, ga, Nat.testBit_lor, Nat.testBit_land] <;>
      cases L[a]? <;> cases L[b]? <;> simp

end PEqualNP.Outside.L_meta_7350_aux

theorem PEqualNP.Outside.L_meta_7350 : have x1 : List (ℕ × ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (ℕ × ℕ) := fun (x1 : List (ℕ × ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) =>   have x3 : ℕ × ℕ := x1.getD (x2.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   have x4 : ℕ × ℕ := x1.getD (x2.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then x3.1 ||| x4.1 else x3.1 &&& x4.1, x3.2 + x4.2)]; ∀ (x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 : List (ℕ × ℕ)), (∀ x4 ∈ x2, (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x4.inputs.length = (2 : ℕ)) → ∀ (x5 x6 : ℕ), ((List.foldl x1 x3 x2).getD x6 ((0 : ℕ), (0 : ℕ))).1.testBit x5 = { gates := x2, output := x6 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.map (fun (x7 : ℕ × ℕ) => x7.1.testBit x5) x3) := by
  intro x1 gs L hg k out
  show ((List.foldl PEqualNP.Outside.L_meta_7350_aux.st L gs).getD out (0, 0)).1.testBit k =
    (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (L.map (fun p => p.1.testBit k)) gs).getD out false
  rw [← PEqualNP.Outside.L_meta_7350_aux.key k gs L hg, PEqualNP.Outside.L_meta_7350_aux.ga]
