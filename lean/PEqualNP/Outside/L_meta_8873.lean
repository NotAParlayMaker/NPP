import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8873_aux

open PEqualNP.CircuitLowerBounds

theorem getD_tb (v : List ℕ) (i k : ℕ) :
    (v.getD i 0).testBit k = (v.map (fun x => x.testBit k)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases v[i]? <;> simp

theorem inv (k : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) (v : List ℕ) :
    (List.foldl (fun (x6 : List ℕ) (x7 : Gate) => x6 ++ [if x7.op.eval [Bool.true, Bool.false] = Bool.true then x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) ||| x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ) else x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) &&& x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ)]) v gs).map (fun x => x.testBit k)
      = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (v.map (fun x => x.testBit k)) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    rw [List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    obtain ⟨hop, hl⟩ := hg g (List.mem_cons_self ..)
    obtain ⟨op, ins⟩ := g
    simp only at hop hl ⊢
    match ins, hl with
    | [a, b], _ =>
      rcases hop with h | h <;> subst h <;> simp [GateOp.eval, Nat.testBit_lor, Nat.testBit_land, getD_tb] <;> cases v[a]? <;> cases v[b]? <;> simp

end PEqualNP.Outside.L_meta_8873_aux

theorem PEqualNP.Outside.L_meta_8873 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 : List ℕ) (x5 : ℕ),       have x6 : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x6 : List ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) =>         have x8 : ℕ := x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);         have x9 : ℕ := x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);         x6 ++ [if x7.op.eval [Bool.true, Bool.false] = Bool.true then x8 ||| x9 else x8 &&& x9];       ((List.foldl x6 x4 x2.gates).getD x2.output (0 : ℕ)).testBit x5 = x2.eval (List.map (fun (x7 : ℕ) => x7.testBit x5) x4) := by
  intro x1 x2 h x4 x5 x6
  exact (PEqualNP.Outside.L_meta_8873_aux.getD_tb _ _ _).trans
    (congrArg (fun l => List.getD l x2.output false)
      (PEqualNP.Outside.L_meta_8873_aux.inv x5 x2.gates (fun g hg => ⟨h.1 g hg, h.2.2 g hg⟩) x4))
