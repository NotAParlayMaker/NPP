import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_8343

theorem getD_map_tb (l : List ℕ) (i k : ℕ) :
    (l.map (fun x => x.testBit k)).getD i false = (l.getD i 0).testBit k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem step (g : Gate) (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : List ℕ) (k : ℕ) :
    (w ++ [if g.op.eval [false, true] = true then w.getD (g.inputs.getD 0 0) 0 ||| w.getD (g.inputs.getD 1 0) 0 else w.getD (g.inputs.getD 0 0) 0 &&& w.getD (g.inputs.getD 1 0) 0]).map (fun x => x.testBit k)
      = w.map (fun x => x.testBit k) ++ [g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit k)).getD i false)] := by
  obtain ⟨hop, hl⟩ := hg
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 hl
  simp only [hpq, List.map_cons, List.map_nil, getD_map_tb, List.map_append,
    List.getD_cons_zero, List.getD_cons_succ]
  rcases hop with h | h <;>
    simp [h, GateOp.eval, Nat.testBit_land, Nat.testBit_lor]

theorem fold_tb (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) (k : ℕ) :
    ∀ w : List ℕ, (List.foldl (fun (w : List ℕ) (g : Gate) => w ++ [if g.op.eval [false, true] = true then w.getD (g.inputs.getD 0 0) 0 ||| w.getD (g.inputs.getD 1 0) 0 else w.getD (g.inputs.getD 0 0) 0 &&& w.getD (g.inputs.getD 1 0) 0]) w gs).map (fun x => x.testBit k)
      = List.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit k)) gs := by
  induction gs with
  | nil =>
    intro w
    rfl
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    rw [ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    exact step g (hg g (by simp)) w k

theorem main (C : Circuit) (x2 : List ℕ) (x3 x4 : ℕ)
    (h : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ((List.foldl (fun (w : List ℕ) (g : Gate) => w ++ [if g.op.eval [false, true] = true then w.getD (g.inputs.getD 0 0) 0 ||| w.getD (g.inputs.getD 1 0) 0 else w.getD (g.inputs.getD 0 0) 0 &&& w.getD (g.inputs.getD 1 0) 0]) x2 C.gates).getD x3 0).testBit x4
      = (C.wires (List.map (fun (x6 : ℕ) => x6.testBit x4) x2)).getD x3 false := by
  rw [← getD_map_tb, fold_tb C.gates h x4 x2]
  rfl

end PEqualNP.Outside.L_meta_8343

theorem PEqualNP.Outside.L_meta_8343 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ) (x3 x4 : ℕ),   (∀ x5 ∈ x1.gates, (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x5.inputs.length = (2 : ℕ)) →     ((List.foldl                 (fun (x6 : List ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) =>                   have x8 : ℕ := x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                   have x9 : ℕ := x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                   x6 ++ [if x7.op.eval [Bool.false, Bool.true] = Bool.true then x8 ||| x9 else x8 &&& x9])                 x2 x1.gates).getD             x3 (0 : ℕ)).testBit         x4 =       (x1.wires (List.map (fun (x6 : ℕ) => x6.testBit x4) x2)).getD x3 Bool.false :=
  fun x1 x2 x3 x4 h => PEqualNP.Outside.L_meta_8343.main x1 x2 x3 x4 h
