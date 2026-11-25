import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9284

/-! The graph is circulant: left vertex u is joined to right vertices u, u + 1, u + 2 (mod 6).
Inputs 0..5 are the left wires x0..x5, inputs 6..11 the right wires y0..y5.
Three pair ORs W0 = y0|y1, W1 = y2|y3, W2 = y4|y5, then six triple ORs
T_u = y_u | y_(u+1) | y_(u+2) built from one pair and one wire, six ANDs x_u & T_u,
and five ORs joining them: 3 + 6 + 6 + 5 = 20 gates. -/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def okop : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => false
  | GateOp.mod _ => false
  | GateOp.maj => false

theorem mono2_of (C : Circuit)
    (h : C.gates.all (fun g => okop g.op && decide (g.inputs.length ≤ 2)) = true) :
    Monotone2 C := by
  intro g hg
  have h2 := List.all_eq_true.mp h g hg
  rcases g with ⟨op, ins⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  refine ⟨?_, h2.2⟩
  have h3 := h2.1
  cases op <;> simp [okop] at h3 ⊢

def circ : Circuit :=
  ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [12, 8]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.or, [13, 10]⟩,
    ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.or, [14, 6]⟩, ⟨GateOp.or, [11, 12]⟩,
    ⟨GateOp.and, [0, 15]⟩, ⟨GateOp.and, [1, 16]⟩, ⟨GateOp.and, [2, 17]⟩,
    ⟨GateOp.and, [3, 18]⟩, ⟨GateOp.and, [4, 19]⟩, ⟨GateOp.and, [5, 20]⟩,
    ⟨GateOp.or, [21, 22]⟩, ⟨GateOp.or, [27, 23]⟩, ⟨GateOp.or, [28, 24]⟩,
    ⟨GateOp.or, [29, 25]⟩, ⟨GateOp.or, [30, 26]⟩], 31⟩

theorem circ_rep : PEqualNP.Represents.Represents
    (fun u v : Fin 6 => (38417843079 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide

theorem main_aux : PEqualNP.Represents.RepSizeAtMost
    (fun u v : Fin 6 => (38417843079 : ℕ).testBit (6 * u.val + v.val)) 20 :=
  ⟨circ, mono2_of circ (by decide), by decide, circ_rep⟩

end PEqualNP.Outside.L_meta_9284

theorem PEqualNP.Outside.L_meta_9284 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (38417843079 : ℕ).testBit (6 * u.val + v.val)) 20 :=
  PEqualNP.Outside.L_meta_9284.main_aux
