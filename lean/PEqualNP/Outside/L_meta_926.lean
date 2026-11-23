import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def opOk : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem opOk_spec (o : GateOp) (h : opOk o = true) : o = GateOp.and ∨ o = GateOp.or := by
  cases o <;> simp_all [opOk]

theorem all_ok (gs : List Gate)
    (h : gs.all (fun g => opOk g.op && g.inputs.length == 2) = true) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨opOk_spec _ h1.1, h1.2⟩

theorem mk (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) (gs : List Gate) (o : ℕ)
    (h1 : gs.all (fun g => opOk g.op && g.inputs.length == 2) = true) (h2 : gs.length ≤ s)
    (h3 : ∀ x : Fin n → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    HasCircuitSize n f s := by
  refine ⟨⟨gs, o⟩, ?_, h2, h3⟩
  intro g hg
  obtain ⟨h4, h5⟩ := all_ok gs h1 g hg
  refine ⟨?_, by omega⟩
  rcases h4 with h4 | h4 <;> simp [h4]

set_option maxRecDepth 100000 in
theorem c0 : HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 :=
  mk _ _ _ [⟨GateOp.and, [0, 1]⟩] 2 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c1 : HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩] 4 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c2 : HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 :=
  mk _ _ _ [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [3, 5]⟩] 6 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c3 : HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 :=
  mk _ _ _ [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩] 6 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c4 : HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.and, [0, 5]⟩] 6 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c5 : HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [3, 1]⟩, ⟨GateOp.or, [5, 6]⟩] 7 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c6 : HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 :=
  mk _ _ _ [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [4, 7]⟩] 8 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c7 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [6, 7]⟩] 8 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c8 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [0, 7]⟩] 8 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c9 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [4, 1]⟩, ⟨GateOp.or, [7, 8]⟩] 9 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c10 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 :=
  mk _ _ _ [⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [7, 9]⟩] 10 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c11 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 :=
  mk _ _ _ [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [6, 8]⟩] 9 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c12 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 :=
  mk _ _ _ [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [5, 9]⟩] 10 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c13 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 :=
  mk _ _ _ [⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [6, 9]⟩] 10 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c14 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 :=
  mk _ _ _ [⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [7, 10]⟩] 11 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c15 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 :=
  mk _ _ _ [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [8, 10]⟩] 11 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c16 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 :=
  mk _ _ _ [⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [7, 11]⟩] 12 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c17 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 :=
  mk _ _ _ [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [9, 8]⟩] 10 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c18 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩] 10 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c19 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [3, 1]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [10, 9]⟩] 11 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c20 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [7, 9]⟩] 10 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c21 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [0, 9]⟩] 10 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c22 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [5, 1]⟩, ⟨GateOp.or, [9, 10]⟩] 11 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c23 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 :=
  mk _ _ _ [⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [9, 3]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [8, 11]⟩] 12 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c24 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 :=
  mk _ _ _ [⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [7, 10]⟩] 11 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c25 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [4, 1]⟩, ⟨GateOp.and, [5, 2]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩] 12 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c26 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [8, 10]⟩] 11 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c27 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 :=
  mk _ _ _ [⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [9, 11]⟩] 12 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c28 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.and, [4, 2]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [11, 10]⟩] 12 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c29 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 :=
  mk _ _ _ [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [6, 11]⟩] 12 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c30 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 :=
  mk _ _ _ [⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [7, 11]⟩] 12 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c31 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 :=
  mk _ _ _ [⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [9, 3]⟩, ⟨GateOp.or, [10, 4]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [8, 12]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c32 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 :=
  mk _ _ _ [⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [9, 12]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c33 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 :=
  mk _ _ _ [⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [9, 12]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c34 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 :=
  mk _ _ _ [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [9, 12]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c35 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 :=
  mk _ _ _ [⟨GateOp.and, [2, 1]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [10, 12]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c36 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 :=
  mk _ _ _ [⟨GateOp.and, [4, 1]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [10, 12]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c37 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 :=
  mk _ _ _ [⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [11, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c38 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [12, 11]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c39 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 :=
  mk _ _ _ [⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [9, 3]⟩, ⟨GateOp.or, [10, 4]⟩, ⟨GateOp.or, [11, 5]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [8, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c40 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 :=
  mk _ _ _ [⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [9, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c41 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 :=
  mk _ _ _ [⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [11, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c42 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩] 12 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c43 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩] 12 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c44 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [4, 1]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [12, 11]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c45 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [9, 11]⟩] 12 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c46 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.and, [5, 6]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [11, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c47 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 :=
  mk _ _ _ [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 11]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c48 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [3, 1]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c49 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩] 12 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c50 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [6, 1]⟩, ⟨GateOp.or, [11, 12]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c51 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.and, [5, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [9, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c52 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 :=
  mk _ _ _ [⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [9, 3]⟩, ⟨GateOp.or, [10, 4]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [8, 12]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c53 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [5, 1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c54 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [10, 12]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c55 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [10, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c56 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [5, 6]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [12, 3]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [11, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c57 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [10, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c58 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [7, 5]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.and, [3, 0]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c59 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [13, 12]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c60 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.and, [5, 2]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c61 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [9, 12]⟩] 13 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c62 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c63 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [10, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c64 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [12, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c65 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [12, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c66 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [13, 12]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c67 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 :=
  mk _ _ _ [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.or, [10, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [7, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c68 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [9, 3]⟩, ⟨GateOp.or, [10, 4]⟩, ⟨GateOp.or, [11, 5]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [8, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c69 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [3, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.or, [12, 5]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [9, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c70 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 :=
  mk _ _ _ [⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [7, 6]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [9, 13]⟩] 14 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c71 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.or, [12, 4]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [10, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c72 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.or, [12, 4]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [10, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c73 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.or, [12, 4]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [10, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c74 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.or, [12, 4]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [10, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c75 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.or, [12, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c76 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.or, [12, 4]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [10, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c77 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.or, [12, 4]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [10, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c78 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [12, 5]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.or, [11, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c79 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [12, 3]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [11, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c80 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [12, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c81 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [8, 6]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [12, 3]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [11, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c82 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [9, 3]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [12, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c83 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [8, 6]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [12, 3]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [11, 14]⟩] 15 (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem c84 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 :=
  mk _ _ _ [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩] 15 (by decide) (by decide) (by decide)

end PEqualNP.Outside.L_meta_926_aux

open PEqualNP.Outside.L_meta_926_aux in
theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) :=
  ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79, c80, c81, c82, c83, c84⟩
