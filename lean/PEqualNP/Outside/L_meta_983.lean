import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_983_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def c0 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

def c1 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

def c2 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

def c3 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

def c4 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

def c5 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

def c6 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

def c7 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

def c8 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

def c9 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

def c10 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

def c11 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

def c12 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

def c13 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

def c14 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

def c15 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

def c16 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

def c17 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

def c18 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

def c19 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

def c20 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

def c21 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

def c22 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [12, 6]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

def c23 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

def c24 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

def c25 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

def c26 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

def c27 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

def c28 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

def c29 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [13, 5]⟩, ⟨GateOp.and, [6, 14]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [16, 12]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

def c30 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [5, 14]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [16, 13]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

theorem mk (n s : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hM : Monotone2 C) (hS : C.size ≤ s)
    (hE : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x :=
  ⟨C, hM, hS, hE⟩

set_option maxRecDepth 100000 in
theorem t0 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x := by
  refine mk 6 10 _ c0 ?_ (by decide) (by decide)
  simp [Monotone2, c0]

set_option maxRecDepth 100000 in
theorem t1 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine mk 7 10 _ c1 ?_ (by decide) (by decide)
  simp [Monotone2, c1]

set_option maxRecDepth 100000 in
theorem t2 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x := by
  refine mk 7 10 _ c2 ?_ (by decide) (by decide)
  simp [Monotone2, c2]

set_option maxRecDepth 100000 in
theorem t3 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x := by
  refine mk 7 10 _ c3 ?_ (by decide) (by decide)
  simp [Monotone2, c3]

set_option maxRecDepth 100000 in
theorem t4 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x := by
  refine mk 7 10 _ c4 ?_ (by decide) (by decide)
  simp [Monotone2, c4]

set_option maxRecDepth 100000 in
theorem t5 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x := by
  refine mk 7 10 _ c5 ?_ (by decide) (by decide)
  simp [Monotone2, c5]

set_option maxRecDepth 100000 in
theorem t6 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine mk 7 10 _ c6 ?_ (by decide) (by decide)
  simp [Monotone2, c6]

set_option maxRecDepth 100000 in
theorem t7 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x := by
  refine mk 7 10 _ c7 ?_ (by decide) (by decide)
  simp [Monotone2, c7]

set_option maxRecDepth 100000 in
theorem t8 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine mk 7 10 _ c8 ?_ (by decide) (by decide)
  simp [Monotone2, c8]

set_option maxRecDepth 100000 in
theorem t9 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x := by
  refine mk 7 10 _ c9 ?_ (by decide) (by decide)
  simp [Monotone2, c9]

set_option maxRecDepth 100000 in
theorem t10 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x := by
  refine mk 7 10 _ c10 ?_ (by decide) (by decide)
  simp [Monotone2, c10]

set_option maxRecDepth 100000 in
theorem t11 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine mk 7 11 _ c11 ?_ (by decide) (by decide)
  simp [Monotone2, c11]

set_option maxRecDepth 100000 in
theorem t12 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x := by
  refine mk 7 10 _ c12 ?_ (by decide) (by decide)
  simp [Monotone2, c12]

set_option maxRecDepth 100000 in
theorem t13 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x := by
  refine mk 7 11 _ c13 ?_ (by decide) (by decide)
  simp [Monotone2, c13]

set_option maxRecDepth 100000 in
theorem t14 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x := by
  refine mk 7 10 _ c14 ?_ (by decide) (by decide)
  simp [Monotone2, c14]

set_option maxRecDepth 100000 in
theorem t15 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine mk 7 11 _ c15 ?_ (by decide) (by decide)
  simp [Monotone2, c15]

set_option maxRecDepth 100000 in
theorem t16 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine mk 7 10 _ c16 ?_ (by decide) (by decide)
  simp [Monotone2, c16]

set_option maxRecDepth 100000 in
theorem t17 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine mk 7 11 _ c17 ?_ (by decide) (by decide)
  simp [Monotone2, c17]

set_option maxRecDepth 100000 in
theorem t18 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine mk 7 11 _ c18 ?_ (by decide) (by decide)
  simp [Monotone2, c18]

set_option maxRecDepth 100000 in
theorem t19 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x := by
  refine mk 7 11 _ c19 ?_ (by decide) (by decide)
  simp [Monotone2, c19]

set_option maxRecDepth 100000 in
theorem t20 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x := by
  refine mk 7 11 _ c20 ?_ (by decide) (by decide)
  simp [Monotone2, c20]

set_option maxRecDepth 100000 in
theorem t21 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine mk 7 11 _ c21 ?_ (by decide) (by decide)
  simp [Monotone2, c21]

set_option maxRecDepth 100000 in
theorem t22 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x := by
  refine mk 7 10 _ c22 ?_ (by decide) (by decide)
  simp [Monotone2, c22]

set_option maxRecDepth 100000 in
theorem t23 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine mk 7 11 _ c23 ?_ (by decide) (by decide)
  simp [Monotone2, c23]

set_option maxRecDepth 100000 in
theorem t24 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine mk 7 11 _ c24 ?_ (by decide) (by decide)
  simp [Monotone2, c24]

set_option maxRecDepth 100000 in
theorem t25 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x := by
  refine mk 7 11 _ c25 ?_ (by decide) (by decide)
  simp [Monotone2, c25]

set_option maxRecDepth 100000 in
theorem t26 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine mk 7 12 _ c26 ?_ (by decide) (by decide)
  simp [Monotone2, c26]

set_option maxRecDepth 100000 in
theorem t27 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine mk 7 12 _ c27 ?_ (by decide) (by decide)
  simp [Monotone2, c27]

set_option maxRecDepth 100000 in
theorem t28 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine mk 7 12 _ c28 ?_ (by decide) (by decide)
  simp [Monotone2, c28]

set_option maxRecDepth 100000 in
theorem t29 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine mk 7 12 _ c29 ?_ (by decide) (by decide)
  simp [Monotone2, c29]

set_option maxRecDepth 100000 in
theorem t30 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x := by
  refine mk 7 12 _ c30 ?_ (by decide) (by decide)
  simp [Monotone2, c30]

end PEqualNP.Outside.L_meta_983_aux

theorem PEqualNP.Outside.L_meta_983 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) := by
  exact ⟨
    PEqualNP.Outside.L_meta_983_aux.t0,
    PEqualNP.Outside.L_meta_983_aux.t1,
    PEqualNP.Outside.L_meta_983_aux.t2,
    PEqualNP.Outside.L_meta_983_aux.t3,
    PEqualNP.Outside.L_meta_983_aux.t4,
    PEqualNP.Outside.L_meta_983_aux.t5,
    PEqualNP.Outside.L_meta_983_aux.t6,
    PEqualNP.Outside.L_meta_983_aux.t7,
    PEqualNP.Outside.L_meta_983_aux.t8,
    PEqualNP.Outside.L_meta_983_aux.t9,
    PEqualNP.Outside.L_meta_983_aux.t10,
    PEqualNP.Outside.L_meta_983_aux.t11,
    PEqualNP.Outside.L_meta_983_aux.t12,
    PEqualNP.Outside.L_meta_983_aux.t13,
    PEqualNP.Outside.L_meta_983_aux.t14,
    PEqualNP.Outside.L_meta_983_aux.t15,
    PEqualNP.Outside.L_meta_983_aux.t16,
    PEqualNP.Outside.L_meta_983_aux.t17,
    PEqualNP.Outside.L_meta_983_aux.t18,
    PEqualNP.Outside.L_meta_983_aux.t19,
    PEqualNP.Outside.L_meta_983_aux.t20,
    PEqualNP.Outside.L_meta_983_aux.t21,
    PEqualNP.Outside.L_meta_983_aux.t22,
    PEqualNP.Outside.L_meta_983_aux.t23,
    PEqualNP.Outside.L_meta_983_aux.t24,
    PEqualNP.Outside.L_meta_983_aux.t25,
    PEqualNP.Outside.L_meta_983_aux.t26,
    PEqualNP.Outside.L_meta_983_aux.t27,
    PEqualNP.Outside.L_meta_983_aux.t28,
    PEqualNP.Outside.L_meta_983_aux.t29,
    PEqualNP.Outside.L_meta_983_aux.t30
  ⟩
