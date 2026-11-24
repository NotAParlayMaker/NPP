import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2940_73
    (normalize : ∀ C : BinaryCircuit, C.size ≤ 13 →
      (∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) →
      ∃ D : BinaryCircuit, D.size = 13 ∧ D.output = 23 ∧
        (∀ j g, D.gates[j]? = some g → g.left ≤ g.right ∧ g.right < 11+j ∧
          ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) ∧
        (∀ w : List Bool, w.length = 11 → w.getD 10 false = false → D.eval w = C.eval w))
    (reject : ∀ (D : BinaryCircuit) (p : Bool), D.size = 13 → D.output = 23 →
      (∀ j g, D.gates[j]? = some g → g.left ≤ g.right ∧ g.right < 11+j ∧
        ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) →
      ∃ x : Fin 9 → Bool, (D.eval (List.ofFn x ++ [x 0 || x 4,false]) != p) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C p ops computes
  by_contra small
  obtain ⟨D,size,out,shape,replay⟩ := normalize C (by omega) ops
  obtain ⟨x,hx⟩ := reject D p size out shape
  apply hx
  have hlen : (List.ofFn x ++ [x 0 || x 4,false]).length = 11 := by simp
  have hzero : (List.ofFn x ++ [x 0 || x 4,false]).getD 10 false = false := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_right]
  rw [replay _ hlen hzero]
  exact computes x
