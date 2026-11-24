import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3977_617
    (trim :
      let reads (g : Gate) := g.inputs[0]? = some 0 ∨ g.inputs[0]? = some 9 ∨
        g.op ≠ .not ∧ (0 ∈ g.inputs ∨ 9 ∈ g.inputs)
      ∀ (C : Circuit) (i : Fin 8) (f : (Fin 8 → Bool) → Bool),
        FanInTwo C →
        (∃ a b : Fin C.gates.length, a ≠ b ∧ reads (C.gates.get a) ∧ reads (C.gates.get b)) →
        (∀ x, C.eval ((false :: List.ofFn x) ++ [true,x i]) = f x) →
        HasCircuitSize 8 f (C.size - 2))
    (lower : ∀ (x1 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x2 : Fin (8 : ℕ) → Bool) => [((0 : Fin (8 : ℕ)), (1 : Fin (8 : ℕ))), ((0 : Fin (8 : ℕ)), (5 : Fin (8 : ℕ))), ((1 : Fin (8 : ℕ)), (2 : Fin (8 : ℕ))), ((1 : Fin (8 : ℕ)), (6 : Fin (8 : ℕ))), ((2 : Fin (8 : ℕ)), (3 : Fin (8 : ℕ))), ((2 : Fin (8 : ℕ)), (7 : Fin (8 : ℕ))), ((4 : Fin (8 : ℕ)), (6 : Fin (8 : ℕ))), ((4 : Fin (8 : ℕ)), (7 : Fin (8 : ℕ))), ((5 : Fin (8 : ℕ)), (7 : Fin (8 : ℕ)))].any fun (x3 : Fin (8 : ℕ) × Fin (8 : ℕ)) => x2 x3.1 && x2 x3.2) x1 → (12 : ℕ) ≤ x1) :
∀ x1 ∈ [((1 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         (∃ (x6 : Fin x3.gates.length) (x7 : Fin x3.gates.length), x6 ≠ x7 ∧ ((x3.gates.get x6).inputs[(0 : ℕ)]? = Option.some (0 : ℕ) ∨ (x3.gates.get x6).inputs[(0 : ℕ)]? = Option.some (9 : ℕ) ∨ (x3.gates.get x6).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((0 : ℕ) ∈ (x3.gates.get x6).inputs ∨ (9 : ℕ) ∈ (x3.gates.get x6).inputs)) ∧ ((x3.gates.get x7).inputs[(0 : ℕ)]? = Option.some (0 : ℕ) ∨ (x3.gates.get x7).inputs[(0 : ℕ)]? = Option.some (9 : ℕ) ∨ (x3.gates.get x7).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((0 : ℕ) ∈ (x3.gates.get x7).inputs ∨ (9 : ℕ) ∈ (x3.gates.get x7).inputs))) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];             have x9 : Fin (12 : ℕ) → Bool := fun (x9 : Fin (12 : ℕ)) => if x9 = (11 : Fin (12 : ℕ)) then Bool.true else x8.getD (↑x9) Bool.false;             x3.eval (x8 ++ [x9 x1.1 && x9 x1.2]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))
 := by
  intro p hp C fan small reads
  classical
  by_contra bad
  have pins : ∀ q : Fin 12 × Fin 12, q ∈ ([(1,9),(2,9),(3,9),(4,9),(6,9)] : List (Fin 12 × Fin 12)) →
      0 < q.1.val ∧ q.1.val ≤ 8 ∧ q.2 = 9 := by
    intro q member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨pos,low,right⟩ := pins p hp
  let i : Fin 8 := ⟨p.1.val-1,by omega⟩
  let f := fun x : Fin 8 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 5) ||
    (x 1 && x 6) || (x 2 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  have restricted (x : Fin 8 → Bool) :
      C.eval ((false :: List.ofFn x) ++ [true,x i]) = f x := by
    let y : Fin 9 → Bool := Fin.cons false x
    let z := List.ofFn y ++ [!y 0]
    let read (q : Fin 12) := if q = 11 then true else z.getD q.val false
    have zero : y 0 = false := rfl
    have list : List.ofFn y = false :: List.ofFn x := List.ofFn_succ
    have zval : z = (false :: List.ofFn x) ++ [true] := by simp only [z,list,zero,Bool.not_false]
    have leftVal : read p.1 = x i := by
      have outside : p.1 ≠ 11 := by intro h; rw [h] at low; omega
      change (if p.1 = 11 then true else z.getD p.1.val false) = _
      rw [ite_eq_right outside,zval,List.getD_append _ _ _ _ (by simp; omega)]
      have e : p.1.val = i.val+1 := by dsimp [i]; omega
      rw [e,List.getD_cons_succ]
      rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
    have rightVal : read p.2 = true := by
      rw [right]
      change (if (9 : Fin 12) = 11 then true else z.getD 9 false) = _
      rw [ite_eq_right (by decide),zval]
      simp [List.getD_eq_getElem?_getD]
    have lhs : z ++ [read p.1 && read p.2] = (false :: List.ofFn x) ++ [true,x i] := by
      rw [leftVal,rightVal,Bool.and_true,zval,List.append_assoc]
      rfl
    have h : C.eval (z ++ [read p.1 && read p.2]) =
        (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
        y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 ||
        y 6 && y 8 || y 8 && y 5) := by
      by_contra no
      exact bad ⟨y,no⟩
    rw [lhs] at h
    have h1 : y 1 = x 0 := rfl
    have h2 : y 2 = x 1 := rfl
    have h3 : y 3 = x 2 := rfl
    have h4 : y 4 = x 3 := rfl
    have h5 : y 5 = x 4 := rfl
    have h6 : y 6 = x 5 := rfl
    have h7 : y 7 = x 6 := rfl
    have h8 : y 8 = x 7 := rfl
    simpa only [f,zero,h1,h2,h3,h4,h5,h6,h7,h8,Bool.false_and,Bool.and_false,
      Bool.false_or,Bool.or_false] using h
  obtain ⟨D,fanD,sizeD,correct⟩ := trim C i f fan reads restricted
  have small' : D.size ≤ 11 := by omega
  have listEval (x : Fin 8 → Bool) :
      f x = ([(0,1),(0,5),(1,2),(1,6),(2,3),(2,7),(4,6),(4,7),(5,7)] :
        List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2) := by
    simp only [f,List.any_cons,List.any_nil,Bool.false_or,Bool.or_assoc,Bool.or_left_comm,
      Bool.or_comm,Bool.and_comm]
  have contradiction := lower 11 ⟨D,fanD,small',fun x => (correct x).trans (listEval x)⟩
  omega
