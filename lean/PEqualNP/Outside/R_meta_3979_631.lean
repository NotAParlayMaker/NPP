import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Charge the supplied conjunction to the known binary-gate lower bound.
-- Split off the thirteen-gate suffix with one remaining inverter.
-- The binary-only branch uses the extremal labelled assignments in each fixed-x_0 subcube.
theorem PEqualNP.Outside.R_meta_3979_631
    (binary : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5)) →
      13 ≤ C.gates.countP (fun g => g.op.eval [true]))
    (zeroCase : ∀ a ∈ ([1,2,3,4,6] : List (Fin 9)), ∀ C : Circuit,
      FanInTwo C → 12 ≤ C.size → C.size ≤ 13 → (∀ i j : Fin C.gates.length,
       ((C.gates.get i).inputs[0]? = some 0 ∨ (C.gates.get i).inputs[0]? = some 9 ∨
        (C.gates.get i).op ≠ .not ∧ (0 ∈ (C.gates.get i).inputs ∨ 9 ∈ (C.gates.get i).inputs)) →
       ((C.gates.get j).inputs[0]? = some 0 ∨ (C.gates.get j).inputs[0]? = some 9 ∨
        (C.gates.get j).op ≠ .not ∧ (0 ∈ (C.gates.get j).inputs ∨ 9 ∈ (C.gates.get j).inputs)) → i=j) →
      C.gates.countP (fun g => !(g.op.eval [true])) = 0 →
      ∃ m : Fin 512, Nat.testBit 0x40002000000000000000300000001001003200000000000010300000000010000043000100100000000240004040201023048 m.val = true ∧
        let x : Fin 9 → Bool := fun i => m.val.testBit i.val
        C.eval (List.ofFn x ++ [!x 0, x a && !x 0]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5))
    (oneCase : ∀ a ∈ ([1,2,3,4,6] : List (Fin 9)), ∀ C : Circuit,
      FanInTwo C → C.size = 13 → (∀ i j : Fin C.gates.length,
       ((C.gates.get i).inputs[0]? = some 0 ∨ (C.gates.get i).inputs[0]? = some 9 ∨
        (C.gates.get i).op ≠ .not ∧ (0 ∈ (C.gates.get i).inputs ∨ 9 ∈ (C.gates.get i).inputs)) →
       ((C.gates.get j).inputs[0]? = some 0 ∨ (C.gates.get j).inputs[0]? = some 9 ∨
        (C.gates.get j).op ≠ .not ∧ (0 ∈ (C.gates.get j).inputs ∨ 9 ∈ (C.gates.get j).inputs)) → i=j) →
      C.gates.countP (fun g => !(g.op.eval [true])) = 1 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x a && !x 0]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5))
    :
    ∀ x1 ∈ [((1 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         (∀ (x6 x7 : Fin x3.gates.length), (x3.gates.get x6).inputs[(0 : ℕ)]? = Option.some (0 : ℕ) ∨ (x3.gates.get x6).inputs[(0 : ℕ)]? = Option.some (9 : ℕ) ∨ (x3.gates.get x6).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((0 : ℕ) ∈ (x3.gates.get x6).inputs ∨ (9 : ℕ) ∈ (x3.gates.get x6).inputs) → (x3.gates.get x7).inputs[(0 : ℕ)]? = Option.some (0 : ℕ) ∨ (x3.gates.get x7).inputs[(0 : ℕ)]? = Option.some (9 : ℕ) ∨ (x3.gates.get x7).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((0 : ℕ) ∈ (x3.gates.get x7).inputs ∨ (9 : ℕ) ∈ (x3.gates.get x7).inputs) → x6 = x7) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];             have x9 : Fin (12 : ℕ) → Bool := fun (x9 : Fin (12 : ℕ)) => if x9 = (11 : Fin (12 : ℕ)) then Bool.true else x8.getD (↑x9) Bool.false;             x3.eval (x8 ++ [x9 x1.1 && x9 x1.2]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  let edgeF (x : Fin 9 → Bool) := (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5)
  let boundary (a : Fin 9) (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0, x a && !x 0]
  have bridge (C : Circuit) (a : Fin 9)
      (h : ∃ x : Fin 9 → Bool, C.eval (boundary a x) ≠ edgeF x) :
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!x 0]
        let z (v : Fin 12) := if v=11 then true else w.getD v.val false
        C.eval (w ++ [z (Fin.castAdd 3 a) && z 9]) ≠ edgeF x := by
    obtain ⟨x,hx⟩ := h
    refine ⟨x,?_⟩
    have low : (List.ofFn x ++ [!x 0]).getD a.val false = x a := by
      rw [List.getD_append _ _ _ _ (by simp [a.isLt]),
        List.getD_eq_getElem _ _ (by simp [a.isLt]),List.getElem_ofFn]
    have high : (List.ofFn x ++ [!x 0]).getD 9 false = !x 0 := by
      simp
    have no : Fin.castAdd 3 a ≠ (11 : Fin 12) := by
      intro he
      have val := congrArg Fin.val he
      change a.val=11 at val
      have al := a.isLt
      omega
    have zNine : (9 : Fin 12) ≠ 11 := by decide
    change C.eval ((List.ofFn x ++ [!x 0]) ++
      [(if Fin.castAdd 3 a = 11 then true else (List.ofFn x ++ [!x 0]).getD a.val false) &&
       (if (9 : Fin 12) = 11 then true else (List.ofFn x ++ [!x 0]).getD 9 false)]) ≠ edgeF x
    rw [ite_eq_right no,ite_eq_right zNine,low,high,List.append_assoc]
    exact hx
  have core (a : Fin 9) (ha : a ∈ ([1,2,3,4,6] : List (Fin 9)))
      (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 13)
      (unique : (∀ i j : Fin C.gates.length,
       ((C.gates.get i).inputs[0]? = some 0 ∨ (C.gates.get i).inputs[0]? = some 9 ∨
        (C.gates.get i).op ≠ .not ∧ (0 ∈ (C.gates.get i).inputs ∨ 9 ∈ (C.gates.get i).inputs)) →
       ((C.gates.get j).inputs[0]? = some 0 ∨ (C.gates.get j).inputs[0]? = some 9 ∨
        (C.gates.get j).op ≠ .not ∧ (0 ∈ (C.gates.get j).inputs ∨ 9 ∈ (C.gates.get j).inputs)) → i=j)) :
      ∃ x : Fin 9 → Bool, C.eval (boundary a x) ≠ edgeF x := by
    by_contra! correct
    let D : Circuit := ⟨⟨.not,[0]⟩ :: ⟨.and,[a.val,9]⟩ :: C.gates,C.output⟩
    have model : FanInTwo D := by
      intro g hg
      simp only [D,List.mem_cons] at hg
      rcases hg with rfl | rfl | h
      · simp
      · simp
      · exact fan g h
    have semantics (x : Fin 9 → Bool) : D.eval (List.ofFn x) = edgeF x := by
      have read (k : Fin 9) : (List.ofFn x).getD k.val false = x k := by
        rw [List.getD_eq_getElem _ _ (by simp [k.isLt]),List.getElem_ofFn]
      have readA (b : Bool) : (List.ofFn x ++ [b]).getD a.val false = x a := by
        rw [List.getD_append _ _ _ _ (by simp [a.isLt]),read]
      have read9 (b : Bool) : (List.ofFn x ++ [b]).getD 9 false = b := by
        simp
      change C.eval ((List.ofFn x ++ [!(List.ofFn x).getD 0 false]) ++
        [GateOp.and.eval [
           (List.ofFn x ++ [!(List.ofFn x).getD 0 false]).getD a.val false,
           (List.ofFn x ++ [!(List.ofFn x).getD 0 false]).getD 9 false]]) = edgeF x
      rw [show (List.ofFn x).getD 0 false = x 0 from read 0,readA,read9,List.append_assoc]
      simpa only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,List.singleton_append,boundary] using correct x
    have necessary := binary D model semantics
    let b (g : Gate) := g.op.eval [true]
    have c0 (G : List Gate) : List.countP b (⟨.not,[0]⟩ :: G) = List.countP b G :=
      List.countP_cons_of_neg (p := b) (a := ⟨.not,[0]⟩) (by change ¬ false = true; decide)
    have c1 : List.countP b (⟨.and,[a.val,9]⟩ :: C.gates) = List.countP b C.gates + 1 :=
      List.countP_cons_of_pos (p := b) (a := ⟨.and,[a.val,9]⟩) rfl
    change 13 ≤ List.countP b (⟨.not,[0]⟩ :: ⟨.and,[a.val,9]⟩ :: C.gates) at necessary
    rw [c0,c1] at necessary
    have split : C.gates.countP (fun g => g.op.eval [true]) +
        C.gates.countP (fun g => !(g.op.eval [true])) = C.size := by
      simpa only [Circuit.size,decide_not,Bool.decide_coe] using
        (List.length_eq_countP_add_countP (fun g : Gate => g.op.eval [true]) (l := C.gates)).symm
    change 13 ≤ C.gates.countP (fun g => g.op.eval [true]) + 1 at necessary
    by_cases no : C.gates.countP (fun g => !(g.op.eval [true])) = 0
    · obtain ⟨m,_,hx⟩ := zeroCase a ha C fan (by omega) size unique no
      exact hx (correct (fun i => m.val.testBit i.val))
    · have one : C.gates.countP (fun g => !(g.op.eval [true])) = 1 := by omega
      obtain ⟨x,hx⟩ := oneCase a ha C fan (by omega) unique one
      exact hx (correct x)
  intro pair member C fan size unique
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact bridge C 1 (core 1 (by decide) C fan size unique)
  · exact bridge C 2 (core 2 (by decide) C fan size unique)
  · exact bridge C 3 (core 3 (by decide) C fan size unique)
  · exact bridge C 4 (core 4 (by decide) C fan size unique)
  · exact bridge C 6 (core 6 (by decide) C fan size unique)
