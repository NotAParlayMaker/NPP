import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A cut of L-meta-4340 by its first gate OR(x_a, x_b), one pair per orbit of the 12 symmetries.
-- Each child is the unrestricted first-gate bound: a circuit whose wire 9 is OR(x_a, x_b) and
-- which computes the edge function has at least 16 gates. For (0,1), (0,2) and (0,4) these are
-- the statements of the checked L-meta-1673, L-meta-1674 and L-meta-1676; the fourth child joins
-- (0,3), (0,6) and (4,6), the statements of L-meta-1675, L-meta-1677 and the checked L-meta-1678.
-- One file cannot hold the six proofs together: each takes 200 KB or more, against a 512 KiB cap.
-- The step follows by prepending the gate OR(x_a, x_b) to a suffix of at most 14 gates; its
-- condition on the gates that read only inputs is not needed.
theorem PEqualNP.Outside.R_meta_4340_16
    (or01 : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size)
    (or02 : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size)
    (or04 : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size)
    (orRest : ∀ p ∈ ([(0,3),(0,6),(4,6)] : List (Fin 9 × Fin 9)), ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y p.1 || y p.2)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size) :
    ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x7 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x7 ++ [x7 x1.1 || x7 x1.2]) ≠ (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7 := by
  intro p hp D legal small _
  by_contra! computes
  -- Prepend the gate OR(x_p1, x_p2) to D: a circuit on the nine inputs with one gate more,
  -- whose wire 9 is that OR and whose later wires are those of D.
  let C : Circuit := ⟨⟨.or, [p.1, p.2]⟩ :: D.gates, D.output⟩
  have input (y : Fin 9 → Bool) (i : Fin 9) : (List.ofFn y).getD i false = y i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have shift (y : Fin 9 → Bool) :
      C.wires (List.ofFn y) = D.wires (List.ofFn y ++ [y p.1 || y p.2]) := by
    change D.wires (List.ofFn y ++
      [(List.ofFn y).getD p.1 false || ((List.ofFn y).getD p.2 false || false)]) = _
    rw [input, input, Bool.or_false]
  -- Gates only append wires, so wire 9 keeps the value of the prepended gate.
  have extend : ∀ (gs : List Gate) (w : List Bool), ∃ t, (Circuit.mk gs 0).wires w = w ++ t := by
    intro gs
    induction gs with
    | nil => exact fun w => ⟨[], (List.append_nil w).symm⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      exact ⟨_, ht.trans (List.append_assoc _ _ _)⟩
  have wire9 (y : Fin 9 → Bool) : (C.wires (List.ofFn y)).getD 9 false = (y p.1 || y p.2) := by
    obtain ⟨t, ht⟩ := extend D.gates (List.ofFn y ++ [y p.1 || y p.2])
    rw [shift, show D.wires _ = _ from ht, List.append_assoc,
      List.getD_append_right _ _ _ _ (by simp)]
    simp
  have legalC : FanInTwo C := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨by simp, by simp⟩
    · exact legal g hg
  have computesC : circuitFun 9 C = _ := funext fun x =>
    (congrArg (fun w => w.getD D.output false) (shift x)).trans (computes x)
  -- The child of the pair needs 16 gates, but C has at most 15.
  have lower : 16 ≤ C.size := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact or01 C legalC wire9 computesC
    · exact or02 C legalC wire9 computesC
    · exact orRest _ (by simp) C legalC wire9 computesC
    · exact or04 C legalC wire9 computesC
    · exact orRest _ (by simp) C legalC wire9 computesC
    · exact orRest _ (by simp) C legalC wire9 computesC
  have : C.size = D.size + 1 := rfl
  omega
