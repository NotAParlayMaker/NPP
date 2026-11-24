import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_1920_733
    (hBits : let tab : List Gate → BitVec 512 := fun gs =>
      (gs.foldl (fun ws g =>
        let a := ws.getD (g.inputs.getD 0 24) 0
        let b := ws.getD (g.inputs.getD 1 24) 0
        ws ++ [if g.inputs.length = 1 then ~~~a
          else bif g.op.eval [false, true] then a ||| b
          else a &&& b])
        ((List.range 9).map fun j =>
          (BitVec.ofBoolListLE ((List.range 512).map fun k => k.testBit j)).setWidth 512)).getD 23 0;

      ∀ (x1 : List Gate), (∀ (x4 : Fin x1.length), (∃ (x5 : ℕ) (x6 : ℕ), x5 ≤ x6 ∧ x6 ≤ (9 : ℕ) + ↑x4 ∧ (x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate })) ∨ ∃ x5 ≤ (9 : ℕ) + ↑x4, x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }) → ∀ i : Fin 512,
      (tab x1).getLsbD i.val =
        (Circuit.mk x1 23).eval (List.ofFn fun j : Fin 9 => (BitVec.ofNat 9 i.val).getLsbD j.val))
    (hTable : ∀ i : Fin 512,
      (BitVec.ofNat 512 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8).getLsbD i.val =
        (fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) (fun j => (BitVec.ofNat 9 i.val).getLsbD j.val))
    (hBound : let tab : List Gate → BitVec 512 := fun gs =>
      (gs.foldl (fun ws g =>
        let a := ws.getD (g.inputs.getD 0 24) 0
        let b := ws.getD (g.inputs.getD 1 24) 0
        ws ++ [if g.inputs.length = 1 then ~~~a
          else bif g.op.eval [false, true] then a ||| b
          else a &&& b])
        ((List.range 9).map fun j =>
          (BitVec.ofBoolListLE ((List.range 512).map fun k => k.testBit j)).setWidth 512)).getD 23 0;

      ∀ (x1 : List Gate), x1.length = 15 → x1.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(4 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } →
      (∀ (x4 : Fin x1.length), (∃ (x5 : ℕ) (x6 : ℕ), x5 ≤ x6 ∧ x6 ≤ (9 : ℕ) + ↑x4 ∧ (x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate })) ∨ ∃ x5 ≤ (9 : ℕ) + ↑x4, x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }) → tab x1 ≠ BitVec.ofNat 512 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate), x1.length = (15 : ℕ) → x1.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(4 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x4 : Fin x1.length), (∃ (x5 : ℕ) (x6 : ℕ), x5 ≤ x6 ∧ x6 ≤ (9 : ℕ) + ↑x4 ∧ (x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate })) ∨ ∃ x5 ≤ (9 : ℕ) + ↑x4, x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }) → ∃ (x5 : Fin (9 : ℕ) → Bool), { gates := x1, output := (23 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x5) ≠ (fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) x5 := by
  intro gs hLen hFirst hGates
  by_contra! hAll
  apply hBound gs hLen hFirst hGates
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (hBits gs hGates ⟨i, hi⟩).trans
    ((hAll (fun j => (BitVec.ofNat 9 i).getLsbD j.val)).trans (hTable ⟨i, hi⟩).symm)
