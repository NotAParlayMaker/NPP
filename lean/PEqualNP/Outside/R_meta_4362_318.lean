import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- With vertex 6 false the function is the ten-edge function of the other eight vertices, after
-- renaming, and the given wire (vertex 0 OR vertex 6) is vertex 0. That function needs 13 gates:
-- bound13 is the statement of the checked L_meta_2537. fixSix: every gate that reads wire 6 goes
-- away, and so does every gate that reads an AND or NOT gate reading wire 6. Two such gates
-- among 14 would leave 12. What remains is oneKilled: only the one reader of wire 6 goes away.
theorem PEqualNP.Outside.R_meta_4362_318
    (bound13 : ∀ (s : ℕ), HasCircuitSize 9 (fun (x : Fin 9 → Bool) => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) s → 13 ≤ s)
    (fixSix : ∀ (C : Circuit), FanInTwo C →
      (∀ y : Fin 9 → Bool, C.eval (List.ofFn (fun i : Fin 9 => if i = 6 then false else y (([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD i.val 0)) ++ [y 1]) = true) ∨
      ∃ E : Circuit, FanInTwo E ∧
        E.size + List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == 6 || (Nat.ble (10 : ℕ) k && (C.gates[k - 10]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains 6 && !h.op.eval [Bool.true, Bool.false])))) C.gates ≤ C.size ∧
        ∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (fun i : Fin 9 => if i = 6 then false else y (([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD i.val 0)) ++ [y 1]))
    (oneKilled : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size = (14 : ℕ) → x1.output = (23 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => (if x5.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x5.inputs else x5.inputs).any fun (x6 : ℕ) => Decidable.decide (x6 = (6 : ℕ))) x1.gates = (1 : ℕ) → List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == 6 || (Nat.ble (10 : ℕ) k && (x1.gates[k - 10]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains 6 && !h.op.eval [Bool.true, Bool.false])))) x1.gates ≤ 1 → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ))]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size = (14 : ℕ) → x1.output = (23 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => (if x5.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x5.inputs else x5.inputs).any fun (x6 : ℕ) => Decidable.decide (x6 = (6 : ℕ))) x1.gates = (1 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ))]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C hmono hsize hout hcnt
  by_contra hne
  have hall : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 || x 6]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    intro x
    by_contra hx
    exact hne ⟨x, hx⟩
  have hfan : FanInTwo C := by
    intro g hg
    refine ⟨?_, (hmono g hg).2⟩
    rcases (hmono g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  by_cases hk : List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == 6 || (Nat.ble (10 : ℕ) k && (C.gates[k - 10]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains 6 && !h.op.eval [Bool.true, Bool.false])))) C.gates ≤ 1
  · exact hne (oneKilled C hmono hsize hout hcnt hk)
  · rcases fixSix C hfan with hT | ⟨E, hE, hEs, hEf⟩
    · have h1 := hT (fun _ => false)
      have e : (List.ofFn (fun i : Fin 9 => if i = 6 then false else (fun _ : Fin 9 => false) (([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD i.val 0)) ++ [(fun _ : Fin 9 => false) 1])
          = List.ofFn (fun _ : Fin 9 => false) ++ [(fun _ : Fin 9 => false) 0 || (fun _ : Fin 9 => false) 6] := rfl
      rw [e, hall (fun _ => false)] at h1
      exact absurd h1 (by decide)
    · have h13 := bound13 E.size ⟨E, hE, le_rfl, fun y => by
        rw [hEf y]
        have e : List.ofFn (fun i : Fin 9 => if i = 6 then false else y (([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD i.val 0)) ++ [(fun i : Fin 9 => if i = 6 then false else y (([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD i.val 0)) 0 || (fun i : Fin 9 => if i = 6 then false else y (([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD i.val 0)) 6] = (List.ofFn (fun i : Fin 9 => if i = 6 then false else y (([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD i.val 0)) ++ [y 1]) := by
          show _ ++ [y 1 || false] = _ ++ [y 1]
          rw [Bool.or_false]
        rw [← e, hall (fun i : Fin 9 => if i = 6 then false else y (([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD i.val 0))]
        have taut : ∀ b0 b1 b2 b3 b5 b6 b7 b8 : Bool,
            (b1 && b0 || b0 && b5 || b5 && b8 || b8 && b6 || b6 && b1 || b1 && b2 || b0 && false || b5 && b7 || b8 && b3 || b2 && b7 || false && b3 || b3 && b2)
            = (b0 && b1 || b1 && b2 || b2 && b3 || b0 && b5 || b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by decide
        exact taut (y 0) (y 1) (y 2) (y 3) (y 5) (y 6) (y 7) (y 8)⟩
      omega
