import Mathlib
import PEqualNP.Defs

-- The normalization premise is from Hanziwww, PR #7099.
-- Four second ORs commute to a first OR with an established lower bound.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_3348_67
    (prune : let feed := fun (m : ℕ) (x : Fin 9 → Bool) => List.ofFn x ++ [x 4 || x 6,(List.finRange 9).any (fun i => m.testBit i.val && x i)]
    let f := fun x : Fin 9 → Bool => (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64)
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 15 →
    (∀ x, C.eval (List.ofFn x) = f x) →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
    C.gates[1]?.map (fun g => g.op) = some PEqualNP.CircuitLowerBounds.GateOp.or →
    ∃ (m : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), m ∈ ([3, 5, 6, 9, 10, 17, 18, 20, 36, 81, 84, 129, 132, 144, 208] : List ℕ) ∧
      PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ 13 ∧ (∀ x, D.eval (feed m x) = f x) ∧
      ∀ j < D.gates.length, ∀ e ∈ ([1, 5, 12, 23, 38, 58] : List ℕ), ∃ x : Fin 9 → Bool,
        (D.wires (feed m x)).getD (11+j) false ≠ (x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (commute : let feed := fun (m : ℕ) (x : Fin 9 → Bool) => List.ofFn x ++ [x 4 || x 6,(List.finRange 9).any (fun i => m.testBit i.val && x i)]
    ∀ (m : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), m ∈ ([3, 6, 17, 132] : List ℕ) →
    PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
    ∃ x : Fin 9 → Bool, D.eval (feed m x) ≠ (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64))
    (search : let feed := fun (m : ℕ) (x : Fin 9 → Bool) => List.ofFn x ++ [x 4 || x 6,(List.finRange 9).any (fun i => m.testBit i.val && x i)]
    ∀ (m : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), m ∈ ([5, 9, 10, 18, 20, 36, 81, 84, 129, 144, 208] : List ℕ) →
    PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 → (∀ j < D.gates.length, ∀ e ∈ ([1, 5, 12, 23, 38, 58] : List ℕ), ∃ x : Fin 9 → Bool,
        (D.wires (feed m x)).getD (11+j) false ≠ (x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) →
    ∃ x : Fin 9 → Bool, D.eval (feed m x) ≠ (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (16 : ℕ) ≤ x1.size := by
  intro C hfan first hfun second
  by_contra! small
  have truth : ∀ x : Fin 9 → Bool, (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64) := by decide
  have computes (x : Fin 9 → Bool) : C.eval (List.ofFn x) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64) := by
    change PEqualNP.MetaComplexity.circuitFun 9 C x = _
    rw [hfun]
    exact truth x
  obtain ⟨m,D,hm,hD,hs,eval,absent⟩ := prune C hfan (by omega) computes first second
  have split : m ∈ ([3,6,17,132] : List Nat) ∨ m ∈ ([5,9,10,18,20,36,81,84,129,144,208] : List Nat) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm ⊢
    tauto
  rcases split with done | rest
  · obtain ⟨x,hx⟩ := commute m D done hD hs
    exact hx (eval x)
  obtain ⟨x,hx⟩ := search m D rest hD hs absent
  exact hx (eval x)
