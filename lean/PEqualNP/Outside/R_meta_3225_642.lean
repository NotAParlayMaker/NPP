import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3225_642
  (lower : ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ))) (12 : ℕ))
  (compress : ∀ (C : Circuit) (a b : ℕ),
    let v := fun (b : Bool) (x : ℕ → Bool) =>
      [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
    let col := fun (j : ℕ) (y : ℕ → Bool) =>
      (C.wires (v false y)).getD j false
    FanInTwo C → a < b → b < C.size →
    (∃ u < 10 + a, col (10 + a) = col u) → (∃ u < 10 + b, col (10 + b) = col u) →
    ∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
      ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = C.eval (v false (fun i => x (Fin.ofNat 8 i))))
  (collision : let v := fun (b : Bool) (x : ℕ → Bool) =>
      [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
    let F := fun (y : ℕ → Bool) =>
      [1, 10, 19, 4, 13, 22, 31, 38, 47, 60].any (fun k : ℕ => y (k / 8) && y (k % 8))
    ∀ C : Circuit, FanInTwo C → C.size = 14 →
    C.gates.countP (fun g => (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).any
      (fun j => decide (j = 6))) ≤ 1 →
    (∃ g ∈ C.gates, g.op = GateOp.or ∧ 6 ∈ g.inputs) →
    (∀ (y : ℕ → Bool) (b : Bool), C.eval (v b y) = if b then F y || y 0 || y 3 else F y) →
    let col := fun (j : ℕ) (y : ℕ → Bool) =>
      (C.wires (v false y)).getD j false
    ∃ a b : ℕ, a < b ∧ b < C.size ∧ (∃ u < 10 + a, col (10 + a) = col u) ∧ (∃ u < 10 + b, col (10 + b) = col u)) :
  have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x8 ∈ x4.gates, x8.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x8.inputs) → (∀ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x9) = x3 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x10) ≠ (x3 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  intro read pins graph C fan size count hasOr low
  by_contra failed
  have high : ∀ x, C.eval (pins true x) = (graph x || x 0 || x 3) := by
    intro x
    by_contra mismatch
    exact failed ⟨x, mismatch⟩
  obtain ⟨a, b, order, within, ha, hb⟩ := collision C fan size count hasOr (by
    intro y m
    let x : Fin 8 → Bool := fun j => y j.val
    have graphEq : graph x =
        [1, 10, 19, 4, 13, 22, 31, 38, 47, 60].any
          (fun k : ℕ => y (k / 8) && y (k % 8)) := by
      change (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 ||
        y 1 && y 5 || y 2 && y 6 || y 3 && y 7 || y 4 && y 6 ||
        y 5 && y 7 || y 7 && y 4) = _
      simp [List.any_cons, Bool.or_assoc]
    cases m
    · exact (low x).trans graphEq
    · exact (high x).trans (congrArg (fun value : Bool => value || y 0 || y 3) graphEq))
  obtain ⟨D, fanD, smaller, agrees⟩ := compress C a b fan order within ha hb
  apply lower
  refine ⟨D, fanD, by omega, ?_⟩
  intro x
  exact (agrees x).trans (low x)
