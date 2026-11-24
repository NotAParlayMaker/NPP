import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1916_713
    (normalize : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ A B : Circuit, Monotone2 A → Monotone2 B →
        (∀ x : Fin 9 → Bool, let w := A.wires (List.ofFn x ++ [x 4 && x 6])
          B.eval (w ++ [!(w.getD A.output false)]) = !(f x)) →
        ∀ x : Fin 9 → Bool, A.eval (List.ofFn x ++ [false]) = f x)
    (lower : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ A : Circuit, A.size ≤ 12 → Monotone2 A →
        ∃ x : Fin 9 → Bool, A.eval (List.ofFn x ++ [false]) ≠ f x)
    (extract : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit, C.size ≤ 13 → FanInTwo C → (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 23) →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 && x 6]) = !(f x)) →
        ∃ A B : Circuit, A.size ≤ 12 ∧ Monotone2 A ∧ Monotone2 B ∧
          ∀ x : Fin 9 → Bool, let w := A.wires (List.ofFn x ++ [x 4 && x 6])
            B.eval (w ++ [!(w.getD A.output false)]) = !(f x)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro gs pins sz fan refs _hlen
  by_contra! all
  cases pins with
  | nil =>
    exact all (fun _ => false) (by change true ≠ false; decide)
  | cons head tail =>
    let C : Circuit := ⟨gs,head.val⟩
    let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    have opposite (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 4 && x 6]) = !(f x) := by
      have eq : (!(C.eval (List.ofFn x ++ [x 4 && x 6]))) = f x := Classical.byContradiction (all x)
      simpa only [Bool.not_not] using congrArg Bool.not eq
    obtain ⟨A,B,small,mA,mB,realizes⟩ := extract C sz fan refs opposite
    obtain ⟨x,bad⟩ := lower A small mA
    exact bad (normalize A B mA mB realizes x)
