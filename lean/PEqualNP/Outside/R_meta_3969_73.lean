import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3969_73
    (exclude :
      let r := fun (g : Gate) =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any (fun j => decide (j = 6))
      let I := fun b (x : Fin 8 → Bool) =>
        [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
      let f := fun x : Fin 8 → Bool =>
        ([1, 12, 23, 4, 15, 26, 37, 46, 57, 74] : List ℕ).any
          fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))
      ∀ C : Circuit, FanInTwo C → C.gates.countP (fun g => g.op.eval [false]) = 0 →
        C.gates.countP r ≤ 1 → (∀ x, C.eval (I false x) = f x) →
        (∀ x, C.eval (I true x) = (f x || x 0 || x 3)) →
        ∀ g ∈ C.gates, g.op = .or → 6 ∈ g.inputs →
          ∀ j ∈ ([0, 2, 7, 8, 9] : List ℕ), j ∉ g.inputs)
    (remaining :
      let r := fun (g : Gate) =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any (fun j => decide (j = 6))
      let I := fun b (x : Fin 8 → Bool) =>
        [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
      let f := fun x : Fin 8 → Bool =>
        ([1, 12, 23, 4, 15, 26, 37, 46, 57, 74] : List ℕ).any
          fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))
      ∀ C : Circuit, FanInTwo C → C.size = 14 → C.gates.countP (fun g => g.op.eval [false]) = 0 →
        C.gates.countP r ≤ 1 → (∀ x, C.eval (I false x) = f x) →
        (∃ g ∈ C.gates, g.op = .or ∧ 6 ∈ g.inputs ∧
          ∀ j ∈ ([0, 2, 7, 8, 9] : List ℕ), j ∉ g.inputs) →
        ∃ x, C.eval (I true x) ≠ (f x || x 0 || x 3)) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false]) x4.gates = (0 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x9 ∈ x4.gates, x9.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x9.inputs) → (∀ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x10) = x3 x10) → ∃ (x11 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x11) ≠ (x3 x11 || x11 (0 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ))) := by
  dsimp only
  intro C fan size noNot count readers off
  let I := fun b (x : Fin 8 → Bool) =>
    [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
  let f := fun x : Fin 8 → Bool =>
    ([1, 12, 23, 4, 15, 26, 37, 46, 57, 74] : List ℕ).any
      fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))
  have f_eq (x : Fin 8 → Bool) : f x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) := by
    simp [f, List.any_cons, Bool.or_assoc]
    rfl
  have off' (x : Fin 8 → Bool) : C.eval (I false x) = f x := (off x).trans (f_eq x).symm
  by_contra! on
  have on' (x : Fin 8 → Bool) : C.eval (I true x) = (f x || x 0 || x 3) := by
    rw [f_eq]
    exact on x
  obtain ⟨g, hg, op, pin⟩ := readers
  have skip := exclude C fan noNot count off' on' g hg op pin
  obtain ⟨x, different⟩ := remaining C fan size noNot count off' ⟨g, hg, op, pin, skip⟩
  exact different (on' x)
