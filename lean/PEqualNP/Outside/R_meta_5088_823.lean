import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- On each sensitive pair at vertex zero at least one gate reading a polarity
-- must change value. This condition constrains the readers jointly.
theorem PEqualNP.Outside.R_meta_5088_823
    (trace : ∀ C : Circuit, let f := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any fun k => x (Fin.ofNat 10 (k / 10)) && x (Fin.ofNat 10 (k % 10));
      let obs := fun (x : Fin 10 → Bool) => C.wires (List.ofFn x ++ [!x 0]);
      let read := fun (g : Gate) => if g.op.eval [false] then g.inputs.head? == some 0 || g.inputs.head? == some 10 else g.inputs.contains 0 || g.inputs.contains 10;
      FanInTwo C → (∀ x, (obs x).getD C.output false = f x) → ∀ x : Fin 10 → Bool, let lo := Function.update x 0 false; let hi := Function.update x 0 true; f lo ≠ f hi → ∃ j : Fin C.gates.length, read (C.gates.get j) = true ∧ (obs lo).getD (11+j.val) false ≠ (obs hi).getD (11+j.val) false)
    (covered : ∀ C : Circuit, let f := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any fun k => x (Fin.ofNat 10 (k / 10)) && x (Fin.ofNat 10 (k % 10));
      let obs := fun (x : Fin 10 → Bool) => C.wires (List.ofFn x ++ [!x 0]);
      let read := fun (g : Gate) => if g.op.eval [false] then g.inputs.head? == some 0 || g.inputs.head? == some 10 else g.inputs.contains 0 || g.inputs.contains 10;
      FanInTwo C → C.size ≤ 18 →
      1 ≤ C.gates.countP read → C.gates.countP read ≤ 2 →
      (∀ x : Fin 10 → Bool, let lo := Function.update x 0 false; let hi := Function.update x 0 true; f lo ≠ f hi → ∃ j : Fin C.gates.length, read (C.gates.get j) = true ∧ (obs lo).getD (11+j.val) false ≠ (obs hi).getD (11+j.val) false) → ∃ x, (obs x).getD C.output false ≠ f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (18 : ℕ) →       have x4 : ℕ := List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => if x4.op.eval [Bool.false] = Bool.true then x4.inputs.head? == Option.some (0 : ℕ) || x4.inputs.head? == Option.some (10 : ℕ) else x4.inputs.contains (0 : ℕ) || x4.inputs.contains (10 : ℕ)) x1.gates;       (1 : ℕ) ≤ x4 → x4 ≤ (2 : ℕ) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [!x7 (0 : Fin (10 : ℕ))]) ≠ (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) := by
  intro C legal size
  dsimp only
  intro lower upper
  let f := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any fun k => x (Fin.ofNat 10 (k / 10)) && x (Fin.ofNat 10 (k % 10))
  have bridge : ∀ x : Fin 10 → Bool, f x = (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))) := by
    dsimp only [f]
    decide +kernel
  by_contra no
  have computes (x : Fin 10 → Bool) : (C.wires (List.ofFn x ++ [!x 0])).getD C.output false = f x := by
    rw [bridge]
    by_contra bad
    exact no ⟨x,bad⟩
  obtain ⟨x,hx⟩ := covered C legal size lower upper (trace C legal computes)
  exact hx (computes x)
