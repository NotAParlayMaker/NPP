import Mathlib
import PEqualNP.Defs

-- The remaining slack is three exact sizes: thirteen binary gates and no NOT,
-- fourteen binary gates and no NOT, or thirteen binary gates and one NOT.
-- Each child is that finite case; the glue adds the gate-count partition and
-- rules the other sizes out.
theorem PEqualNP.Outside.R_meta_4310_1
    (h13 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ (x3 : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => !x4.op.eval [Bool.false]) C.gates → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false]) C.gates = (0 : ℕ) → C.size ≠ (13 : ℕ))
    (h14bin : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ (x3 : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => !x4.op.eval [Bool.false]) C.gates → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false]) C.gates = (0 : ℕ) → C.size ≠ (14 : ℕ))
    (h14not : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ (x3 : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => !x4.op.eval [Bool.false]) C.gates → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false]) C.gates = (1 : ℕ) → C.size ≠ (14 : ℕ)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => !x4.op.eval [Bool.false]) x1.gates → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false]) x1.gates ≤ (1 : ℕ) → (15 : ℕ) ≤ x1.size := by
  intro C hfan heval hbin hnots
  have hsz : C.size = C.gates.length := rfl
  have hsum : List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => !g.op.eval [Bool.false]) C.gates +
      List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [Bool.false]) C.gates =
      C.size := by
    rw [hsz]
    induction C.gates with
    | nil => simp
    | cons g gs ih =>
      simp [List.countP_cons] at ih ⊢
      cases g.op.eval [Bool.false] <;> simp [ih] <;> omega
  have : (15 : ℕ) ≤ C.size := by
    by_contra h
    have hle : C.size ≤ 14 := by omega
    have hge : 13 ≤ C.size := by omega
    have hcase : C.size = 13 ∨ C.size = 14 := by omega
    rcases hcase with hs | hs
    · have z : List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [Bool.false]) C.gates = 0 := by
        omega
      exact h13 C hfan heval hbin z hs
    · have hn : List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [Bool.false]) C.gates = 0 ∨
          List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [Bool.false]) C.gates = 1 := by
        omega
      rcases hn with z | z
      · exact h14bin C hfan heval hbin z hs
      · exact h14not C hfan heval hbin z hs
  exact this
