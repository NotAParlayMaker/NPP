import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3438_618
    (normalize : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) C.gates ≤ (12 : ℕ) →
      ∃ (ys : List ((ℕ × Bool) × (ℕ × Bool))) (out : ℕ × Bool),
        ys.length ≤ 12 ∧ out.1 < 22 ∧
        (∀ g ∈ ys, g.1.1 < 22 ∧ g.2.1 < 22) ∧
        ∀ (x3 : Fin 9 → Bool), have w : List Bool := ys.foldl (fun (w : List Bool) g => w ++ [(w.getD g.1.1 false != g.1.2) && (w.getD g.2.1 false != g.2.2)]) (List.ofFn x3 ++ [false]); (w.getD out.1 false != out.2) = C.eval (List.ofFn x3))
    (finite : ∀ (ys : List ((ℕ × Bool) × (ℕ × Bool))) (out : ℕ × Bool),
      ys.length ≤ 12 → out.1 < 22 → (∀ g ∈ ys, g.1.1 < 22 ∧ g.2.1 < 22) →
      ∃ (x3 : Fin 9 → Bool), have w : List Bool := ys.foldl (fun (w : List Bool) g => w ++ [(w.getD g.1.1 false != g.1.2) && (w.getD g.2.1 false != g.2.2)]) (List.ofFn x3 ++ [false]); (w.getD out.1 false != out.2) ≠ (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates := by
  intro C fan computes
  by_contra h
  have small : List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) C.gates ≤ (12 : ℕ) := by omega
  obtain ⟨ys, out, hlen, hout, hys, heval⟩ := normalize C fan small
  obtain ⟨x, hx⟩ := finite ys out hlen hout hys
  exact hx ((heval x).trans (computes x))
