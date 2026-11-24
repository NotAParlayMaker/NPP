import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Cut of L-meta-2293. The first hypothesis only normalizes a computing circuit: every gate
-- reads wires that already exist among the ten inputs, no gate reads a wire twice, a not gate
-- reads one wire and every other gate reads two. The second hypothesis is what remains of the
-- bound once that normalization is paid for: no circuit in normal form computes the negated
-- edge function.
set_option maxHeartbeats 400000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_2293_1
    (hNF : let E : List (Fin 9 × Fin 9) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
      let g : (Fin 9 → Bool) → Bool := fun x => !(E.any (fun p => x p.1 && x p.2))
      let inp : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 && x 6]
      let NF : Circuit → Prop := fun D =>
        ∀ i : Fin D.size, let h := D.gates.get i
          (∀ w ∈ h.inputs, w < 10 + (i : ℕ)) ∧ h.inputs.Nodup ∧
          ((h.op = GateOp.not ∧ h.inputs.length = 1) ∨
            (h.op ≠ GateOp.not ∧ h.inputs.length = 2))
      ∀ (x1 : List Gate) (x2 : ℕ), FanInTwo { gates := x1, output := 0 } → x1.length ≤ 13 →
        (∀ x : Fin 9 → Bool, ({ gates := x1, output := x2 } : Circuit).eval (inp x) = g x) →
        ∃ (y1 : List Gate) (y2 : ℕ), FanInTwo { gates := y1, output := 0 } ∧ y1.length ≤ 13 ∧
          NF { gates := y1, output := y2 } ∧
          ∀ x : Fin 9 → Bool, ({ gates := y1, output := y2 } : Circuit).eval (inp x) = g x)
    (hNo : let E : List (Fin 9 × Fin 9) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
      let g : (Fin 9 → Bool) → Bool := fun x => !(E.any (fun p => x p.1 && x p.2))
      let inp : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 && x 6]
      let NF : Circuit → Prop := fun D =>
        ∀ i : Fin D.size, let h := D.gates.get i
          (∀ w ∈ h.inputs, w < 10 + (i : ℕ)) ∧ h.inputs.Nodup ∧
          ((h.op = GateOp.not ∧ h.inputs.length = 1) ∨
            (h.op ≠ GateOp.not ∧ h.inputs.length = 2))
      ∀ (x1 : List Gate) (x2 : ℕ), FanInTwo { gates := x1, output := 0 } → x1.length ≤ 13 →
        NF { gates := x1, output := x2 } →
        ∃ x : Fin 9 → Bool, ({ gates := x1, output := x2 } : Circuit).eval (inp x) ≠ g x) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → x1.length ≤ (13 : ℕ) → (fun (x5 : Fin (9 : ℕ) → Bool) => { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ))])) ≠ fun (x5 : Fin (9 : ℕ) → Bool) => !(x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  intro x1 x2 hfan hlen
  by_contra hc
  have hchain : ∀ x : Fin 9 → Bool, ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) =
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any (fun p => x p.1 && x p.2) := by
    decide
  have hpoint : ∀ x : Fin 9 → Bool,
      ({ gates := x1, output := x2 } : Circuit).eval (List.ofFn x ++ [x 0 && x 6]) =
        !(([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any (fun p => x p.1 && x p.2)) := by
    intro x
    have hx := congrFun hc x
    rw [hx, hchain x]
  obtain ⟨y1, y2, hyfan, hylen, hyNF, hycomp⟩ := hNF x1 x2 hfan hlen hpoint
  obtain ⟨x, hx⟩ := hNo y1 y2 hyfan hylen hyNF
  exact hx (hycomp x)
