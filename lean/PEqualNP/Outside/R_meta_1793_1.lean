import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Cut of L-meta-1793. The first hypothesis only normalizes a computing circuit: every gate
-- reads wires that already exist, no gate reads a wire twice, a not gate reads one wire and
-- every other gate reads two. The second hypothesis is what remains of the bound once that
-- normalization is paid for: no circuit in normal form computes the edge function.
set_option maxHeartbeats 400000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_1793_1
    (hNF : let E : List (Fin 9 × Fin 9) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
      let f : (Fin 9 → Bool) → Bool := fun x => E.any (fun p => x p.1 && x p.2)
      let inp : (Fin 9 → Bool) → List ℕ → List Bool := fun x l =>
        let w : List Bool := List.ofFn x ++ [x 0 && x 1]
        w ++ [GateOp.or.eval (List.map (fun i : ℕ => w.getD i false) l)]
      let NF : Circuit → Prop := fun D =>
        ∀ i : Fin D.size, let g := D.gates.get i
          (∀ w ∈ g.inputs, w < 11 + (i : ℕ)) ∧ g.inputs.Nodup ∧
          ((g.op = GateOp.not ∧ g.inputs.length = 1) ∨
            (g.op ≠ GateOp.not ∧ g.inputs.length = 2))
      ∀ (l : List ℕ) (C : Circuit), l.length ≤ 2 → FanInTwo C → C.size ≤ 13 →
        (∀ x : Fin 9 → Bool, C.eval (inp x l) = f x) →
        ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧ NF D ∧
          ∀ x : Fin 9 → Bool, D.eval (inp x l) = f x)
    (hNo : let E : List (Fin 9 × Fin 9) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
      let f : (Fin 9 → Bool) → Bool := fun x => E.any (fun p => x p.1 && x p.2)
      let inp : (Fin 9 → Bool) → List ℕ → List Bool := fun x l =>
        let w : List Bool := List.ofFn x ++ [x 0 && x 1]
        w ++ [GateOp.or.eval (List.map (fun i : ℕ => w.getD i false) l)]
      let NF : Circuit → Prop := fun D =>
        ∀ i : Fin D.size, let g := D.gates.get i
          (∀ w ∈ g.inputs, w < 11 + (i : ℕ)) ∧ g.inputs.Nodup ∧
          ((g.op = GateOp.not ∧ g.inputs.length = 1) ∨
            (g.op ≠ GateOp.not ∧ g.inputs.length = 2))
      ∀ (l : List ℕ) (D : Circuit), l.length ≤ 2 → FanInTwo D → D.size ≤ 13 → NF D →
        ∃ x : Fin 9 → Bool, D.eval (inp x l) ≠ f x) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 x3 hfan hsize
  by_contra hc
  simp only [not_exists, ne_eq, not_not] at hc
  have hchain : ∀ x : Fin 9 → Bool, ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) =
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any (fun p => x p.1 && x p.2) := by
    decide
  have hcomp : ∀ x : Fin 9 → Bool, x3.eval (List.ofFn x ++ [x 0 && x 1] ++
          [GateOp.or.eval (List.map (fun i : ℕ => (List.ofFn x ++ [x 0 && x 1]).getD i false) x1)]) =
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any (fun p => x p.1 && x p.2) := by
    intro x
    rw [hc x]
    exact hchain x
  obtain ⟨D, hDfan, hDsize, hDNF, hDcomp⟩ := hNF x1 x3 hx1 hfan hsize hcomp
  obtain ⟨x, hx⟩ := hNo x1 D hx1 hDfan hDsize hDNF
  exact hx (hDcomp x)
