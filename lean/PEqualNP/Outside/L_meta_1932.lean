import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_1668

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_1932 :
    ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 →
          x3.size ≤ (13 : ℕ) →
            ∃ (x6 : Fin (9 : ℕ) → Bool),
              have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];
              x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins hpins D hfan hsize
  by_contra hcon
  let edge : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  -- If no counterexample input exists, D computes the edge function on the
  -- 11-wire input (9 inputs, the AND(x0,x2) wire, one extra OR wire).
  have hall : ∀ y : Fin 9 → Bool,
      D.eval ((List.ofFn y ++ [y 0 && y 2]) ++
        [GateOp.or.eval (pins.map fun i => (List.ofFn y ++ [y 0 && y 2]).getD i false)]) =
        edge y := by
    intro y
    by_contra hy
    exact hcon ⟨y, hy⟩
  let g0 : Gate := ⟨GateOp.and, [0, 2]⟩
  let g1 : Gate := ⟨GateOp.or, pins⟩
  let C : Circuit := ⟨[g0, g1] ++ D.gates, D.output⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserved : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
    intro gs w i hi
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons]
      have hlt : i < (step w g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (step w g) hlt]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hstep2 : ∀ y : Fin 9 → Bool,
      List.foldl step (List.ofFn y) [g0, g1] =
        (List.ofFn y ++ [y 0 && y 2]) ++
          [GateOp.or.eval (pins.map fun i => (List.ofFn y ++ [y 0 && y 2]).getD i false)] := by
    intro y
    have ha : GateOp.and.eval ([0, 2].map fun i => (List.ofFn y).getD i false) = (y 0 && y 2) := by
      simp [GateOp.eval]
    show step (step (List.ofFn y) g0) g1 = _
    simp only [step, g0, g1, ha]
  -- The wires of the prepended circuit C agree with the wires of D.
  have hwires : ∀ y : Fin 9 → Bool,
      C.wires (List.ofFn y) =
        D.wires ((List.ofFn y ++ [y 0 && y 2]) ++
          [GateOp.or.eval (pins.map fun i => (List.ofFn y ++ [y 0 && y 2]).getD i false)]) := by
    intro y
    show List.foldl step (List.ofFn y) ([g0, g1] ++ D.gates) =
      List.foldl step ((List.ofFn y ++ [y 0 && y 2]) ++
        [GateOp.or.eval (pins.map fun i => (List.ofFn y ++ [y 0 && y 2]).getD i false)]) D.gates
    rw [List.foldl_append, hstep2 y]
  -- The first gate of C computes x0 AND x2.
  have hfirst : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2) := by
    intro y
    rw [hwires y]
    show (List.foldl step ((List.ofFn y ++ [y 0 && y 2]) ++
        [GateOp.or.eval (pins.map fun i => (List.ofFn y ++ [y 0 && y 2]).getD i false)]) D.gates).getD 9 false = (y 0 && y 2)
    rw [preserved D.gates _ 9 (by simp)]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp : 9 < (List.ofFn y ++ [y 0 && y 2]).length),
      List.getElem?_append_right (by simp : (List.ofFn y).length ≤ 9)]
    simp
  have hfanC : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with ((rfl | rfl) | hg)
    · exact ⟨Or.inl rfl, by simp [g0]⟩
    · exact ⟨Or.inr (Or.inl rfl), hpins⟩
    · exact hfan g hg
  have hsizeC : C.size = D.size + 2 := by
    simp [C, Circuit.size, List.length_cons]
  -- C computes the edge function, contradicting L_meta_1668.
  have hfun : circuitFun 9 C = edge := by
    funext y
    show C.eval (List.ofFn y) = edge y
    show (C.wires (List.ofFn y)).getD C.output false = edge y
    rw [hwires y]
    exact hall y
  have h16 := PEqualNP.Outside.L_meta_1668 C hfanC hfirst hfun
  omega
