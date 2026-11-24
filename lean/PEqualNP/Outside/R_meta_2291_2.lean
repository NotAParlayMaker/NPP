import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Restore the final OR. The fixed nonedge gate can then be discarded or
-- the restriction x6 = false can save two gates in the continuation.
theorem PEqualNP.Outside.R_meta_2291_2
    (restrict :
      let f := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ D : Circuit, FanInTwo D → D.size ≤ 14 → D.output ≠ 6 → D.output ≠ 9 →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 && x 6]) = f x) →
      HasCircuitSize 9 f 14 ∨
      HasCircuitSize 8 (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
        (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
        (x 5 && x 7) || (x 7 && x 4)) 12)
    (unrestricted : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 14)
    (eight : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
        (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
        (x 5 && x 7) || (x 7 && x 4)) 12) :
∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → x1.length ≤ (13 : ℕ) → x2 < x3 → x3 < (10 : ℕ) + x1.length → (fun (x8 : Fin (9 : ℕ) → Bool) => { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))]) || { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))])) ≠ fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) := by
  intro gs a b fan length _ _ computes
  let last : Gate := ⟨GateOp.or, [a, b]⟩
  let D : Circuit := ⟨gs ++ [last], 10 + gs.length⟩
  have df : FanInTwo D := by
    intro g hg
    change g ∈ gs ++ [last] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact fan g hg
    · have he : g = last := List.mem_singleton.mp hg
      subst g
      simp [last]
  have size : D.size ≤ 14 := by
    change (gs ++ [last]).length ≤ 14
    simp only [List.length_append, List.length_singleton]
    omega
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have runLen (gates : List Gate) (w : List Bool) :
      (gates.foldl step w).length = w.length + gates.length := by
    induction gates generalizing w with
    | nil => simp
    | cons g tail ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have eval (x : Fin 9 → Bool) :
      D.eval (List.ofFn x ++ [x 0 && x 6]) =
        (((⟨gs, a⟩ : Circuit).eval (List.ofFn x ++ [x 0 && x 6])) ||
         ((⟨gs, b⟩ : Circuit).eval (List.ofFn x ++ [x 0 && x 6]))) := by
    let w := List.ofFn x ++ [x 0 && x 6]
    let W := gs.foldl step w
    have len : W.length = 10 + gs.length := by
      simp only [W, runLen, w, List.length_append, List.length_ofFn, List.length_singleton]
    change ((gs ++ [last]).foldl step w).getD (10 + gs.length) false =
      (W.getD a false || W.getD b false)
    rw [List.foldl_append]
    change (W ++ [(last.op.eval (last.inputs.map fun i => W.getD i false))]).getD
      (10 + gs.length) false = _
    rw [← len]
    change (W ++ [(GateOp.or.eval [W.getD a false, W.getD b false])]).getD W.length false = _
    have get : (W ++ [(GateOp.or.eval [W.getD a false, W.getD b false])]).getD W.length false =
        GateOp.or.eval [W.getD a false, W.getD b false] := by simp
    rw [get]
    cases W.getD a false <;> cases W.getD b false <;> rfl
  have ne6 : D.output ≠ 6 := by change 10 + gs.length ≠ 6; omega
  have ne9 : D.output ≠ 9 := by change 10 + gs.length ≠ 9; omega
  rcases restrict D df size ne6 ne9 (fun x => (eval x).trans (congrFun computes x)) with won | won
  · exact unrestricted won
  · exact eight won
