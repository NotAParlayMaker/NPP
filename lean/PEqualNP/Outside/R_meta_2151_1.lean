import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2151_1 :
    (∀ (D : Circuit) (inputs : List ℕ),
      FanInTwo D → inputs.length ≤ 2 → 9 ∉ inputs →
      (∀ x : Fin 9 → Bool,
        let wires := List.ofFn x ++ [x 0 || x 4]
        D.eval (wires ++ [GateOp.or.eval (inputs.map fun i => wires.getD i false)]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
            (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
            (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      14 ≤ D.size) →
    (∀ (D : Circuit) (inputs : List ℕ),
      FanInTwo D → inputs.length ≤ 2 → 9 ∈ inputs →
      (∀ x : Fin 9 → Bool,
        let wires := List.ofFn x ++ [x 0 || x 4]
        D.eval (wires ++ [GateOp.or.eval (inputs.map fun i => wires.getD i false)]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
            (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
            (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      14 ≤ D.size) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (16 : ℕ) ≤ x1.size := by
  intro independent dependent C hFan hFirst hFun hSecond
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]; omega
  rcases C with ⟨gs, out⟩
  rcases gs with _ | ⟨first, gs⟩
  · simp at hSecond
  rcases gs with _ | ⟨second, tail⟩
  · simp at hSecond
  have hop : second.op = GateOp.or := by simpa using hSecond
  let D : Circuit := ⟨tail, out⟩
  have hTail : FanInTwo D := by
    intro g hg
    exact hFan g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
  have hLength : second.inputs.length ≤ 2 := (hFan second (by simp)).2
  have hPrefix (x : Fin 9 → Bool) :
      step (List.ofFn x) first = List.ofFn x ++ [x 0 || x 4] := by
    have hv := hFirst x
    change ((second :: tail).foldl step (step (List.ofFn x) first)).getD 9 false = _ at hv
    rw [keep] at hv
    · have last (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
        simp [List.getD_eq_getElem?_getD]
      have hLast := last (List.ofFn x)
        (first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false))
      rw [List.length_ofFn] at hLast
      change (List.ofFn x ++ [_]).getD 9 false = _ at hv
      rw [hLast] at hv
      simp only [step, hv]
    · simp [step]
  have hEval (x : Fin 9 → Bool) :
      let wires := List.ofFn x ++ [x 0 || x 4]
      D.eval (wires ++ [GateOp.or.eval (second.inputs.map fun i => wires.getD i false)]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    have h := congrFun hFun x
    change (tail.foldl step (step (step (List.ofFn x) first) second)).getD out false = _ at h
    rw [hPrefix] at h
    simpa only [step, hop, D, Circuit.eval, Circuit.wires] using h
  have lower : 14 ≤ D.size := by
    by_cases h : 9 ∈ second.inputs
    · exact dependent D second.inputs hTail hLength h hEval
    · exact independent D second.inputs hTail hLength h hEval
  change 14 ≤ tail.length at lower
  change 16 ≤ (first :: second :: tail).length
  simp; omega
