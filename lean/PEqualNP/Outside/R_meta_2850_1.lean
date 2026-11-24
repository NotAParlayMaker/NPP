import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reduce L-meta-2850 (the x2 = true case of the R_meta_2541_1 cut; its sibling
-- L-meta-2848, the x2 = false case, is already proved in main) by splitting on the
-- number of gates reading wire 0: the 0-reader case is proved inline (the circuit
-- does not depend on wire 0, so two inputs differing only in x0 distinguish it from
-- the edge function), and the exactly-1-reader case splits into a NOT reader and a
-- non-NOT reader, each a new fleet gap. The 0-reader argument is adapted from
-- R_meta_2541_2 with the flip bit fixed to true.
theorem PEqualNP.Outside.R_meta_2850_1
    (notReader : ∀ (C : Circuit), FanInTwo C → C.size ≤ 14 →
      (C.gates.filter fun g => g.inputs.contains 0).length = 1 →
      (∃ g ∈ C.gates, 0 ∈ g.inputs ∧ g.op = GateOp.not) →
      ∃ x : Fin 9 → Bool,
        circuitFun 9 C (fun i => if i = 0 then true != x 0 else x i) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (otherReader : ∀ (C : Circuit), FanInTwo C → C.size ≤ 14 →
      (C.gates.filter fun g => g.inputs.contains 0).length = 1 →
      (¬ ∃ g ∈ C.gates, 0 ∈ g.inputs ∧ g.op = GateOp.not) →
      ∃ x : Fin 9 → Bool,
        circuitFun 9 C (fun i => if i = 0 then true != x 0 else x i) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (x2 = Bool.true) → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro C x2 hFan hSize hCount hx2
  subst hx2
  classical
  by_cases hZero : (C.gates.filter fun g => g.inputs.contains 0).length = 0
  · have hNone : ∀ g ∈ C.gates, 0 ∉ g.inputs := by
      intro g hg hRead
      have hm : g ∈ C.gates.filter (fun h => h.inputs.contains 0) := by
        simpa using And.intro hg hRead
      have he : (C.gates.filter fun h => h.inputs.contains 0) = [] :=
        List.length_eq_zero_iff.mp hZero
      rw [he] at hm
      exact List.not_mem_nil hm
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have independent (gs : List Gate) (hgs : ∀ g ∈ gs, 0 ∉ g.inputs)
        (tail : List Bool) (o : ℕ) (ho : o ≠ 0) :
        (gs.foldl step (false :: tail)).getD o false =
        (gs.foldl step (true :: tail)).getD o false := by
      induction gs generalizing tail with
      | nil => cases o <;> simp_all
      | cons g gs ih =>
        have same : g.inputs.map (fun i => (false :: tail).getD i false) =
            g.inputs.map (fun i => (true :: tail).getD i false) := by
          apply List.map_congr_left
          intro i hi
          cases i with
          | zero => exact (hgs g (by simp) hi).elim
          | succ i => rfl
        simp only [List.foldl_cons, step, same, List.cons_append]
        exact ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) _
    have preserveZero (gs : List Gate) (a : Bool) (tail : List Bool) :
        (gs.foldl step (a :: tail)).getD 0 false = a := by
      induction gs generalizing tail with
      | nil => rfl
      | cons g gs ih => simpa only [List.foldl_cons, step, List.cons_append] using ih _
    have inputForm (x : Fin 9 → Bool) :
        (List.ofFn fun i : Fin 9 => if i = 0 then true != x 0 else x i) =
          (true != x 0) :: (List.ofFn fun i : Fin 8 => x i.succ) := by
      rw [List.ofFn_succ]
      simp
    by_contra! hAll
    by_cases hOut : C.output = 0
    · let x : Fin 9 → Bool := fun i => decide (i = 0)
      let y : Fin 9 → Bool := fun _ => false
      have hx := hAll x
      have hy := hAll y
      change (C.gates.foldl step (List.ofFn fun i : Fin 9 =>
        if i = 0 then true != x 0 else x i)).getD C.output false = _ at hx
      change (C.gates.foldl step (List.ofFn fun i : Fin 9 =>
        if i = 0 then true != y 0 else y i)).getD C.output false = _ at hy
      rw [hOut, inputForm, preserveZero] at hx hy
      simp [y] at hy
    · let x : Fin 9 → Bool := fun i => decide (i = 1)
      let y : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
      have hx := hAll x
      have hy := hAll y
      change (C.gates.foldl step (List.ofFn fun i : Fin 9 =>
        if i = 0 then true != x 0 else x i)).getD C.output false = _ at hx
      change (C.gates.foldl step (List.ofFn fun i : Fin 9 =>
        if i = 0 then true != y 0 else y i)).getD C.output false = _ at hy
      have ht : (List.ofFn fun i : Fin 8 => x i.succ) =
          List.ofFn (fun i : Fin 8 => y i.succ) := by decide
      rw [inputForm] at hx hy
      rw [← ht] at hy
      have hi := independent C.gates hNone (List.ofFn fun i : Fin 8 => x i.succ) C.output hOut
      have hxy :
          (C.gates.foldl step ((true != x 0) :: List.ofFn fun i : Fin 8 => x i.succ)).getD
            C.output false =
          (C.gates.foldl step ((true != y 0) :: List.ofFn fun i : Fin 8 => x i.succ)).getD
            C.output false :=
        hi.symm
      rw [hx, hy] at hxy
      have impossible : false = true := hxy
      cases impossible
  · have hOne : (C.gates.filter fun g => g.inputs.contains 0).length = 1 := by omega
    by_cases hn : ∃ g ∈ C.gates, 0 ∈ g.inputs ∧ g.op = GateOp.not
    · exact notReader C hFan hSize hOne hn
    · exact otherReader C hFan hSize hOne hn
