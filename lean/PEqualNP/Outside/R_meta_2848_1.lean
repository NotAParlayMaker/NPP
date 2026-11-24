import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2848_1 :
    (∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
      (C.gates.filter fun g => g.inputs.contains 0).length = 1 →
      ( ∃ g ∈ C.gates, 0 ∈ g.inputs ∧ g.op = GateOp.not) →
      ∃ x : Fin 9 → Bool, circuitFun 9 C x ≠ (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) →
    (∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
      (C.gates.filter fun g => g.inputs.contains 0).length = 1 →
      (¬ ∃ g ∈ C.gates, 0 ∈ g.inputs ∧ g.op = GateOp.not) →
      ∃ x : Fin 9 → Bool, circuitFun 9 C x ≠ (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → x2 = Bool.false → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro notReader otherReader C bit hFan hSize hCount hBit
  subst bit
  have identity (x : Fin 9 → Bool) :
      (fun i : Fin 9 => if i = 0 then false != x 0 else x i) = x := by
    funext i
    by_cases hi : i = 0
    · subst i
      cases x (0 : Fin 9) <;> simp_all
    · simp [hi]
  simp only [identity]
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
    by_contra! hAll
    by_cases hOut : C.output = 0
    · let x : Fin 9 → Bool := fun i => decide (i = 0)
      have h := hAll x
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = _ at h
      rw [hOut, List.ofFn_succ, preserveZero] at h
      have impossible : true = false := by simpa [x] using h
      cases impossible
    · let x : Fin 9 → Bool := fun i => decide (i = 1)
      let y : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
      have hx := hAll x
      have hy := hAll y
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = _ at hx
      change (C.gates.foldl step (List.ofFn y)).getD C.output false = _ at hy
      have ht : (List.ofFn fun i : Fin 8 => x i.succ) =
          List.ofFn (fun i : Fin 8 => y i.succ) := by decide
      rw [List.ofFn_succ] at hx hy
      rw [← ht] at hy
      have hi := independent C.gates hNone (List.ofFn fun i : Fin 8 => x i.succ) C.output hOut
      have hxval : (C.gates.foldl step (false :: List.ofFn fun i : Fin 8 => x i.succ)).getD
          C.output false = false := by simpa [x] using hx
      have hyval : (C.gates.foldl step (true :: List.ofFn fun i : Fin 8 => x i.succ)).getD
          C.output false = true := by simpa [x, y] using hy
      rw [hxval, hyval] at hi
      exact Bool.noConfusion hi
  · have hOne : (C.gates.filter fun g => g.inputs.contains 0).length = 1 := by omega
    by_cases hn : ∃ g ∈ C.gates, 0 ∈ g.inputs ∧ g.op = GateOp.not
    · exact notReader C hFan hSize hOne hn
    · exact otherReader C hFan hSize hOne hn
