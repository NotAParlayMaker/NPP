import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2598_381
    (minor : ∀ v : Fin 10, ¬ HasCircuitSize 9 (fun y : Fin 9 → Bool =>
      let x : Fin 10 → Bool := Fin.insertNth v false y
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] :
        List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) 14)
    (eliminate : ∀ (v : Fin 10) (C : Circuit), FanInTwo C → C.size ≤ 18 →
      let read := fun g : Gate =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          (fun i => decide (i = v.val ∨ v = 0 ∧ i = 10))
      let input := fun y : Fin 9 → Bool =>
        let x : Fin 10 → Bool := Fin.insertNth v false y
        List.ofFn x ++ [!x 0]
      (if v = 0 then 4 else 5) ≤ C.gates.countP read →
      C.eval (input fun _ => false) = false →
      HasCircuitSize 9 (fun y => C.eval (input y)) 14)
    (residual : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
      (∀ v : Fin 10,
        C.gates.countP (fun g =>
          (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
            (fun i => decide (i = v.val ∨ v = 0 ∧ i = 10))) < (if v = 0 then 4 else 5)) →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] :
          List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  let f (x : Fin 10 → Bool) :=
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] :
      List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
  have format (x : Fin 10 → Bool) : f x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
       x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    simp [f, Bool.or_assoc]
  intro C basis budget
  by_contra! same
  have correct (x : Fin 10 → Bool) : C.eval (List.ofFn x ++ [!x 0]) = f x :=
    (same x).trans (format x).symm
  have noEdge (v : Fin 10) : f (Fin.insertNth v false (fun _ : Fin 9 => false)) = false := by
    have h : Fin.insertNth v false (fun _ : Fin 9 => false) = (fun _ : Fin 10 => false) := by
      funext j
      refine Fin.succAboveCases v ?_ (fun i => ?_) j
      · simp
      · simp
    rw [h]
    rfl
  have reads (v : Fin 10) :
      C.gates.countP (fun g =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          (fun i => decide (i = v.val ∨ v = 0 ∧ i = 10))) < (if v = 0 then 4 else 5) := by
    by_contra! many
    have smaller := eliminate v C basis budget many
      ((correct (Fin.insertNth v false (fun _ => false))).trans (noEdge v))
    obtain ⟨D, hD, sD, eD⟩ := smaller
    exact minor v ⟨D, hD, sD, fun y => (eD y).trans (correct (Fin.insertNth v false y))⟩
  obtain ⟨x, different⟩ := residual C basis budget reads
  exact different (correct x)

