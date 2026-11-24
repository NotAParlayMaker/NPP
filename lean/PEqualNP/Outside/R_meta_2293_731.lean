import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.R_meta_2293_731
    (relabel : ∀ (p : Fin 10 → Fin 10) (f : (Fin 10 → Bool) → Bool) (s : ℕ),
      HasCircuitSize 10 f s → HasCircuitSize 10 (fun x => f (x ∘ p)) s)
    (drop : ∀ (f : (Fin 10 → Bool) → Bool) (s : ℕ), 2 ≤ s →
      (∃ x, f (Function.update x 8 false) ≠ f (Function.update x 8 true)) →
      (∀ b : Bool, ∃ x y : Fin 10 → Bool,
        f (Function.update x 8 b) ≠ f (Function.update y 8 b)) →
      HasCircuitSize 10 f s →
      HasCircuitSize 8 (fun x => f (Fin.append x (fun _ : Fin 2 => false))) (s - 1))
    (lower : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      !(x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4)) 12) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → x1.length ≤ (13 : ℕ) → (fun (x5 : Fin (9 : ℕ) → Bool) => { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ))])) ≠ fun (x5 : Fin (9 : ℕ) → Bool) => !(x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  intro gs o fan hlen hsame
  let C : Circuit := ⟨gs, o⟩
  let f (z : Fin 10 → Bool) := C.eval (List.ofFn z)
  let p : Fin 10 → Fin 10 := ![1, 0, 4, 7, 5, 2, 8, 6, 3, 9]
  let g (z : Fin 10 → Bool) := f (z ∘ p)
  let edge (z : Fin 9 → Bool) :=
    z 0 && z 1 || z 1 && z 2 || z 2 && z 3 || z 3 && z 4 || z 4 && z 0 ||
      z 0 && z 5 || z 1 && z 6 || z 2 && z 7 || z 3 && z 8 || z 5 && z 7 ||
      z 6 && z 8 || z 8 && z 5
  have hC : HasCircuitSize 10 f 13 := ⟨C, fan, hlen, fun _ => rfl⟩
  have hg : HasCircuitSize 10 g 13 := relabel p f 13 hC
  have pinned (z : Fin 10 → Bool) (hz : z 9 = (z 0 && z 6)) :
      f z = !edge (fun k : Fin 9 => z k.castSucc) := by
    let raw : Fin 9 → Bool := fun k => z k.castSucc
    have hl : List.ofFn z = List.ofFn raw ++ [z 9] := by
      rw [List.ofFn_succ']
      rfl
    change C.eval (List.ofFn z) = !edge raw
    rw [hl, hz]
    exact congrFun hsame raw
  have pair : ∃ z, g (Function.update z 8 false) ≠ g (Function.update z 8 true) := by
    let z : Fin 10 → Bool := fun i => decide (i = 0)
    refine ⟨z, ?_⟩
    change f (Function.update z 8 false ∘ p) ≠ f (Function.update z 8 true ∘ p)
    rw [pinned _ (by decide), pinned _ (by decide)]
    decide
  let q (x : Fin 8 → Bool) := Fin.append x (fun _ : Fin 2 => false)
  let cut (x : Fin 8 → Bool) :=
    !(x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
      x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4)
  have cut_eq (x : Fin 8 → Bool) : g (q x) = cut x := by
    change f (q x ∘ p) = cut x
    have hp : (q x ∘ p) 9 = ((q x ∘ p) 0 && (q x ∘ p) 6) := by
      change false = (x 1 && false)
      simp
    rw [pinned _ hp]
    change (!(x 1 && x 0 || x 0 && x 4 || x 4 && x 7 || x 7 && x 5 ||
      x 5 && x 1 || x 1 && x 2 || x 0 && false || x 4 && x 6 ||
      x 7 && x 3 || x 2 && x 6 || false && x 3 || x 3 && x 2)) = cut x
    simp only [cut, Bool.and_false, Bool.false_and, Bool.or_false]
    ac_rfl
  have nc (b : Bool) : ∃ x y : Fin 10 → Bool,
      g (Function.update x 8 b) ≠ g (Function.update y 8 b) := by
    let z : Fin 10 → Bool := fun _ => false
    let w : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 4)
    refine ⟨z, w, ?_⟩
    change f (Function.update z 8 b ∘ p) ≠ f (Function.update w 8 b ∘ p)
    cases b <;> rw [pinned _ (by decide), pinned _ (by decide)] <;> decide
  apply lower
  have h := drop g 13 (by omega) pair nc hg
  change HasCircuitSize 8 (fun x => g (q x)) 12 at h
  have heq : (fun x => g (q x)) = cut := funext cut_eq
  rwa [heq] at h
