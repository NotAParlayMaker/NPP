import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fixing either endpoint at zero makes the auxiliary input a copy of the other endpoint.
-- Three direct readers would leave at most eleven gates for the resulting eight-input function.
theorem PEqualNP.Outside.R_meta_3091_673
    (cofactor :
      let f := fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      let reads := fun (C : Circuit) i =>
        C.gates.countP (fun g => (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains i)
      ∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
        (∀ x, C.eval (List.ofFn x ++ [x 0 || x 3]) = f x) → reads C 0 ≤ 2 ∧ reads C 3 ≤ 2)
    (restricted :
      let f := fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      let reads := fun (C : Circuit) i =>
        C.gates.countP (fun g => (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains i)
      ∀ C : Circuit, FanInTwo C → C.size = 14 →
        let refs := C.output :: C.gates.flatMap Gate.inputs
        (∀ i ∈ refs, i ≤ 24) →
        (∀ i < 24, i ∈ refs) →
        9 + (C.gates.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length +
          (∑ i ∈ Finset.range 24, (refs.count i - 1)) ≤ 14 →
        2 ≤ refs.count 9 →
        reads C 0 ≤ 2 → reads C 3 ≤ 2 →
        (∀ p : Fin 9, ∃ x, C.eval (List.ofFn x ++ [x p]) ≠ f x) →
        ∃ x, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x)
    : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (14 : ℕ) → (x2.output ≤ (10 : ℕ) + x2.size ∧ ∀ x5 ∈ x2.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x2.size) → (∀ x6 < (10 : ℕ) + x2.size, x6 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (9 : ℕ) + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false] && !x7.op.eval [Bool.true]) x2.gates).length + ∑ x7 ∈ Finset.range ((10 : ℕ) + x2.size), (List.count x7 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) - (1 : ℕ)) ≤ x2.size → (2 : ℕ) ≤ List.count (9 : ℕ) (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (∀ (x9 : Fin (9 : ℕ)), ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 x9]) ≠ x1 x10) → ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]) ≠ x1 x10 := by
  dsimp only at cofactor restricted ⊢
  intro C legal size bound live budget reused duplicate
  by_contra noWitness
  have results x := Classical.not_not.mp (fun different => noWitness ⟨x, different⟩)
  have correct (x : Fin 9 → Bool) :
      C.eval (List.ofFn x ++ [x 0 || x 3]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) := by
    simpa only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using results x
  obtain ⟨left, right⟩ := cofactor C legal (Nat.le_of_eq size) correct
  have pins (i : ℕ) (hi : i ∈ C.output :: C.gates.flatMap Gate.inputs) : i ≤ 24 := by
    rw [List.mem_cons, List.mem_flatMap] at hi
    rcases hi with eq | ⟨g, hg, hgi⟩
    · simpa [eq, size] using bound.1
    · simpa [size] using bound.2 g hg i hgi
  have need := restricted C legal size pins (by simpa [size] using live)
    (by simpa [size] using budget) reused left right (by
      simpa only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using duplicate)
  apply noWitness
  simpa only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using need
