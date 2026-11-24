import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2012_741
    (hExtract : ∀ (C : Circuit) (T : Finset (Fin 9 → Bool)), FanInTwo C →
      ∃ W : List (Finset (Fin 9 → Bool)),
        let V (j : ℕ) := (List.ofFn fun i : Fin 9 => T.filter (fun x => x i)) ++ W.take j
        W.length = C.size ∧
        (∀ j < W.length, let A := fun i => (V j).getD i ∅
          ∃ a b : ℕ, W.getD j ∅ = A a ∪ A b ∨ W.getD j ∅ = A a ∩ A b ∨
            W.getD j ∅ = T \ A a) ∧
        ∀ x ∈ T, C.eval (List.ofFn x) = true ↔ x ∈ (V W.length).getD C.output ∅)
    (hLower :
      let T : Finset (Fin 9 → Bool) := Finset.univ
      let E : List ℕ := [1,12,23,34,40,5,16,27,38,57,68,85]
      ¬ ∃ (W : List (Finset (Fin 9 → Bool))) (o : ℕ),
        let V (j : ℕ) := (List.ofFn fun i : Fin 9 => T.filter (fun x => x i)) ++ W.take j
        W.length ≤ 14 ∧
        (∀ j < W.length, let A := fun i => (V j).getD i ∅
          ∃ a b : ℕ, W.getD j ∅ = A a ∪ A b ∨ W.getD j ∅ = A a ∩ A b ∨
            W.getD j ∅ = T \ A a) ∧
        ∀ x ∈ T, x ∈ (V W.length).getD o ∅ ↔
          ∃ e ∈ E, x (Fin.ofNat 9 (e / 10)) = true ∧ x (Fin.ofNat 9 (e % 10)) = true) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ) := by
  classical
  intro f h
  obtain ⟨C, hC, hSize, hEval⟩ := h
  let T : Finset (Fin 9 → Bool) := Finset.univ
  obtain ⟨W, hLength, hTrace, hValues⟩ := hExtract C T hC
  apply hLower
  refine ⟨W, C.output, by omega, hTrace, ?_⟩
  intro x hx
  rw [← hValues x hx, hEval x]
  simp only [f, List.any_eq_true, Bool.and_eq_true]
