import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_670_642
    (binary : ∀ (C : Circuit), FanInTwo C → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → 13 ≤ C.size - notCount C)
    (single : ∀ (C : Circuit), FanInTwo C → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → notCount C ≤ 1 → 16 ≤ C.size)
    (tight : ∀ (C : Circuit), FanInTwo C → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → notCount C = 2 → C.size - notCount C = 13 → False) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  rintro ⟨C, legal, small, computes⟩
  have agree (x : Fin 9 → Bool) : C.eval (List.ofFn x) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) := by
    simpa only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using computes x
  have b := binary C legal agree
  by_cases few : notCount C ≤ 1
  · have h := single C legal agree few
    omega
  · exact tight C legal agree (by omega) (by omega)
