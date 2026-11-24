import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1342_713
    (assemble : ∀ (P : Fin 4 → Circuit) (a : Fin 3 → List ℕ),
      (∀ i, Monotone2 (P i)) → (∀ i, (a i).length ≤ 2) →
      ∃ C : Circuit, Monotone2 C ∧ C.size = (∑ i, (P i).size) + 3 ∧
      let w := fun (xs : List Bool) (k : ℕ) => ((List.finRange 3).take k).foldl (fun ws i =>
        let vs := (P i.castSucc).wires ws
        vs ++ [(a i).all (fun j => vs.getD j false)]) xs
      ∀ xs, C.eval xs = (P 3).eval (w xs 3))
    (search : ∃ (P : Fin 4 → Circuit) (a : Fin 3 → List ℕ),
      (∀ i, Monotone2 (P i)) ∧ (∀ i, (a i).length ≤ 2) ∧ (∑ i, (P i).size) ≤ 18 ∧
      4 ≤ (∑ i, (P i).gates.countP (fun g => !(g.op.eval [false,true]))) ∧
      let w := fun (xs : List Bool) (k : ℕ) => ((List.finRange 3).take k).foldl (fun ws i =>
        let vs := (P i.castSucc).wires ws
        vs ++ [(a i).all (fun j => vs.getD j false)]) xs
      let out := fun x : Fin 11 → Bool => (P 3).eval (w (List.ofFn x) 3)
      (∀ i : Fin 3, ∃ x : Fin 11 → Bool, (w (List.ofFn x) (i.val+1)).getLast? = some true ∧ out x = false) ∧
      ∀ x, out x = true ↔ ∃ u v : Fin 11, (([1536,272,1056,192,1280,768,1152,512,512,0,0] : List ℕ).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin 11 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧ C.size ≤ 21 := by
  obtain ⟨P,a,mp,arity,lim,_andCount,_dirty,model⟩ := search
  obtain ⟨C,mc,size,eval⟩ := assemble P a mp arity
  refine ⟨C,mc,?_,by omega⟩
  have bits : ∀ u v : Fin 11, (([1536,272,1056,192,1280,768,1152,512,512,0,0] : List ℕ).getD u.val 0).testBit v.val = true ↔
      (u.val,v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) := by decide +kernel
  intro x
  rw [eval]
  simpa only [bits] using model x
