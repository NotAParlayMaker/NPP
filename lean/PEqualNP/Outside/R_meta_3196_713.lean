import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3196_713
    (compile : ∀ (n : ℕ) (C : Circuit), FanInTwo C →
      (∃ i j : Fin C.gates.length, i < j ∧ (C.gates.get i).op = .not ∧ (C.gates.get j).op = .not) →
      ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length + 2 ≤ C.size ∧ ∀ x : Fin n → Bool,
        (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
          w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false = C.eval (List.ofFn x))
    (restrict : let can := fun (n : ℕ) (f : (Fin 9 → Bool) → Bool) =>
      ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ n ∧ ∀ x : Fin 9 → Bool,
        (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
          w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false = f x
      can 13 (fun x => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      can 10 (fun x => ([(1,2),(2,3),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)))
    (exclude : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 10 → ∃ x : Fin 9 → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
          w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false ≠ ([(1,2),(2,3),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (4 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C hc positions _ computes
  obtain ⟨i,j,lt,_,first,second,_⟩ := positions
  obtain ⟨p,o,size,hit⟩ := compile 9 C hc ⟨i,j,lt,first,second⟩
  by_contra! small
  obtain ⟨q,k,cap,yes⟩ := restrict ⟨p,o,by omega,fun x => by
    apply (hit x).trans
    have e := congrFun computes x
    change C.eval (List.ofFn x) = _ at e
    simpa only [List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] using e⟩
  obtain ⟨x,bad⟩ := exclude q k cap
  exact bad (yes x)
