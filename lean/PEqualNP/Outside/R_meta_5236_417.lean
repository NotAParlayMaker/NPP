import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

-- A false pin of either endpoint of the given OR turns that wire into an alias.
-- The nine-vertex bound then requires the entire eighteen-gate budget, with exactly
-- three NOT gates and at most one paid gate reading each of the two raw endpoints.
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_5236_417
    (nineFloor :
      let target9 := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (ℕ × ℕ)).any
        (fun e => x (Fin.ofNat 9 e.1) && x (Fin.ofNat 9 e.2));
      let paid := fun (D : Circuit) => D.size - notCount D;
      ∀ D : Circuit, FanInTwo D → (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = target9 x) → 14 ≤ paid D)
    (pinCost :
      let target10 := fun (x : Fin 10 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (ℕ × ℕ)).any
        (fun e => x (Fin.ofNat 10 e.1) && x (Fin.ofNat 10 e.2));
      let target9 := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (ℕ × ℕ)).any
        (fun e => x (Fin.ofNat 9 e.1) && x (Fin.ofNat 9 e.2));
      let paid := fun (D : Circuit) => D.size - notCount D;
      let reads := fun (C : Circuit) (p : ℕ) => C.gates.countP (fun g =>
        (notCount ⟨[g],0⟩ == 0) && g.inputs.contains p);
      ∀ C : Circuit, FanInTwo C → (∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) = target10 x) →
        ∀ p : Bool, ∃ D : Circuit, FanInTwo D ∧ paid D < paid C ∧
        paid D + reads C (if p then 2 else 0) ≤ paid C ∧
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = target9 x)
    (tightCase :
      let target := fun (x : Fin 10 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (ℕ × ℕ)).any
        (fun e => x (Fin.ofNat 10 e.1) && x (Fin.ofNat 10 e.2));
      let reads := fun (C : Circuit) (p : ℕ) => C.gates.countP (fun g =>
        (notCount ⟨[g],0⟩ == 0) && g.inputs.contains p);
      ∀ C : Circuit, FanInTwo C → ReadsBack 11 C → C.size = 18 → 11 ≤ C.output →
        C.output < 11 + C.size → notCount C = 3 → reads C 0 ≤ 1 → reads C 2 ≤ 1 →
        ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠ target x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → (3 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (4 : ℕ) → ∃ (x9 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x9 ++ [x9 (0 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ))]) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))) := by
  intro C fan back size output1 output2 not1 _
  by_contra! fit
  let target := fun (x : Fin 10 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (ℕ × ℕ)).any
        (fun e => x (Fin.ofNat 10 e.1) && x (Fin.ofNat 10 e.2))
  have fitList (x : Fin 10 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 2]) = target x := by
    have h := fit x
    simpa [target,Fin.ofNat,Bool.or_assoc] using h
  obtain ⟨A,hA,smallA,used0,evA⟩ := pinCost C fan fitList false
  obtain ⟨B,hB,_,used2,evB⟩ := pinCost C fan fitList true
  have a := nineFloor A hA evA
  have b := nineFloor B hB evB
  change 14 ≤ A.size - notCount A at a
  change 14 ≤ B.size - notCount B at b
  change A.size - notCount A < C.size - notCount C at smallA
  have lower : 15 ≤ C.size - notCount C := by omega
  have sizeOK : C.size = 18 := by omega
  have notOK : notCount C = 3 := by omega
  let reads := fun (C : Circuit) (p : ℕ) => C.gates.countP (fun g =>
        (notCount ⟨[g],0⟩ == 0) && g.inputs.contains p)
  change A.size - notCount A + reads C 0 ≤ C.size - notCount C at used0
  change B.size - notCount B + reads C 2 ≤ C.size - notCount C at used2
  have one0 : reads C 0 ≤ 1 := by omega
  have one2 : reads C 2 ≤ 1 := by omega
  obtain ⟨x,mismatch⟩ := tightCase C fan back sizeOK output1 output2 notOK one0 one2
  exact mismatch (fitList x)
