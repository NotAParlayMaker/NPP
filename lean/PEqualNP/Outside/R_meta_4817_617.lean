import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_4817_617
   (binary : ∀ (C : Circuit) (s : Fin 12), FanInTwo C →
    (∀x : Fin 10→Bool,let z:=List.ofFn x++[x 0 && x 2]
     C.eval (z++[!z.getD s.val false])=([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any
        (fun e=>x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e % 10)))) →
    16≤C.gates.countP (fun g=>g.inputs.length==2 && GateOp.rec true true false (fun _=>false) false g.op))
   (readers : ∀ (C : Circuit) (s : Fin 12), FanInTwo C →
    (∀x : Fin 10→Bool,let z:=List.ofFn x++[x 0 && x 2]
     C.eval (z++[!z.getD s.val false])=([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any
        (fun e=>x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e % 10)))) →
    15+C.gates.countP (fun g=>(GateOp.rec true true false (fun _=>false) false g.op) &&
        g.inputs.any (fun i=> i==10 || (i==11 && decide (10≤s.val))))+PEqualNP.NotBracket.notCount C≤C.size)
   (mono : ∀(C : Circuit) (s : Fin 12), Monotone2 C → 16≤C.size → C.size≤17 →
    C.gates.countP (fun g=>(GateOp.rec true true false (fun _=>false) false g.op) &&
        g.inputs.any (fun i=> i==10 || (i==11 && decide (10≤s.val))))≤C.size-15 → ∃x : Fin 10→Bool,let z:=List.ofFn x++[x 0 && x 2]
     C.eval (z++[!z.getD s.val false])≠([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any
        (fun e=>x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e % 10))))
   (one : ∀(C : Circuit) (s : Fin 12), FanInTwo C → C.size=17 → PEqualNP.NotBracket.notCount C=1 →
    C.gates.countP (fun g=>g.inputs.length==2 && GateOp.rec true true false (fun _=>false) false g.op)=16 → C.gates.countP (fun g=>(GateOp.rec true true false (fun _=>false) false g.op) &&
        g.inputs.any (fun i=> i==10 || (i==11 && decide (10≤s.val))))≤1 →
    ∃x : Fin 10→Bool,let z:=List.ofFn x++[x 0 && x 2]
     C.eval (z++[!z.getD s.val false])≠([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any
        (fun e=>x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e % 10)))) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       ∃ (x5 : Fin (10 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];         x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5 := by
 let target:=fun x : Fin 10→Bool=>([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any
        (fun e=>x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e % 10)))
 have agree : ∀ x : Fin 10→Bool,target x=(x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by decide +kernel
 let proper := fun g : Gate=>g.inputs.length==2 && GateOp.rec true true false (fun _=>false) false g.op
 let inv : Gate→Bool := fun g : Gate=>GateOp.rec false false true (fun _=>false) false g.op
 have balance (gs : List Gate) : gs.countP proper + gs.countP inv ≤ gs.length := by
   induction gs with
   | nil =>rfl
   | cons g gs ih =>
     have disjoint : ¬(proper g=true ∧ inv g=true) := by
       obtain ⟨o,ins⟩:=g
       cases o <;> simp [proper,inv]
     simp only [List.countP_cons,List.length_cons]
     cases h : proper g <;> cases e : inv g <;> simp [h,e] at disjoint ⊢ <;> omega
 intro C s fan size
 by_contra no
 push Not at no
 have correct (x : Fin 10→Bool) : (let z:=List.ofFn x++[x 0 && x 2]
     C.eval (z++[!z.getD s.val false]))=target x := (Classical.byContradiction (no x)).trans (agree x).symm
 have pb:=binary C s fan correct
 have rd:=readers C s fan correct
 have ni : PEqualNP.NotBracket.notCount C=C.gates.countP inv := by
   unfold PEqualNP.NotBracket.notCount
   rw [List.countP_eq_length_filter]
   congr 2
   funext g
   dsimp only [inv]
   cases g.op <;> rfl
 have bal:=balance C.gates
 change C.gates.countP proper+C.gates.countP inv≤C.size at bal
 change 16≤C.gates.countP proper at pb
 by_cases z : PEqualNP.NotBracket.notCount C=0
 · have mt : Monotone2 C := by
     intro g hg
     obtain ⟨ops,arity⟩:=fan g hg
     refine ⟨?_,arity⟩
     have ng : g.op≠.not := by
       intro ng
       have pos:=List.countP_pos_iff.mpr (show ∃v∈C.gates,inv v=true from ⟨g,hg,by dsimp only [inv];rw [ng]⟩)
       omega
     exact ops.elim Or.inl (fun p=>p.elim Or.inr (fun n=>(ng n).elim))
   obtain ⟨x,fail⟩:=mono C s mt (by omega) size (by omega)
   exact fail (correct x)
 · obtain ⟨x,fail⟩:=one C s fan (by omega) (by omega) (by change C.gates.countP proper=16;omega) (by omega)
   exact fail (correct x)
