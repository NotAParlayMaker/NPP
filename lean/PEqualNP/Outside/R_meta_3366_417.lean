import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_3366_417
    (readNeeded :
      ∀ (C : Circuit) (a b : List Bool) (i j : ℕ) (v : Bool),
        FanInTwo C → a.length = b.length → j < a.length →
        a.getD j false = v → b.getD j false = v → C.output ≠ i →
        (∀ k ≠ i, a.getD k false = b.getD k false) → C.eval a ≠ C.eval b →
        ∃ g ∈ C.gates,
          i ∈ (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs) ∧
          ¬(g.op = (if v then GateOp.or else GateOp.and) ∧ j ∈ g.inputs))
    (residual :
      let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
        (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      let pairs : List (ℕ × ℕ × Bool) := [(3,10,true),(4,9,true),(9,4,false),(10,3,false)]
      ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn (Function.update x 0 false) ++
          [x 0 || x 4, x 0 || x 3]) = f x) →
        (∀ p ∈ pairs, ∃ g ∈ C.gates,
          p.1 ∈ (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs) ∧
          ¬(g.op = (if p.2.2 then GateOp.or else GateOp.and) ∧ p.2.1 ∈ g.inputs)) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x1 x5) → False := by
  dsimp only
  intro C fan budget computes
  let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
    (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let base (x : Fin 9 → Bool) := List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]
  let row (mask : ℕ) (i : Fin 9) := mask.testBit i.val
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have len (x : Fin 9 → Bool) : (base x).length = 11 := by simp [base]
  have acceptingA : f (row 3) = true := by dsimp [f,row]; decide +kernel
  have acceptingB : f (row 132) = true := by dsimp [f,row]; decide +kernel
  have disjoint : ∀ i : Fin 11,
      (base (row 3)).getD i.val false = false ∨ (base (row 132)).getD i.val false = false := by
    dsimp [base,row]
    decide +kernel
  have out (i : ℕ) (hi : i < 11) : C.output ≠ i := by
    intro h
    have val (x : Fin 9 → Bool) : C.eval (base x) = (base x).getD i false := by
      change (C.gates.foldl step (base x)).getD C.output false = _
      rw [h, keep _ _ _ (by rwa [len])]
    have check (mask : ℕ) (yes : f (row mask) = true) (no : (base (row mask)).getD i false = false) :
        False := by
      have eq := computes (row mask)
      change C.eval (base (row mask)) = f (row mask) at eq
      rw [val, yes, no] at eq
      cases eq
    rcases disjoint ⟨i,hi⟩ with ha | hb
    · exact check 3 acceptingA ha
    · exact check 132 acceptingB hb
  let pairs : List (ℕ × ℕ × Bool) := [(3,10,true),(4,9,true),(9,4,false),(10,3,false)]
  let pair (k : Fin 4) : ℕ × ℕ × Bool := pairs[k.val]'(by exact k.isLt)
  let a (k : Fin 4) : Fin 9 → Bool := row ([5,1,10,16].getD k.val 0)
  let b (k : Fin 4) : Fin 9 → Bool := row ([13,17,11,17].getD k.val 0)
  have witnesses : ∀ k : Fin 4,
      (pair k).1 < 11 ∧ (pair k).2.1 < 11 ∧
      (base (a k)).getD (pair k).2.1 false = (pair k).2.2 ∧
      (base (b k)).getD (pair k).2.1 false = (pair k).2.2 ∧
      f (a k) = false ∧ f (b k) = true ∧
      ∀ t : Fin 11, t.val ≠ (pair k).1 → (base (a k)).getD t.val false = (base (b k)).getD t.val false := by
    dsimp [pair,pairs,a,b,row,base,f]
    decide +kernel
  apply residual C fan budget computes
  intro p hp
  have index : ∃ k : Fin 4, pair k = p := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with h | h | h | h
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
    · exact ⟨3,h.symm⟩
  obtain ⟨k,rfl⟩ := index
  obtain ⟨ile,jle,ja,jb,fa,fb,agree⟩ := witnesses k
  apply readNeeded C (base (a k)) (base (b k)) (pair k).1 (pair k).2.1 (pair k).2.2
    fan (by rw [len,len]) (by rwa [len]) ja jb (out _ ile)
  · intro t ht
    by_cases live : t < 11
    · exact agree ⟨t,live⟩ ht
    · rw [List.getD_eq_default _ _ (by rw [len]; omega),
        List.getD_eq_default _ _ (by rw [len]; omega)]
  · intro eq
    have ca := computes (a k)
    have cb := computes (b k)
    change C.eval (base (a k)) = f (a k) at ca
    change C.eval (base (b k)) = f (b k) at cb
    rw [eq, cb, fa, fb] at ca
    cases ca
