import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2928_915
    (h1 : (let run := fun (input : Nat → Bool) (prog : List (Nat × Bool)) =>
        (prog.foldl (fun (ws : List Bool) u => if u.1 < 10 then (input u.1 ^^ u.2) :: ws
          else match ws with
            | x :: y :: rest => (if u.2 then x && y else x || y) :: rest
            | _ => []) []).headD false
      ∀ (p s : List (Nat × Bool)), p.length ≤ 9 → p.length + s.length ≤ 30 →
        ∃ z : BitVec 9, run (fun i => if i=9 then run z.getLsbD p else z.getLsbD i) s ≠ (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : Nat).testBit z.toNat))
    (h2 : (let run := fun (input : Nat → Bool) (prog : List (Nat × Bool)) =>
        (prog.foldl (fun (ws : List Bool) u => if u.1 < 10 then (input u.1 ^^ u.2) :: ws
          else match ws with
            | x :: y :: rest => (if u.2 then x && y else x || y) :: rest
            | _ => []) []).headD false
      let deep := fun (c : PEqualNP.CircuitLowerBounds.Circuit) =>
        let empty : Option Nat × List Nat := (none,[])
        let init := List.replicate 10 empty ++ [(some 10,[])]
        let w := c.gates.foldl (fun (ws : List (Option Nat × List Nat)) g =>
          let source := fun i : Nat => (ws.getD i empty).1
          let binary := match g.op, g.inputs with
            | .and, [_,_] | .or, [_,_] => true
            | _, _ => false
          ws ++ [if binary then (some ws.length, g.inputs.filterMap source)
                 else (source (g.inputs.headD ws.length),[])]) init
        let ps := fun j : Nat => (w.getD j empty).2
        let reach := fun j : Nat => (List.range w.length).foldl
          (fun (vs : List Nat) _ => (vs ++ vs.flatMap ps).eraseDups) [j]
        let live := ((w.getD c.output empty).1.toList).flatMap reach
        let uses := live.flatMap ps
        let shared := live.filter (fun j => decide (2 ≤ uses.count j))
        decide (2 ≤ shared.length) || shared.any (fun j => decide (5 ≤ (reach j).length))
      ∀ (a b : Fin 11) (c : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo c → c.size ≤ 13 →
      deep c = true ∨ ∃ (p s : List (Nat × Bool)), p.length ≤ 9 ∧ p.length + s.length ≤ 30 ∧
        ∀ z : BitVec 9, let x : Fin 9 → Bool := fun i : Fin 9 => z.getLsbD i.val
          run (fun i => if i=9 then run z.getLsbD p else z.getLsbD i) s = (let v := List.ofFn x ++ [!x 0]
        c.eval (v ++ [v.getD a.val false || v.getD b.val false]))))
    (h3 : (let deep := fun (c : PEqualNP.CircuitLowerBounds.Circuit) =>
        let empty : Option Nat × List Nat := (none,[])
        let init := List.replicate 10 empty ++ [(some 10,[])]
        let w := c.gates.foldl (fun (ws : List (Option Nat × List Nat)) g =>
          let source := fun i : Nat => (ws.getD i empty).1
          let binary := match g.op, g.inputs with
            | .and, [_,_] | .or, [_,_] => true
            | _, _ => false
          ws ++ [if binary then (some ws.length, g.inputs.filterMap source)
                 else (source (g.inputs.headD ws.length),[])]) init
        let ps := fun j : Nat => (w.getD j empty).2
        let reach := fun j : Nat => (List.range w.length).foldl
          (fun (vs : List Nat) _ => (vs ++ vs.flatMap ps).eraseDups) [j]
        let live := ((w.getD c.output empty).1.toList).flatMap reach
        let uses := live.flatMap ps
        let shared := live.filter (fun j => decide (2 ≤ uses.count j))
        decide (2 ≤ shared.length) || shared.any (fun j => decide (5 ≤ (reach j).length))
      ∀ (a b : Fin 11) (c : PEqualNP.CircuitLowerBounds.Circuit), a ≤ b → PEqualNP.MetaComplexity.FanInTwo c → c.size ≤ 13 → deep c = true →
      ∃ z : BitVec 9, let x : Fin 9 → Bool := fun i : Fin 9 => z.getLsbD i.val
        let v := List.ofFn x ++ [!x 0]
        c.eval (v ++ [v.getD a.val false || v.getD b.val false]) ≠ ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))) :
    ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 ≤ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2 := by
  intro a b c hab hf hc
  rcases h2 a b c hf hc with high | ⟨p,s,hp,hn,agree⟩
  · exact h3 a b c hab hf hc high
  obtain ⟨z, mismatch⟩ := h1 p s hp hn
  have table : ∀ u : BitVec 9, (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : Nat).testBit u.toNat =
      (let x : Fin 9 → Bool := fun i => u.getLsbD i.val
       ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) := by decide +kernel
  refine ⟨z, ?_⟩
  change (let x : Fin 9 → Bool := fun i => z.getLsbD i.val
          let v := List.ofFn x ++ [!x 0]
        c.eval (v ++ [v.getD a.val false || v.getD b.val false])) ≠
      (let x : Fin 9 → Bool := fun i => z.getLsbD i.val
       ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
  rw [← agree z, ← table z]
  exact mismatch
