import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3233_915
    (h0 : let F := fun (x : Fin 9 → Bool) => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun e : Nat => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))); ¬∃ d : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo d ∧ d.size ≤ 14 ∧ PEqualNP.MetaComplexity.circuitFun 9 d = F)
    (h1 : let norm := fun (x : Fin 9 → Bool) (p : List (Bool × Nat × Nat)) (t : List (Nat × Nat)) =>
        let w := p.foldl (fun (xs : List Bool) g =>
          let a := xs.getD g.2.1 false
          let b := xs.getD g.2.2 false
          xs ++ [if g.1 then a && b else a || b]) (List.ofFn x ++ [x 4 || x 6])
        t.any (fun b => w.getD b.1 false && w.getD b.2 false)
      let F := fun (x : Fin 9 → Bool) => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun e : Nat => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))); ∀ (p : List (Bool × Nat × Nat)) (t : List (Nat × Nat)), (p.head?.map Prod.fst = some false) ∧ p.countP Prod.fst ≤ 1 ∧ p.length + 2*t.length ≤ 15 →
        ∃ x, norm x p t ≠ F x)
    (h2 : let norm := fun (x : Fin 9 → Bool) (p : List (Bool × Nat × Nat)) (t : List (Nat × Nat)) =>
        let w := p.foldl (fun (xs : List Bool) g =>
          let a := xs.getD g.2.1 false
          let b := xs.getD g.2.2 false
          xs ++ [if g.1 then a && b else a || b]) (List.ofFn x ++ [x 4 || x 6])
        t.any (fun b => w.getD b.1 false && w.getD b.2 false)
      ∀ (c : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 c → c.size ≤ 15 →
        (∀ d : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo d → d.size < c.size → PEqualNP.MetaComplexity.circuitFun 9 d ≠ PEqualNP.MetaComplexity.circuitFun 9 c) →
        (∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) → (c.gates[1]?.map (fun g => g.op.eval [true,false])) = some true →
        (∀ i : Fin 9, PEqualNP.MetaComplexity.circuitFun 9 c (fun j => decide (j=i)) = false) →
        let bad := fun j : Nat => (c.gates[j]?.map (fun g => g.op.eval [true,false])) = some false ∧ ∃ x : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 c x = false ∧ (c.wires (List.ofFn x)).getD (9+j) false = true; ¬(∃ j k, j ≠ k ∧ bad j ∧ bad k) →
        ∃ p t, ((p.head?.map Prod.fst = some false) ∧ p.countP Prod.fst ≤ 1 ∧ p.length + 2*t.length ≤ 15) ∧ ∀ x, norm x p t = PEqualNP.MetaComplexity.circuitFun 9 c x)
    (h3 : let F := fun (x : Fin 9 → Bool) => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun e : Nat => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))); ∀ (c : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo c → (∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) → PEqualNP.MetaComplexity.circuitFun 9 c = F →
        ∀ g, c.gates[1]? = some g → g.op = .or →
        g.inputs ≤ g.inputs.map (fun i => ([1,0,5,8,6,2,4,7,3] : List Nat).getD i i) →
        let bad := fun j : Nat => (c.gates[j]?.map (fun g => g.op.eval [true,false])) = some false ∧ ∃ x : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 c x = false ∧ (c.wires (List.ofFn x)).getD (9+j) false = true; ((¬PEqualNP.MetaComplexity.Monotone2 c) ∨ (∃ j k, j ≠ k ∧ bad j ∧ bad k)) → 16 ≤ c.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5.inputs ≤ List.map (fun (x8 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x8 x8) x5.inputs → (16 : ℕ) ≤ x1.size := by
  intro c hf first correct g hg hop lex
  let F := fun (x : Fin 9 → Bool) => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun e : Nat => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)))
  have eqF : PEqualNP.MetaComplexity.circuitFun 9 c = F := by
    rw [correct]
    funext x
    simp [F, List.any_cons, Bool.or_assoc]
    rfl
  let bad := fun j : Nat => (c.gates[j]?.map (fun g => g.op.eval [true,false])) = some false ∧ ∃ x : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 c x = false ∧ (c.wires (List.ofFn x)).getD (9+j) false = true
  by_cases hard : (¬PEqualNP.MetaComplexity.Monotone2 c) ∨ (∃ j k, j ≠ k ∧ bad j ∧ bad k)
  · exact h3 c hf first eqF g hg hop lex hard
  classical
  by_contra! small
  have hm : PEqualNP.MetaComplexity.Monotone2 c := by by_contra hn; exact hard (Or.inl hn)
  have minC (d : PEqualNP.CircuitLowerBounds.Circuit) (hd : PEqualNP.MetaComplexity.FanInTwo d) (hs : d.size < c.size) : PEqualNP.MetaComplexity.circuitFun 9 d ≠ PEqualNP.MetaComplexity.circuitFun 9 c := by
    intro h
    exact h0 ⟨d, hd, by omega, h.trans eqF⟩
  have noOne : ∀ i : Fin 9, PEqualNP.MetaComplexity.circuitFun 9 c (fun j => decide (j=i)) = false := by
    rw [eqF]
    decide +kernel
  have hg' : (c.gates[1]?.map (fun g => g.op.eval [true,false])) = some true := by rw [hg]; simp [hop, PEqualNP.CircuitLowerBounds.GateOp.eval]
  obtain ⟨p,t,hpts,agree⟩ := h2 c hm (by omega) minC first hg' noOne (fun h => hard (Or.inr h))
  obtain ⟨x,diff⟩ := h1 p t hpts
  exact diff ((agree x).trans (congrFun eqF x))
