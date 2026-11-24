import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3283_713
    (normal : ∀ (n : ℕ) (C : Circuit) (_hc : FanInTwo C),
    (∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length < C.size ∧ ∀ x : Fin n → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false =
      circuitFun n C x)
    (signed : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 13 → ∃ x : Fin 9 → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false ≠
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
    (pack : ∀ (C : Circuit) (_h : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2),
    ∃ p : List (Bool × ℕ × ℕ), p.length = C.size ∧ ∀ (s : List ℕ) (i : ℕ),
      ((p.foldl (fun w g =>
        let a := w.getD g.2.1 0
        let b := w.getD g.2.2 0
        w ++ [ite (g.1 = true) (a ||| b) (a &&& b)]) s).getD C.output 0).testBit i =
      C.eval (s.map fun u => u.testBit i))
    (boundary : ∀ (p : List (Bool × ℕ × ℕ)) (o : ℕ), p.length ≤ 14 →
      ∃ j : Fin 24, ((p.foldl (fun w g =>
        let a := w.getD g.2.1 0
        let b := w.getD g.2.2 0
        w ++ [ite (g.1 = true) (a ||| b) (a &&& b)]) ([5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968] : List ℕ)).getD o 0).testBit j.val ≠ decide (j.val < 12)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x4 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x3 x4.1 && x3 x4.2) → (15 : ℕ) ≤ x1.size := by
  let graph := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  intro C hc computes
  change circuitFun 9 C = graph at computes
  by_contra! small
  rcases normal 9 C hc with ordinary | ⟨p,o,budget,agrees⟩
  · obtain ⟨p,len,simulate⟩ := pack C ordinary
    let masks : List ℕ := [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968]
    obtain ⟨j,miss⟩ := boundary p C.output (by omega)
    let x := fun v : Fin 9 => (masks.getD v.val 0).testBit j.val
    have inputs : masks.map (fun u => u.testBit j.val) = List.ofFn x := rfl
    have target : ∀ k : Fin 24, graph (fun v => (masks.getD v.val 0).testBit k.val) = decide (k.val < 12) := by decide
    apply miss
    have run := simulate masks j.val
    rw [inputs] at run
    exact run.trans ((congrFun computes x).trans (target j))
  · obtain ⟨x,miss⟩ := signed p o (by omega)
    apply miss
    exact (agrees x).trans (congrFun computes x)
