import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each encoded row lists the ten inputs in its low bits. Bit ten gives the desired output.
-- The first two premises force a fourteen-gate monotone suffix and its two additional test rows.
theorem PEqualNP.Outside.R_meta_2311_236
    (shape :
      let edges := fun (y : Fin 9 → Bool) =>
        ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any
          (fun n => y (Fin.ofNat 9 (n / 9)) && y (Fin.ofNat 9 (n % 9)))
      ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !y 0) →
      circuitFun 9 C = edges → C.size≤15 → ∃ D : Circuit, D.gates=C.gates.drop 1 ∧ D.size=14 ∧
        FanInTwo D ∧ (∀ g ∈ D.gates, g.op=.and ∨ g.op=.or) ∧ ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0]) = edges x)
    (faces :
      let edges := fun (y : Fin 9 → Bool) =>
        ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any
          (fun n => y (Fin.ofNat 9 (n / 9)) && y (Fin.ofNat 9 (n % 9)))
      let input := fun (r : Nat) => List.ofFn (fun j : Fin 10 => r.testBit j.val)
      ∀ D : Circuit, FanInTwo D → D.size≤14 → (∀ g ∈ D.gates, g.op=.and ∨ g.op=.or) →
        (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0]) = edges x) →
        (∃ r ∈ ([6,12,24,66,132,160,264,288,320] : List Nat), D.eval (input r)=false) ∧
        (∃ r ∈ ([581,713,773,897] : List Nat), D.eval (input r)=true))
    (search :
      let input := fun (r : Nat) => List.ofFn (fun j : Fin 10 => r.testBit j.val)
      let reads := fun g : Gate => ([0,9] : List Nat).any (fun i => g.inputs.contains i)
      ∀ D : Circuit, FanInTwo D → D.size=14 → (∀ g ∈ D.gates, g.op=.and ∨ g.op=.or) → (D.gates.filter reads).length=2 →
        (¬ ∃ (P : List Gate) (g : Gate) (R : List Gate), D.gates=P++g::R ∧
          (g.op=.and ∧ 0∈g.inputs ∨ g.op=.or ∧ 9∈g.inputs) ∧
          ∃ h ∈ R, reads h=false ∧ 10+P.length ∈ h.inputs) →
        (∀ r ∈ ([1542,1548,1560,1602,1668,1696,1800,1824,1856,554,562,616,628,650,712,720,788,914,1027,1037,1041,1057,1157,1289,1345,69,201,261,385] : List Nat), D.eval (input r)=r.testBit 10) →
        (∃ r ∈ ([6,12,24,66,132,160,264,288,320] : List Nat), D.eval (input r)=false) →
        (∃ r ∈ ([581,713,773,897] : List Nat), D.eval (input r)=true) → False) : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => { op := x3.op, inputs := if x3.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x2.gates);   have x4 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5;   have x5 : ℕ := (List.filter x4 x3).length;   have x6 : Prop := ∃ (x6 : List PEqualNP.CircuitLowerBounds.Gate) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 : List PEqualNP.CircuitLowerBounds.Gate), x3 = x6 ++ x7 :: x8 ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x7.inputs ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x7.inputs) ∧ ∃ x9 ∈ x8, x4 x9 = Bool.false ∧ (10 : ℕ) + x6.length ∈ x9.inputs;   PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x8 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x8)).getD (9 : ℕ) Bool.false = !x8 (0 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → x5 = (2 : ℕ) → ¬x6 → False := by
  dsimp only
  intro C fan first works cap count noCascade
  let edge := fun (x : Fin 9 → Bool) => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let edges := fun (y : Fin 9 → Bool) =>
      ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any
        (fun n => y (Fin.ofNat 9 (n / 9)) && y (Fin.ofNat 9 (n % 9)))
  have codes : edges = edge := by
    funext y
    simp [edges,edge,List.any,Bool.or_assoc,Fin.ofNat]
  obtain ⟨D,gates,sz,legal,ops,correct⟩ := shape C fan first (works.trans codes.symm) cap
  obtain ⟨lo,hi⟩ := faces D legal (by omega) ops correct
  let norm := fun (g : Gate) => ({op:=g.op, inputs:=if g.op.eval [false]=true then g.inputs.take 1 else g.inputs} : Gate)
  have normed : (C.gates.drop 1).map norm=D.gates := by
    rw [←gates]
    refine (List.map_congr_left (g:=id) ?_).trans (List.map_id _)
    intro g hg
    obtain ⟨op,ins⟩ := g
    rcases ops _ hg with eq|eq <;> change op=_ at eq <;> subst op <;> rfl
  apply search D legal sz ops
  · rw [←normed]; exact count
  · rw [←normed]; exact noCascade
  · let x := fun (r : Nat) (j : Fin 9) => r.testBit j.val
    let data := ([1542,1548,1560,1602,1668,1696,1800,1824,1856,554,562,616,628,650,712,720,788,914,1027,1037,1041,1057,1157,1289,1345,69,201,261,385] : List Nat)
    have tab : data.all (fun r =>
        decide (List.ofFn (fun j : Fin 10 => r.testBit j.val) = List.ofFn (x r) ++ [!x r 0]) &&
        (edge (x r) == r.testBit 10)) = true := by decide +kernel
    intro r hr
    obtain ⟨same,out⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp tab r hr)
    exact (congrArg D.eval (of_decide_eq_true same)).trans ((correct (x r)).trans ((congrFun codes _).trans (beq_iff_eq.mp out)))
  · exact lo
  · exact hi
