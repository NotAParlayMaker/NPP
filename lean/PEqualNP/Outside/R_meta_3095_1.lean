import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3095_1
    (search :
      let E : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
      let target := fun x : Fin 9 → Bool => E.any fun p => x (Fin.ofNat 9 p.1) && x (Fin.ofNat 9 p.2)
      let Reader := fun (C : Circuit) (i : Fin 9) (s : Finset ℕ) =>
        ∀ r ∈ s, r < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x i = false → (C.wires (List.ofFn x)).getD (9 + r) false = b) ∨
           ∃ j < 9 + r, ∀ x : Fin 9 → Bool, x i = false → (C.wires (List.ofFn x)).getD (9 + r) false = (C.wires (List.ofFn x)).getD j false)
      let Bound := fun C : Circuit => ∀ (i : Fin 9) (s : Finset ℕ), Reader C i s →
        (i ∈ [(0 : Fin 9), 1, 2, 3, 5, 8] → s.card ≤ 3) ∧ (i ∈ [(4 : Fin 9), 6, 7] → s.card ≤ 2)
      let code := fun op : GateOp => match op with | GateOp.and => 0 | GateOp.or => 1 | GateOp.not => 2 | _ => 3
      let sw := fun i : ℕ => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 5 else if i = 5 then 2 else if i = 3 then 8 else if i = 8 then 3 else if i = 4 then 6 else if i = 6 then 4 else i
      let rk := fun g : Gate =>
        let a := g.inputs.headD 0
        let b := g.inputs.getD 1 a
        code g.op * 100 + min a b * 10 + max a b
      let rkS := fun g : Gate =>
        let a := sw (g.inputs.headD 0)
        let b := sw (g.inputs.getD 1 (g.inputs.headD 0))
        code g.op * 100 + min a b * 10 + max a b
      let Normal := fun C : Circuit => C.gates.length ≤ 1 ∨
        rk (C.gates.headD { op := GateOp.and, inputs := [] }) ≤ rkS (C.gates.headD { op := GateOp.and, inputs := [] })
      ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 15 ∧
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1)) ∧
        circuitFun 9 C = target ∧ Bound C ∧ Normal C)
    (normalize :
      let E : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
      let target := fun x : Fin 9 → Bool => E.any fun p => x (Fin.ofNat 9 p.1) && x (Fin.ofNat 9 p.2)
      let Reader := fun (C : Circuit) (i : Fin 9) (s : Finset ℕ) =>
        ∀ r ∈ s, r < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x i = false → (C.wires (List.ofFn x)).getD (9 + r) false = b) ∨
           ∃ j < 9 + r, ∀ x : Fin 9 → Bool, x i = false → (C.wires (List.ofFn x)).getD (9 + r) false = (C.wires (List.ofFn x)).getD j false)
      let Bound := fun C : Circuit => ∀ (i : Fin 9) (s : Finset ℕ), Reader C i s →
        (i ∈ [(0 : Fin 9), 1, 2, 3, 5, 8] → s.card ≤ 3) ∧ (i ∈ [(4 : Fin 9), 6, 7] → s.card ≤ 2)
      let code := fun op : GateOp => match op with | GateOp.and => 0 | GateOp.or => 1 | GateOp.not => 2 | _ => 3
      let sw := fun i : ℕ => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 5 else if i = 5 then 2 else if i = 3 then 8 else if i = 8 then 3 else if i = 4 then 6 else if i = 6 then 4 else i
      let rk := fun g : Gate =>
        let a := g.inputs.headD 0
        let b := g.inputs.getD 1 a
        code g.op * 100 + min a b * 10 + max a b
      let rkS := fun g : Gate =>
        let a := sw (g.inputs.headD 0)
        let b := sw (g.inputs.getD 1 (g.inputs.headD 0))
        code g.op * 100 + min a b * 10 + max a b
      let Normal := fun C : Circuit => C.gates.length ≤ 1 ∨
        rk (C.gates.headD { op := GateOp.and, inputs := [] }) ≤ rkS (C.gates.headD { op := GateOp.and, inputs := [] })
      ∀ C : Circuit, FanInTwo C →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1)) →
        circuitFun 9 C = target → Bound C →
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 1)) ∧
          circuitFun 9 D = target ∧ Bound D ∧ Normal D) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin (9 : ℕ)) (x6 : Finset ℕ), (∀ x7 ∈ x6, x7 < x1.size ∧ ((∃ (x9 : Bool), ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = x9) ∨ ∃ x9 < (9 : ℕ) + x7, ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = (x1.wires (List.ofFn x10)).getD x9 Bool.false)) → (x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))] → x6.card ≤ (3 : ℕ)) ∧ (x5 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))] → x6.card ≤ (2 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan wire computes readers
  dsimp at search normalize
  by_contra hsmall
  have hle : C.size ≤ 15 := by omega
  obtain ⟨D, dfan, dsize, dwire, dcomputes, dreaders, dnorm⟩ := normalize C fan wire computes readers
  apply search
  refine ⟨D, dfan, ?_, dwire, dcomputes, dreaders, dnorm⟩
  omega
