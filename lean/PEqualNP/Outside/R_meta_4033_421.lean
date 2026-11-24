import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4033_421
    (normalize :
      let f := fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ (C : Circuit), FanInTwo C → (∀ x, C.eval (List.ofFn x) = f x) →
      ∃ (gs : List Gate) (op : GateOp) (a b : ℕ),
        gs.length + 1 ≤ C.size ∧ FanInTwo ⟨gs, 0⟩ ∧
        9 ≤ a ∧ a < 9 + gs.length ∧ 9 ≤ b ∧ b < 9 + gs.length ∧
        (op = .not ∨ a ≠ b ∧ (op = .and ∨ op = .or)) ∧
        ∀ x : Fin 9 → Bool,
          let w := (Circuit.mk gs 0).wires (List.ofFn x)
          op.eval [w.getD a false, w.getD b false] = f x)
    (remaining :
      let f := fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (gs : List Gate) (op : GateOp) (a b : ℕ), gs.length ≤ 14 → FanInTwo ⟨gs, 0⟩ →
        9 ≤ a → a < 9 + gs.length → 9 ≤ b → b < 9 + gs.length →
        (op = .not ∨ a ≠ b ∧ (op = .and ∨ op = .or)) →
        ∃ x : Fin 9 → Bool,
          let w := (Circuit.mk gs 0).wires (List.ofFn x)
          op.eval [w.getD a false, w.getD b false] ≠ f x) :
    ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))) (15 : ℕ) := by
  rintro ⟨C, legal, small, computes⟩
  let f := fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have encoding (x : Fin 9 → Bool) : f x = (fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))) x := by
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  have hFit (x : Fin 9 → Bool) : C.eval (List.ofFn x) = f x :=
    (computes x).trans (encoding x).symm
  obtain ⟨gs, op, a, b, hSize, hLegal, ha, ha', hb, hb', hOp, eval⟩ :=
    normalize C legal hFit
  obtain ⟨x, differing⟩ := remaining gs op a b (by omega) hLegal ha ha' hb hb' hOp
  exact differing (eval x)

