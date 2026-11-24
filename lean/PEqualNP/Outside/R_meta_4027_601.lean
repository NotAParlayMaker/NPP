import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4027_601
    (boundary : ∀ (n : ℕ) (C : Circuit) (edge : Fin n → Fin n → Prop),
      let hit (x : Fin (n+n) → Bool) :=
        ∃ p l, edge p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true
      (∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) →
      (∀ p l, edge p l → C.eval (List.ofFn fun k : Fin (n+n) =>
        decide (k = Fin.castAdd n p ∨ k = Fin.natAdd n l)) = true) →
      (∀ x, Maximal (fun z => ¬ hit z) x → C.eval (List.ofFn x) = false) →
      ∀ x, C.eval (List.ofFn x) = true ↔ hit x)
    (suffix :
      let edge (p l : Fin 13) := l ≠ 1 ∧ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9)
      let hit (x : Fin 26 → Bool) :=
        ∃ p l, edge p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      let vals (x : Fin 26 → Bool) := List.ofFn x ++ [x 1 || x 2]
      ∃ D : Circuit, D.size ≤ 58 ∧ 27 ≤ D.output ∧ D.output < 27 + D.size ∧
        PEqualNP.TopForm.IsAO2 27 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        (∀ p l, edge p l → D.eval (vals fun k => decide
          (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)) = true) ∧
        ∀ x, Maximal (fun z => ¬ hit z) x → D.eval (vals x) = false) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), x1.size ≤ (59 : ℕ) ∧ (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size ∧ (26 : ℕ) ≤ x2 ∧ x2 < (26 : ℕ) + x1.size ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) ∧ (∀ (x3 : Fin (26 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (1 : Fin (26 : ℕ)) || x3 (2 : Fin (26 : ℕ)))) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x5 ≠ (1 : Fin (13 : ℕ)) ∧ (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true := by
  let appendGate (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have earlierWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl appendGate w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (appendGate w g) (by simp [appendGate]; omega)]
      simp [appendGate, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  obtain ⟨D, hsize, hout, hupper, hao, hdistinct, hpos, hneg⟩ := suffix
  let seed : Gate := ⟨.or, [1, 2]⟩
  let C : Circuit := ⟨seed :: D.gates, D.output⟩
  have cs : C.size = D.size + 1 := rfl
  have co : C.output = D.output := rfl
  have legal : ∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j := by
    intro j g hg
    cases j with
    | zero =>
      have h : seed = g := by simpa [C] using hg
      subst g
      exact ⟨Or.inr rfl, 1, 2, rfl, by decide, by decide, by decide⟩
    | succ j =>
      have lookup : D.gates[j]? = some g := by simpa [C] using hg
      have hmem := List.mem_iff_getElem?.2 ⟨j, lookup⟩
      obtain ⟨a,b,inputs⟩ := List.length_eq_two.mp (hao.2.2 g hmem)
      have back := hao.2.1 j (List.getElem?_eq_some_iff.1 lookup).1
      have same : gateAt D j = g := by simp [gateAt, List.getD_eq_getElem?_getD, lookup]
      rw [same, inputs] at back
      have ha := back a (by simp)
      have hb := back b (by simp)
      exact ⟨hao.1 g hmem, a, b, inputs, by simpa [inputs] using hdistinct g hmem,
        by omega, by omega⟩
  have seedStep (x : Fin 26 → Bool) :
      appendGate (List.ofFn x) seed = List.ofFn x ++ [x 1 || x 2] := by
    simp [appendGate, seed, GateOp.eval, List.getD_eq_getElem?_getD]
  have readSeed (x : Fin 26 → Bool) : (C.wires (List.ofFn x)).getD 26 false = (x 1 || x 2) := by
    change (D.gates.foldl appendGate (appendGate (List.ofFn x) seed)).getD 26 false = _
    rw [seedStep, earlierWire _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have sameEval (x : Fin 26 → Bool) :
      C.eval (List.ofFn x) = D.eval (List.ofFn x ++ [x 1 || x 2]) := by
    change (D.gates.foldl appendGate (appendGate (List.ofFn x) seed)).getD D.output false = _
    rw [seedStep]
    rfl
  have ops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg
    exact (legal j g hj).1
  let edge (p l : Fin 13) := l ≠ 1 ∧ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9)
  have correct := boundary 13 C edge ops
    (fun p l h => (sameEval _).trans (hpos p l h))
    (fun x h => (sameEval x).trans (hneg x h))
  refine ⟨C, 26, by omega, by omega, by omega, by decide, by omega, legal, readSeed, ?_⟩
  intro x
  simpa only [edge, and_assoc] using correct x
