import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Cut off the first gate and pass its signal as the tenth input to the suffix. -/
theorem PEqualNP.Outside.R_meta_2163_509
    (cut : ∀ (C : Circuit) (w : List Bool), C.gates ≠ [] →
      C.eval w = (⟨C.gates.tail, C.output⟩ : Circuit).eval
        (w ++ [(C.wires w).getD w.length false]))
    (suffixBound : ∀ D : Circuit, FanInTwo D →
      (∃ a b : Fin D.gates.length, a ≠ b ∧ (D.gates.get a).op = GateOp.not ∧
        (D.gates.get b).op = GateOp.not ∧ ∀ i : Fin D.gates.length,
        (D.gates.get i).op = GateOp.not → i = a ∨ i = b) →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      15 ≤ D.size) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 ≠ x4 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size
 := by
  intro C fan ⟨a,b,hab,ha,hb,honly⟩ front computes
  cases C with
  | mk gates output =>
    cases gates with
    | nil => exact Fin.elim0 a
    | cons g gs =>
      have noFrontNot : g.op ≠ GateOp.not := by
        intro hn
        have eq := front (fun _ => false)
        have initial : List.ofFn (fun _ : Fin 9 => false) = List.replicate 9 false := by decide
        have one : (g.inputs.map fun i => (List.replicate 9 false).getD i false).headD false =
            false := by
          cases h : g.inputs with
          | nil => rfl
          | cons i is =>
            simp only [List.map_cons, List.headD_cons, List.getD_eq_getElem?_getD,
              List.getElem?_replicate]
            split <;> rfl
        rw [initial] at eq
        have preserve (s : List Gate) (ws : List Bool) (h : 9 < ws.length) :
            (s.foldl (fun w (v : Gate) =>
              w ++ [v.op.eval (v.inputs.map fun i => w.getD i false)]) ws).getD 9 false =
            ws.getD 9 false := by
          induction s generalizing ws with
          | nil => rfl
          | cons v vs ih =>
            rw [List.foldl_cons, ih]
            · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
            · simp
              omega
        have gval : g.op.eval (g.inputs.map fun i => (List.replicate 9 false).getD i false)
            = true := by
          rw [hn]
          change !((g.inputs.map fun i => (List.replicate 9 false).getD i false).headD false) = true
          rw [one]
          rfl
        change ((g::gs).foldl (fun w (v : Gate) =>
          w ++ [v.op.eval (v.inputs.map fun i => w.getD i false)])
          (List.replicate 9 false)).getD 9 false = false at eq
        rw [List.foldl_cons, gval, preserve gs _ (by decide)] at eq
        exact Bool.noConfusion eq
      have an : a.val ≠ 0 := by
        intro h
        apply noFrontNot
        simpa only [List.get_eq_getElem, h, List.getElem_cons_zero] using ha
      have bn : b.val ≠ 0 := by
        intro h
        apply noFrontNot
        simpa only [List.get_eq_getElem, h, List.getElem_cons_zero] using hb
      let a' : Fin gs.length := ⟨a.val-1, by have := a.isLt; simp at this; omega⟩
      let b' : Fin gs.length := ⟨b.val-1, by have := b.isLt; simp at this; omega⟩
      have aeq : a'.succ = a := by apply Fin.ext; change a.val - 1 + 1 = a.val; omega
      have beq : b'.succ = b := by apply Fin.ext; change b.val - 1 + 1 = b.val; omega
      have mapGet (i : Fin gs.length) : (g::gs).get i.succ = gs.get i := by
        simp [List.get_eq_getElem]
      let D : Circuit := ⟨gs, output⟩
      have hf : FanInTwo D := fun v hv => fan v (List.mem_cons_of_mem _ hv)
      have hn : ∃ i j : Fin D.gates.length, i ≠ j ∧ (D.gates.get i).op = GateOp.not ∧
          (D.gates.get j).op = GateOp.not ∧ ∀ k : Fin D.gates.length,
          (D.gates.get k).op = GateOp.not → k = i ∨ k = j := by
        refine ⟨a', b', ?_, ?_, ?_, ?_⟩
        · intro e
          exact hab (aeq.symm.trans ((congrArg Fin.succ e).trans beq))
        · change (gs.get a').op = _
          rw [← mapGet, aeq]
          exact ha
        · change (gs.get b').op = _
          rw [← mapGet, beq]
          exact hb
        · intro i hi
          have hh := honly i.succ (by rw [mapGet]; exact hi)
          rcases hh with hh | hh
          · exact Or.inl (Fin.succ_injective _ (hh.trans aeq.symm))
          · exact Or.inr (Fin.succ_injective _ (hh.trans beq.symm))
      have lower := suffixBound D hf hn (by
        intro x
        have he := cut ⟨g::gs,output⟩ (List.ofFn x) (by simp)
        change _ = D.eval (List.ofFn x ++ [_]) at he
        rw [List.length_ofFn, front x] at he
        exact he.symm.trans (congrFun computes x))
      exact Nat.succ_le_succ lower
