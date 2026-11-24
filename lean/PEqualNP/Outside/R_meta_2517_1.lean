import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2517_1
    (cut : ∀ (C : Circuit) (w : List Bool), C.gates ≠ [] →
      C.eval w = (⟨C.gates.tail, C.output⟩ : Circuit).eval
        (w ++ [(C.wires w).getD w.length false]))
    (suffixBound : ∀ D : Circuit, FanInTwo D →
      (∃ a b : Fin D.gates.length, a < b ∧ 3 ≤ (a : ℕ) ∧ (a : ℕ) ≤ 6 ∧
        (D.gates.get a).op = GateOp.not ∧ (D.gates.get b).op = GateOp.not ∧
        ∀ i : Fin D.gates.length, (D.gates.get i).op = GateOp.not → i = a ∨ i = b) →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      15 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ (4 : ℕ) ≤ ↑x3 ∧ ↑x3 ≤ (7 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan ⟨a, b, ab, alo, ahi, ha, hb, only⟩ front computes
  cases C with
  | mk gates output =>
    cases gates with
    | nil => exact Fin.elim0 a
    | cons g gs =>
      let a' : Fin gs.length := ⟨a.val - 1, by have := a.isLt; simp at this; omega⟩
      let b' : Fin gs.length := ⟨b.val - 1, by have := b.isLt; simp at this; omega⟩
      have aeq : a'.succ = a := by apply Fin.ext; change a.val - 1 + 1 = a.val; omega
      have beq : b'.succ = b := by apply Fin.ext; change b.val - 1 + 1 = b.val; omega
      have mapGet (i : Fin gs.length) : (g :: gs).get i.succ = gs.get i := by
        simp [List.get_eq_getElem]
      let D : Circuit := ⟨gs, output⟩
      have dfan : FanInTwo D := fun v hv => fan v (List.mem_cons_of_mem _ hv)
      have dnots : ∃ i j : Fin D.gates.length, i < j ∧ 3 ≤ (i : ℕ) ∧
          (i : ℕ) ≤ 6 ∧ (D.gates.get i).op = GateOp.not ∧
          (D.gates.get j).op = GateOp.not ∧ ∀ k : Fin D.gates.length,
          (D.gates.get k).op = GateOp.not → k = i ∨ k = j := by
        refine ⟨a', b', ?_, by change 3 ≤ a.val - 1; omega,
          by change a.val - 1 ≤ 6; omega, ?_, ?_, ?_⟩
        · exact Fin.mk_lt_mk.mpr (by omega)
        · change (gs.get a').op = _
          rw [← mapGet, aeq]
          exact ha
        · change (gs.get b').op = _
          rw [← mapGet, beq]
          exact hb
        · intro i hi
          have h := only i.succ (by rw [mapGet]; exact hi)
          rcases h with h | h
          · exact Or.inl (Fin.succ_injective _ (h.trans aeq.symm))
          · exact Or.inr (Fin.succ_injective _ (h.trans beq.symm))
      have lower := suffixBound D dfan dnots (by
        intro x
        have hcut := cut ⟨g :: gs, output⟩ (List.ofFn x) (by simp)
        change _ = D.eval (List.ofFn x ++ [_]) at hcut
        rw [List.length_ofFn, front x] at hcut
        exact hcut.symm.trans (congrFun computes x))
      exact Nat.succ_le_succ lower
