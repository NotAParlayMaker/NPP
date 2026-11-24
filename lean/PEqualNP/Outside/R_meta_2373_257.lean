import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2373_257
    (hLowBin : ∀ (C : Circuit), FanInTwo C →
      C.gates.countP (fun g => !(g.op.eval [false])) ≤ 15 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠
        (fun x : Fin 10 → Bool =>
          x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
          x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x)
    (hHighBin : ∀ (g1 : Gate) (C2 : Circuit) (u v : ℕ),
      FanInTwo { gates := [g1], output := 0 } →
      FanInTwo C2 →
      C2.size ≤ 17 →
      15 ≤ (g1 :: C2.gates).countP (fun g => !(g.op.eval [false])) →
      have f : (Fin 10 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5;
      have w : (Fin 10 → Bool) → ℕ → Bool := fun x k =>
        (C2.wires ({ gates := [g1], output := 0 : Circuit }.wires (List.ofFn x))).getD k false;
      (∃ x, w x u = true ∧ w x v = false) →
      (∃ x, w x u = false ∧ w x v = true) →
      (∀ x, f x = false → w x u = false ∧ w x v = false) →
      ∃ x, f x = true ∧ w x u = false ∧ w x v = false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size ≤ (17 : ℕ) →
      have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) =>
        x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) ||
        x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) ||
        x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) ||
        x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) ||
        x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) ||
        x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));
      have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) =>
        (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;
      (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) →
      (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) →
      (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro g1 C2 u v h1 h2 hsz f w hU hV hFalse
  by_cases hbin : 15 ≤ (g1 :: C2.gates).countP (fun g => !(g.op.eval [false]))
  · exact hHighBin g1 C2 u v h1 h2 hsz hbin hU hV hFalse
  · by_contra hno
    let topGate : Gate := ⟨GateOp.or, [u, v]⟩
    let C : Circuit := ⟨(g1 :: C2.gates) ++ [topGate], 10 + (g1 :: C2.gates).length⟩
    have hfanC : FanInTwo C := by
      intro g hg
      change g ∈ (g1 :: C2.gates) ++ [topGate] at hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (rfl | hg2) | rfl
      · exact h1 g (by simp)
      · exact h2 g hg2
      · exact ⟨by simp [topGate], by simp [topGate]⟩
    have hcntC : C.gates.countP (fun g => !(g.op.eval [false])) ≤ 15 := by
      change ((g1 :: C2.gates) ++ [topGate]).countP (fun g => !(g.op.eval [false])) ≤ 15
      rw [List.countP_append]
      have htop : [topGate].countP (fun g => !(g.op.eval [false])) = 1 := rfl
      omega
    obtain ⟨x, hx⟩ := hLowBin C hfanC hcntC
    apply hx
    have hstepLen (gs : List Gate) (ws : List Bool) :
        (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) ws).length =
          ws.length + gs.length := by
      induction gs generalizing ws with
      | nil => simp
      | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega
    let pre := (g1 :: C2.gates).foldl
      (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn x)
    have hpreEq : pre = C2.wires ({ gates := [g1], output := 0 : Circuit }.wires (List.ofFn x)) := by
      rfl
    have hpreLen : pre.length = 10 + (g1 :: C2.gates).length := by
      simpa [pre] using hstepLen (g1 :: C2.gates) (List.ofFn x)
    have hEvalC : C.eval (List.ofFn x) = (pre.getD u false || pre.getD v false) := by
      change (((g1 :: C2.gates) ++ [topGate]).foldl
        (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn x)).getD
          (10 + (g1 :: C2.gates).length) false = _
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (pre ++ [topGate.op.eval (topGate.inputs.map fun i => pre.getD i false)]).getD
        (10 + (g1 :: C2.gates).length) false = _
      rw [← hpreLen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
      change GateOp.or.eval [pre.getD u false, pre.getD v false] = (pre.getD u false || pre.getD v false)
      cases pre.getD u false <;> cases pre.getD v false <;> rfl
    rw [hEvalC, hpreEq]
    change (w x u || w x v) = f x
    cases hfx : f x with
    | false =>
      obtain ⟨hu, hv⟩ := hFalse x hfx
      rw [hu, hv]
      rfl
    | true =>
      cases hu : w x u <;> cases hv : w x v
      · exact (hno ⟨x, hfx, hu, hv⟩).elim
      · rfl
      · rfl
      · rfl
