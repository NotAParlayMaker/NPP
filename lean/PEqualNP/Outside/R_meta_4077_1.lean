import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_4077_1
    (h18 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 (fun (x : Fin 10 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) 18)
    (h17 : ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size = (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) || if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true) :
    ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) || if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true := by
  intro b C u v hfan hsize f w h10 h11 h12
  change ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 f 18 at h18
  by_cases hsmall : C.size ≤ 16
  · by_contra hgoal
    have hNo : ∀ x : Fin 10 → Bool, f x = false →
        ¬ (w x u = true ∧ w x v = true) := by
      intro x hfx hboth
      exact hgoal ⟨x, hfx, hboth.1, hboth.2⟩
    let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
      fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
    let t : (Fin 10 → Bool) → Bool :=
      fun x => x 0 || (if b then x 1 else x 2)
    let g₀ : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, if b then 1 else 2]⟩
    let g₁ : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [u, v]⟩
    let E : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨g₀ :: (C.gates ++ [g₁]), 11 + C.size⟩
    have hfanE : PEqualNP.MetaComplexity.FanInTwo E := by
      intro g hg
      simp only [E, List.mem_cons, List.mem_append] at hg
      rcases hg with hg | hg
      · subst g
        constructor <;> simp [g₀]
      · rcases hg with hg | hg
        · exact hfan g hg
        · rcases hg with hg | hg
          · subst g
            constructor <;> simp [g₁]
          · simp at hg
    have hsizeE : E.size ≤ 18 := by
      simp only [E, PEqualNP.CircuitLowerBounds.Circuit.size, List.length_cons,
        List.length_append, List.length_nil] 
      simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hsmall
      omega
    have hlen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool),
        (gs.foldl step ws).length = ws.length + gs.length := by
      intro gs
      induction gs with
      | nil =>
          intro ws
          simp
      | cons g gs ih =>
          intro ws
          rw [List.foldl_cons, ih]
          change (ws ++ [_]).length + gs.length = ws.length + (g :: gs).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
    have ofFn10 (x : Fin 10 → Bool) :
        List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
      simp [List.ofFn_succ]
    have hE (x : Fin 10 → Bool) :
        E.wires (List.ofFn x) =
          C.wires (List.ofFn x ++ [t x]) ++ [w x u && w x v] := by
      have h0 : g₀.op.eval (g₀.inputs.map fun i => (List.ofFn x).getD i false) = t x := by
        rw [ofFn10 x]
        cases b <;> simp [g₀, t, PEqualNP.CircuitLowerBounds.GateOp.eval]
      have h0' : step (List.ofFn x) g₀ = List.ofFn x ++ [t x] := by
        simpa [step] using congrArg (fun q : Bool => List.ofFn x ++ [q]) h0
      have h1 : g₁.op.eval (g₁.inputs.map fun i =>
          (C.wires (List.ofFn x ++ [t x])).getD i false) = (w x u && w x v) := by
        simp [g₁, w, PEqualNP.CircuitLowerBounds.GateOp.eval]
        all_goals cases b <;> rfl
      change List.foldl step (List.ofFn x) (g₀ :: (C.gates ++ [g₁])) = _
      rw [List.foldl_cons, h0', List.foldl_append, List.foldl_cons]
      change C.wires (List.ofFn x ++ [t x]) ++
        [g₁.op.eval (g₁.inputs.map fun i => (C.wires (List.ofFn x ++ [t x])).getD i false)] = _
      rw [h1]
    have hpreLen (x : Fin 10 → Bool) :
        (C.wires (List.ofFn x ++ [t x])).length = 11 + C.size := by
      change (C.gates.foldl step (List.ofFn x ++ [t x])).length = _
      rw [hlen]
      simp [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append]
    have getD_snoc_end : ∀ {α : Type} (l : List α) (a d : α),
        (l ++ [a]).getD l.length d = a := by
      intro α l a d
      rw [List.getD_eq_getElem _ _ (by simp),
        List.getElem_append_right (Nat.le_refl _)]
      simp
    have hEval (x : Fin 10 → Bool) : E.eval (List.ofFn x) = (w x u && w x v) := by
      change (E.wires (List.ofFn x)).getD (11 + C.size) false = _
      rw [hE x, ← hpreLen x]
      exact getD_snoc_end _ _ _
    have hcompute : ∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = f x := by
      intro x
      cases hf : f x
      · have hprod : (w x u && w x v) = false := by
          by_cases hu : w x u = true
          · by_cases hv : w x v = true
            · exact False.elim (hNo x hf ⟨hu, hv⟩)
            · simp [hu, hv]
          · simp [hu]
        rw [hEval x]
        exact hprod
      · obtain ⟨hu, hv⟩ := h12 x hf
        rw [hEval x]
        simp [hu, hv]
    exact h18 ⟨E, hfanE, hsizeE, hcompute⟩
  · exact h17 b C u v hfan (by omega) h10 h11 h12

