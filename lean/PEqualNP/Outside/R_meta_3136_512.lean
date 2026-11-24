import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Reduction of L-meta-3136 (weight 90):
    Internally proves:
    1. Out-of-range wires (`23 ≤ a ∨ 23 ≤ b`) evaluate to `false` at `fun _ => true`, where `f9 = true`.
    2. Input wires (`a < 9 ∨ b < 9`) are `false` on a non-incident edge of `f9`, where `f9 = true`.
    3. Wire 9 (`x 0 || x 3`) is `false` on edge `(1, 2)`, where `f9 = true`.
    4. By `Bool.and_comm`, WLOG `10 ≤ a ≤ b < 23`.
    Splits the remaining cases into `single_wire` (`a = b`), `monotone_pair` (`10 ≤ a < b < 23`,
    0 NOT gates), and `one_not_pair` (`10 ≤ a < b < 23`, 1 NOT gate). -/
theorem PEqualNP.Outside.R_meta_3136_512
    (single_wire :
      let f9 : (Fin 9 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
        (x 6 && x 8) || (x 8 && x 5)
      ∀ (gs : List Gate) (a : ℕ),
        gs.length = 13 →
        FanInTwo { gates := gs, output := 0 } →
        List.countP (fun g => g.op.eval [false]) gs ≤ 1 →
        10 ≤ a → a < 23 →
        ∃ x : Fin 9 → Bool,
          ({ gates := gs, output := 0 : Circuit }.wires (List.ofFn x ++ [x 0 || x 3])).getD a false ≠ f9 x)
    (monotone_pair :
      let f9 : (Fin 9 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
        (x 6 && x 8) || (x 8 && x 5)
      ∀ (gs : List Gate) (a b : ℕ),
        gs.length = 13 →
        FanInTwo { gates := gs, output := 0 } →
        List.countP (fun g => g.op.eval [false]) gs = 0 →
        10 ≤ a → a < b → b < 23 →
        ∃ x : Fin 9 → Bool,
          let ws := { gates := gs, output := 0 : Circuit }.wires (List.ofFn x ++ [x 0 || x 3])
          (ws.getD a false && ws.getD b false) ≠ f9 x)
    (one_not_pair :
      let f9 : (Fin 9 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
        (x 6 && x 8) || (x 8 && x 5)
      ∀ (gs : List Gate) (a b : ℕ),
        gs.length = 13 →
        FanInTwo { gates := gs, output := 0 } →
        List.countP (fun g => g.op.eval [false]) gs = 1 →
        10 ≤ a → a < b → b < 23 →
        ∃ x : Fin 9 → Bool,
          let ws := { gates := gs, output := 0 : Circuit }.wires (List.ofFn x ++ [x 0 || x 3])
          (ws.getD a false && ws.getD b false) ≠ f9 x) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),
      x1.length = (13 : ℕ) →
      PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →
      x2 ≤ (24 : ℕ) →
      x3 ≤ (24 : ℕ) →
      ∃ (x9 : Fin (9 : ℕ) → Bool),
        have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires
          (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);
        (x10.getD x2 Bool.false && x10.getD x3 Bool.false) ≠
          (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) ||
           x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) ||
           x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) ||
           x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) ||
           x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) ||
           x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) ||
           x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) ||
           x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) ||
           x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) ||
           x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) ||
           x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) ||
           x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro gs a b hlen hfan hnot ha24 hb24
  let f9 : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  let wireStep : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]
  have hfold_len : ∀ (ls : List Gate) (ws : List Bool),
      (ls.foldl wireStep ws).length = ws.length + ls.length := by
    intro ls; induction ls with
    | nil => intro ws; simp
    | cons g r ih =>
      intro ws; simp only [List.foldl_cons, List.length_cons]
      rw [ih]; simp [wireStep]; omega
  have hfold_prev : ∀ (ls : List Gate) (ws : List Bool) (w : ℕ),
      w < ws.length → (ls.foldl wireStep ws).getD w false = ws.getD w false := by
    intro ls; induction ls with
    | nil => intro ws w _; rfl
    | cons g r ih =>
      intro ws w hw
      simp only [List.foldl_cons]
      rw [ih (wireStep ws g) w (by simp [wireStep]; omega)]
      dsimp only [wireStep]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hw, ← List.getD_eq_getElem?_getD]
  -- Helper: any wire w with w < 10 or 23 ≤ w has an input x where f9 x = true and ws.getD w false = false
  have hbad_wire : ∀ w : ℕ, (w < 10 ∨ 23 ≤ w) →
      ∃ x : Fin 9 → Bool,
        ({ gates := gs, output := 0 : Circuit }.wires (List.ofFn x ++ [x 0 || x 3])).getD w false = false ∧
        f9 x = true := by
    intro w hw
    rcases hw with hlt10 | hge23
    · by_cases hlt9 : w < 9
      · -- Input wire w < 9: pick edge (5, 7) if w ≠ 5 ∧ w ≠ 7, else edge (0, 1)
        let i0 : Fin 9 := ⟨w, hlt9⟩
        let x : Fin 9 → Bool :=
          if w = 5 ∨ w = 7 then fun k => decide (k = 0 ∨ k = 1)
          else fun k => decide (k = 5 ∨ k = 7)
        refine ⟨x, ?_, ?_⟩
        · unfold Circuit.wires
          change (gs.foldl wireStep (List.ofFn x ++ [x 0 || x 3])).getD w false = false
          rw [hfold_prev _ _ w (by simp; omega),
              List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlt9]),
              List.getElem?_eq_getElem (by simp [hlt9]), Option.getD_some, List.getElem_ofFn]
          dsimp only [x]
          split_ifs with h57
          · rcases h57 with rfl | rfl <;> simp
          · push Not at h57
            simp only [decide_eq_false_iff_not, not_or]
            exact ⟨fun h => h57.1 (congrArg Fin.val h), fun h => h57.2 (congrArg Fin.val h)⟩
        · dsimp only [x]
          split_ifs <;> decide
      · -- Wire 9 = x 0 || x 3: evaluate at edge (1, 2)
        have hw9 : w = 9 := by omega
        let x : Fin 9 → Bool := fun k => decide (k = 1 ∨ k = 2)
        refine ⟨x, ?_, by decide⟩
        unfold Circuit.wires
        change (gs.foldl wireStep (List.ofFn x ++ [x 0 || x 3])).getD w false = false
        rw [hfold_prev _ _ w (by simp; omega), hw9,
            List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp [x]
    · -- Out-of-range wire 23 ≤ w: evaluate at allTrue
      let x : Fin 9 → Bool := fun _ => true
      refine ⟨x, ?_, by decide⟩
      unfold Circuit.wires
      change (gs.foldl wireStep (List.ofFn x ++ [x 0 || x 3])).getD w false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
      · rfl
      · rw [hfold_len]; simp [hlen]; omega
  -- Eliminate bad wires a or b
  by_cases haBad : a < 10 ∨ 23 ≤ a
  · rcases hbad_wire a haBad with ⟨x, hwa, hfx⟩
    exact ⟨x, by change _ ≠ f9 x; rw [hwa, Bool.false_and, hfx]; decide⟩
  · by_cases hbBad : b < 10 ∨ 23 ≤ b
    · rcases hbad_wire b hbBad with ⟨x, hwb, hfx⟩
      exact ⟨x, by change _ ≠ f9 x; rw [hwb, Bool.and_false, hfx]; decide⟩
    · have ha10 : 10 ≤ a := by omega
      have ha23 : a < 23 := by omega
      have hb10 : 10 ≤ b := by omega
      have hb23 : b < 23 := by omega
      by_cases hab : a = b
      · subst hab
        rcases single_wire gs a hlen hfan hnot ha10 ha23 with ⟨x, hx⟩
        exact ⟨x, by simpa only [Bool.and_self] using hx⟩
      · by_cases hlt : a < b
        · by_cases hn0 : List.countP (fun g => g.op.eval [false]) gs = 0
          · exact monotone_pair gs a b hlen hfan hn0 ha10 hlt hb23
          · exact one_not_pair gs a b hlen hfan (by omega) ha10 hlt hb23
        · have hgt : b < a := by omega
          by_cases hn0 : List.countP (fun g => g.op.eval [false]) gs = 0
          · rcases monotone_pair gs b a hlen hfan hn0 hb10 hgt ha23 with ⟨x, hx⟩
            exact ⟨x, by simpa only [Bool.and_comm] using hx⟩
          · rcases one_not_pair gs b a hlen hfan (by omega) hb10 hgt ha23 with ⟨x, hx⟩
            exact ⟨x, by simpa only [Bool.and_comm] using hx⟩
