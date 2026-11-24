import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

/-- Reduction of L-meta-4960:
    Internally proves:
    1. Minimalization: replaces `C` with a minimum-size `IsAO2 (a + b)` circuit `C'` computing `f_E`.
    2. Small-`E` elimination: proves `E.card = 0` and `E.card = 1` directly (showing `1 ≤ C'.size`
       whenever `E.Nonempty`), reducing to `2 ≤ E.card`.
    3. Output-wire normalization: proves `a + b ≤ C'.output ∧ C'.output < a + b + C'.size`.
    Splits the remaining minimal circuits by `andCount C' < M.card` vs `M.card ≤ andCount C'`,
    combining the two constants via `max K₁ K₂`. -/
theorem PEqualNP.Outside.R_meta_4960_512
    (low_and :
      ∃ K₁ : ℕ, ∀ (a b : ℕ) (E M : Finset (Fin a × Fin b)) (C : Circuit),
        (∀ p₁ p₂ : Fin a, ∀ l₁ l₂ : Fin b, p₁ ≠ p₂ → l₁ ≠ l₂ →
          ¬((p₁, l₁) ∈ E ∧ (p₁, l₂) ∈ E ∧ (p₂, l₁) ∈ E ∧ (p₂, l₂) ∈ E)) →
        IsAO2 (a + b) C →
        (∀ x : Fin (a + b) → Bool,
          circuitFun (a + b) C x =
            decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true)) →
        (∀ C' : Circuit, IsAO2 (a + b) C' →
          (∀ x : Fin (a + b) → Bool,
            circuitFun (a + b) C' x =
              decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true)) →
          C.size ≤ C'.size) →
        M ⊆ E →
        (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁.1 = e₂.1 → e₁ = e₂) →
        (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁.2 = e₂.2 → e₁ = e₂) →
        2 ≤ E.card →
        a + b ≤ C.output →
        C.output < a + b + C.size →
        (C.gates.filter (fun g => match g.op with | GateOp.and => true | _ => false)).length < M.card →
        E.card + M.card ≤ C.size + 1 + K₁ * (a + b + 1).sqrt)
    (high_and :
      ∃ K₂ : ℕ, ∀ (a b : ℕ) (E M : Finset (Fin a × Fin b)) (C : Circuit),
        (∀ p₁ p₂ : Fin a, ∀ l₁ l₂ : Fin b, p₁ ≠ p₂ → l₁ ≠ l₂ →
          ¬((p₁, l₁) ∈ E ∧ (p₁, l₂) ∈ E ∧ (p₂, l₁) ∈ E ∧ (p₂, l₂) ∈ E)) →
        IsAO2 (a + b) C →
        (∀ x : Fin (a + b) → Bool,
          circuitFun (a + b) C x =
            decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true)) →
        (∀ C' : Circuit, IsAO2 (a + b) C' →
          (∀ x : Fin (a + b) → Bool,
            circuitFun (a + b) C' x =
              decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true)) →
          C.size ≤ C'.size) →
        M ⊆ E →
        (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁.1 = e₂.1 → e₁ = e₂) →
        (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁.2 = e₂.2 → e₁ = e₂) →
        2 ≤ E.card →
        a + b ≤ C.output →
        C.output < a + b + C.size →
        M.card ≤ (C.gates.filter (fun g => match g.op with | GateOp.and => true | _ => false)).length →
        E.card + M.card ≤ C.size + 1 + K₂ * (a + b + 1).sqrt) :
    ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 x5 : Finset (Fin x2 × Fin x3))
      (x6 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x7 x8 : Fin x2) (x9 x10 : Fin x3), x7 ≠ x8 → x9 ≠ x10 →
        ¬((x7, x9) ∈ x4 ∧ (x7, x10) ∈ x4 ∧ (x8, x9) ∈ x4 ∧ (x8, x10) ∈ x4)) →
      PEqualNP.TopForm.IsAO2 (x2 + x3) x6 →
      (∀ (x9 : Fin (x2 + x3) → Bool),
        PEqualNP.MetaComplexity.circuitFun (x2 + x3) x6 x9 =
          Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x3),
            (x10, x11) ∈ x4 ∧ x9 (Fin.castAdd x3 x10) = Bool.true ∧ x9 (Fin.natAdd x2 x11) = Bool.true)) →
      x5 ⊆ x4 →
      (∀ x11 ∈ x5, ∀ x13 ∈ x5, x11.1 = x13.1 → x11 = x13) →
      (∀ x12 ∈ x5, ∀ x14 ∈ x5, x12.2 = x14.2 → x12 = x14) →
      x4.card + x5.card ≤ x6.size + (1 : ℕ) + x1 * (x2 + x3 + (1 : ℕ)).sqrt := by
  classical
  rcases low_and with ⟨K₁, hlow⟩
  rcases high_and with ⟨K₂, hhigh⟩
  refine ⟨max K₁ K₂, ?_⟩
  intro a b E M C hno4 hao2 hfun hME hM1 hM2
  -- Helper: wireStep preserves length and earlier entries
  let wireStep : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]
  have hfold_len : ∀ (gs : List Gate) (ws : List Bool),
      (gs.foldl wireStep ws).length = ws.length + gs.length := by
    intro gs; induction gs with
    | nil => intro ws; simp
    | cons g r ih =>
      intro ws; simp only [List.foldl_cons, List.length_cons]
      rw [ih]; simp [wireStep]; omega
  have hfold_prev : ∀ (gs : List Gate) (ws : List Bool) (w : ℕ),
      w < ws.length → (gs.foldl wireStep ws).getD w false = ws.getD w false := by
    intro gs; induction gs with
    | nil => intro ws w _; rfl
    | cons g r ih =>
      intro ws w hw
      simp only [List.foldl_cons]
      rw [ih (wireStep ws g) w (by simp [wireStep]; omega)]
      dsimp only [wireStep]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hw, ← List.getD_eq_getElem?_getD]
  -- Step 1: Minimalize C via Nat.find
  let P : ℕ → Prop := fun s =>
    ∃ C' : Circuit, IsAO2 (a + b) C' ∧ C'.size = s ∧
      ∀ x : Fin (a + b) → Bool,
        circuitFun (a + b) C' x =
          decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true)
  have hP_ex : ∃ s, P s := ⟨C.size, C, hao2, rfl, hfun⟩
  let sMin := Nat.find hP_ex
  have hsMin_le : sMin ≤ C.size := Nat.find_min' hP_ex ⟨C, hao2, rfl, hfun⟩
  rcases Nat.find_spec hP_ex with ⟨C', hao2', hsz', hfun'⟩
  have hmin' : ∀ C'' : Circuit, IsAO2 (a + b) C'' →
      (∀ x : Fin (a + b) → Bool,
        circuitFun (a + b) C'' x =
          decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true)) →
      C'.size ≤ C''.size := by
    intro C'' hao2'' hfun''
    rw [hsz']
    exact Nat.find_min' hP_ex ⟨C'', hao2'', rfl, hfun''⟩
  have hC'_le_C : C'.size ≤ C.size := by omega
  -- Step 2: Handle E.card = 0
  have hM_le_E : M.card ≤ E.card := Finset.card_le_card hME
  by_cases hE0 : E.card = 0
  · omega
  · -- E is nonempty: pick an edge (p0, l0) ∈ E
    have hEne : E.Nonempty := Finset.card_pos.mp (by omega)
    rcases hEne with ⟨⟨p0, l0⟩, hp0l0⟩
    -- Step 3: Prove a + b ≤ C'.output and C'.output < a + b + C'.size
    have hout_ge : a + b ≤ C'.output := by
      by_contra hlt
      push Not at hlt
      let i0 : Fin (a + b) := ⟨C'.output, hlt⟩
      let x : Fin (a + b) → Bool := fun k => decide (k = i0)
      have hC'x : circuitFun (a + b) C' x = true := by
        unfold circuitFun Circuit.eval Circuit.wires
        change (C'.gates.foldl wireStep (List.ofFn x)).getD C'.output false = true
        rw [hfold_prev _ _ C'.output (by simp [hlt])]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlt])]
        simp [x, i0]
      rw [hfun' x] at hC'x
      simp only [decide_eq_true_eq] at hC'x
      rcases hC'x with ⟨p, l, _, hp, hl⟩
      have hp' : Fin.castAdd b p = i0 := by simpa [x] using hp
      have hl' : Fin.natAdd a l = i0 := by simpa [x] using hl
      have heq := congrArg Fin.val (hp'.trans hl'.symm)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
      have := p.isLt
      omega
    have hout_lt : C'.output < a + b + C'.size := by
      by_contra hge
      push Not at hge
      let x : Fin (a + b) → Bool := fun k => decide (k = Fin.castAdd b p0 ∨ k = Fin.natAdd a l0)
      have hC'x : circuitFun (a + b) C' x = false := by
        unfold circuitFun Circuit.eval Circuit.wires
        change (C'.gates.foldl wireStep (List.ofFn x)).getD C'.output false = false
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
        · rfl
        · rw [hfold_len, List.length_ofFn]; exact hge
      have hfx : decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨p0, l0, hp0l0, by simp [x], by simp [x]⟩
      rw [hfun' x, hfx] at hC'x
      contradiction
    -- Step 4: Handle E.card = 1 (since 1 ≤ C'.size follows from hout_ge and hout_lt)
    have hC'_pos : 1 ≤ C'.size := by omega
    by_cases hE1 : E.card ≤ 1
    · omega
    · have hE2 : 2 ≤ E.card := by omega
      -- Step 5: Split on andCount C' < M.card vs M.card ≤ andCount C'
      have hK1_le : K₁ * (a + b + 1).sqrt ≤ max K₁ K₂ * (a + b + 1).sqrt :=
        Nat.mul_le_mul_right _ (le_max_left K₁ K₂)
      have hK2_le : K₂ * (a + b + 1).sqrt ≤ max K₁ K₂ * (a + b + 1).sqrt :=
        Nat.mul_le_mul_right _ (le_max_right K₁ K₂)
      by_cases hand : (C'.gates.filter (fun g => match g.op with | GateOp.and => true | _ => false)).length < M.card
      · have hb := hlow a b E M C' hno4 hao2' hfun' hmin' hME hM1 hM2 hE2 hout_ge hout_lt hand
        omega
      · have hb := hhigh a b E M C' hno4 hao2' hfun' hmin' hME hM1 hM2 hE2 hout_ge hout_lt (by omega)
        omega
