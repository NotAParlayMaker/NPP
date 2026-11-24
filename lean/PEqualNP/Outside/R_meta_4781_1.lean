import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4781_1
    (hnorm : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∃ x : Fin 14 → Bool, C.eval (List.ofFn x) = Bool.true) →
      (∃ y : Fin 14 → Bool, C.eval (List.ofFn y) = Bool.false) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 14 D ∧
        D.size ≤ C.size ∧
        ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (htopAnd : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 14 D →
        14 ≤ D.output → D.output < 14 + D.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D (D.output - 14)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ x4 : Fin 14 → Bool,
          (∃ x5 x6 : Fin 14, (↑x5, ↑x6) ∈ x1 ∧ (x5 ≠ 0 ∨ x6 ≠ 7) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) →
          D.eval (List.ofFn x4) = Bool.true) →
        (∀ x5 : Fin 14 → Bool,
          D.eval (List.ofFn x5) = Bool.true →
          ∃ x7 x8 : Fin 14, (↑x7, ↑x8) ∈ x1 ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true) →
        D.eval (List.ofFn fun x6 : Fin 14 => Decidable.decide (x6 = 0 ∨ x6 = 7)) = Bool.false →
        25 ≤ D.size)
    (htopOr : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 14 D →
        14 ≤ D.output → D.output < 14 + D.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D (D.output - 14)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ x4 : Fin 14 → Bool,
          (∃ x5 x6 : Fin 14, (↑x5, ↑x6) ∈ x1 ∧ (x5 ≠ 0 ∨ x6 ≠ 7) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) →
          D.eval (List.ofFn x4) = Bool.true) →
        (∀ x5 : Fin 14 → Bool,
          D.eval (List.ofFn x5) = Bool.true →
          ∃ x7 x8 : Fin 14, (↑x7, ↑x8) ∈ x1 ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true) →
        D.eval (List.ofFn fun x6 : Fin 14 => Decidable.decide (x6 = 0 ∨ x6 = 7)) = Bool.false →
        25 ≤ D.size) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : Fin (14 : ℕ) → Bool), (∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)), (↑x5, ↑x6) ∈ x1 ∧ (x5 ≠ (0 : Fin (14 : ℕ)) ∨ x6 ≠ (7 : Fin (14 : ℕ))) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) → x2.eval (List.ofFn x4) = Bool.true) → (∀ (x5 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true → ∃ (x7 : Fin (14 : ℕ)) (x8 : Fin (14 : ℕ)), (↑x7, ↑x8) ∈ x1 ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true) → x2.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = (0 : Fin (14 : ℕ)) ∨ x6 = (7 : Fin (14 : ℕ)))) = Bool.false → (25 : ℕ) ≤ x2.size := by
  dsimp only
  let x1 : List (ℕ × ℕ) :=
    [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
     (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
     (6, 8), (6, 9), (6, 11)]
  intro C hmono hcomp hsound hrej07
  have htrue : C.eval (List.ofFn (fun _ : Fin 14 => Bool.true)) = Bool.true := by
    apply hcomp
    refine ⟨0, 8, ?_, Or.inr (by decide), rfl, rfl⟩
    change (0, 8) ∈ x1
    decide
  have hfalse : C.eval (List.ofFn (fun _ : Fin 14 => Bool.false)) = Bool.false := by
    cases h : C.eval (List.ofFn (fun _ : Fin 14 => Bool.false))
    · rfl
    · exfalso
      rcases hsound _ h with ⟨u, v, _, hu, _⟩
      cases hu
  rcases hnorm C hmono ⟨_, htrue⟩ ⟨_, hfalse⟩ with ⟨D, hao, hsz, heq⟩
  have hcompD : ∀ x4 : Fin 14 → Bool,
      (∃ x5 x6 : Fin 14, (↑x5, ↑x6) ∈ x1 ∧ (x5 ≠ 0 ∨ x6 ≠ 7) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) →
      D.eval (List.ofFn x4) = Bool.true := fun x4 h => (heq x4).trans (hcomp x4 h)
  have hsoundD : ∀ x5 : Fin 14 → Bool,
      D.eval (List.ofFn x5) = Bool.true →
      ∃ x7 x8 : Fin 14, (↑x7, ↑x8) ∈ x1 ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true :=
    fun x5 h => hsound x5 ((heq x5).symm.trans h)
  have hrej07D : D.eval (List.ofFn fun x6 : Fin 14 => Decidable.decide (x6 = 0 ∨ x6 = 7)) = Bool.false :=
    (heq _).trans hrej07
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g rest ih =>
      intro w
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have hfold_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g rest ih =>
      intro w i hi
      simp only [List.foldl_cons]
      have hi' : i < (step w g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (step w g) i hi']
      simp only [step, List.getD, List.getElem?_append_left hi]
  have hout_ge : 14 ≤ D.output := by
    by_contra hlt
    have hk : D.output < 14 := by omega
    let v : Fin 14 := ⟨D.output, hk⟩
    let xv : Fin 14 → Bool := fun i => Decidable.decide (i = v)
    have hev : D.eval (List.ofFn xv) = Bool.true := by
      change (D.gates.foldl step (List.ofFn xv)).getD D.output false = Bool.true
      rw [hfold_prefix D.gates (List.ofFn xv) D.output (by rw [List.length_ofFn]; exact hk)]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn]
      simp [xv, v]
    rcases hsoundD xv hev with ⟨u, w, hmem, hu, hw⟩
    have huv : u = v := of_decide_eq_true hu
    have hwv : w = v := of_decide_eq_true hw
    have huw : u = w := huv.trans hwv.symm
    rw [huw] at hmem
    have hnoself : ∀ p ∈ x1, p.1 ≠ p.2 := by decide
    exact hnoself (w.val, w.val) hmem rfl
  have hout_lt : D.output < 14 + D.size := by
    by_contra hge
    have hlen : (D.wires (List.ofFn (fun _ : Fin 14 => Bool.true))).length = 14 + D.size := by
      change (D.gates.foldl step (List.ofFn (fun _ : Fin 14 => Bool.true))).length = 14 + D.gates.length
      rw [hfold_len, List.length_ofFn]
    have hfalseD : D.eval (List.ofFn (fun _ : Fin 14 => Bool.true)) = Bool.false := by
      change (D.wires (List.ofFn (fun _ : Fin 14 => Bool.true))).getD D.output false = Bool.false
      have hge' : (D.wires (List.ofFn (fun _ : Fin 14 => Bool.true))).length ≤ D.output := by omega
      simp only [List.getD, List.getElem?_eq_none hge', Option.getD_none]
    have htrueD : D.eval (List.ofFn (fun _ : Fin 14 => Bool.true)) = Bool.true :=
      (heq _).trans htrue
    rw [htrueD] at hfalseD
    cases hfalseD
  have hj_lt : D.output - 14 < D.gates.length := by
    change D.output - 14 < D.size
    omega
  have hg_mem : PEqualNP.MetaComplexity.NestedCover.gateAt D (D.output - 14) ∈ D.gates := by
    change D.gates.getD (D.output - 14) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ D.gates
    rw [List.getD_eq_getElem _ _ hj_lt]
    exact List.getElem_mem hj_lt
  have h25D : 25 ≤ D.size := by
    rcases hao.1 _ hg_mem with hand | hor
    · exact htopAnd D hao hout_ge hout_lt hand hcompD hsoundD hrej07D
    · exact htopOr D hao hout_ge hout_lt hor hcompD hsoundD hrej07D
  omega
