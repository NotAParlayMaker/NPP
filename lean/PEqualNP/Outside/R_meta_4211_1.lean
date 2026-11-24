import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Input wires cannot stay false on the empty or full point-line rows.
-- The leftover is two internal wires, split on whether the first of them is AND or OR.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4211_1
    (hAND :
      have x1 : Finset (Fin 13) := [0, 1, 3, 9].toFinset
      have x2 : Fin 13 → Fin 13 → Prop := fun p l => ∃ d ∈ x1, p = l + d
      have x3 : Fin 13 → Fin 13 → Fin 26 → Bool :=
        fun p l v => decide (v = Fin.castAdd 13 p ∨ v = Fin.natAdd 13 l)
      have x4 : Finset (Fin 13) → Fin (13 + 13) → Bool :=
        fun S v => decide ((∃ p ∈ S, v = Fin.castAdd 13 p) ∨
          ∃ l, v = Fin.natAdd 13 l ∧ ∀ p ∈ S, ¬∃ d ∈ x1, p = l + d)
      have x5 : Circuit → ℕ → (Fin 26 → Bool) → Bool :=
        fun C w x => (C.wires (List.ofFn x)).getD w false
      ∀ (C : Circuit) (a b : Fin (26 + C.size)),
        Monotone2 C → C.size ≤ 62 → a ≠ b → 26 ≤ a.val → 26 ≤ b.val →
        (NestedCover.gateAt C (a.val - 26)).op = GateOp.and →
        (∀ p l, x2 p l → GateOp.or.eval [x5 C a.val (x3 p l), x5 C b.val (x3 p l)] = true) →
        (∀ m : ℕ, ∀ k : Fin 13,
          m ∈ [8191, 7668, 6624, 5584, 3492, 1408, 7492, 7316, 6272, 7472, 4176, 2084, 6144,
            5120, 4160, 2304, 2052, 4112, 4096, 0].toFinset →
          have S : Finset (Fin 13) := {p : Fin 13 | m.testBit (p - k).val = true}
          GateOp.or.eval [x5 C a.val (x4 S), x5 C b.val (x4 S)] = false) →
        False)
    (hOR :
      have x1 : Finset (Fin 13) := [0, 1, 3, 9].toFinset
      have x2 : Fin 13 → Fin 13 → Prop := fun p l => ∃ d ∈ x1, p = l + d
      have x3 : Fin 13 → Fin 13 → Fin 26 → Bool :=
        fun p l v => decide (v = Fin.castAdd 13 p ∨ v = Fin.natAdd 13 l)
      have x4 : Finset (Fin 13) → Fin (13 + 13) → Bool :=
        fun S v => decide ((∃ p ∈ S, v = Fin.castAdd 13 p) ∨
          ∃ l, v = Fin.natAdd 13 l ∧ ∀ p ∈ S, ¬∃ d ∈ x1, p = l + d)
      have x5 : Circuit → ℕ → (Fin 26 → Bool) → Bool :=
        fun C w x => (C.wires (List.ofFn x)).getD w false
      ∀ (C : Circuit) (a b : Fin (26 + C.size)),
        Monotone2 C → C.size ≤ 62 → a ≠ b → 26 ≤ a.val → 26 ≤ b.val →
        (NestedCover.gateAt C (a.val - 26)).op = GateOp.or →
        (∀ p l, x2 p l → GateOp.or.eval [x5 C a.val (x3 p l), x5 C b.val (x3 p l)] = true) →
        (∀ m : ℕ, ∀ k : Fin 13,
          m ∈ [8191, 7668, 6624, 5584, 3492, 1408, 7492, 7316, 6272, 7472, 4176, 2084, 6144,
            5120, 4160, 2304, 2052, 4112, 4096, 0].toFinset →
          have S : Finset (Fin 13) := {p : Fin 13 | m.testBit (p - k).val = true}
          GateOp.or.eval [x5 C a.val (x4 S), x5 C b.val (x4 S)] = false) →
        False) :
    have x1 : Finset (Fin (13 : ℕ)) := [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].toFinset; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) (x5 : Fin (26 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (13 : ℕ) x3 ∨ x5 = Fin.natAdd (13 : ℕ) x4); have x4 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x4 : Finset (Fin (13 : ℕ))) (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x6 ∈ x4, x5 = Fin.castAdd (13 : ℕ) x6) ∨ ∃ (x6 : Fin (13 : ℕ)), x5 = Fin.natAdd (13 : ℕ) x6 ∧ ∀ x7 ∈ x4, ¬∃ x9 ∈ x1, x7 = x6 + x9); have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : Fin (26 : ℕ) → Bool) => (x5.wires (List.ofFn x7)).getD x6 Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x6 →     x6.size ≤ (62 : ℕ) →       ∀ (x9 x10 : Fin ((26 : ℕ) + x6.size)),         x9 ≠ x10 →           (∀ (x12 x13 : Fin (13 : ℕ)), x2 x12 x13 → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 x6 (↑x9) (x3 x12 x13), x5 x6 (↑x10) (x3 x12 x13)] = Bool.true) →             (∀ (x13 : ℕ) (x14 : Fin (13 : ℕ)),                 x13 ∈ [(8191 : ℕ), (7668 : ℕ), (6624 : ℕ), (5584 : ℕ), (3492 : ℕ), (1408 : ℕ), (7492 : ℕ), (7316 : ℕ), (6272 : ℕ), (7472 : ℕ), (4176 : ℕ), (2084 : ℕ), (6144 : ℕ), (5120 : ℕ), (4160 : ℕ), (2304 : ℕ), (2052 : ℕ), (4112 : ℕ), (4096 : ℕ), (0 : ℕ)].toFinset →                   have x16 : Finset (Fin (13 : ℕ)) := {x16 : Fin (13 : ℕ) | x13.testBit ↑(x16 - x14) = Bool.true};                   PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 x6 (↑x9) (x4 x16), x5 x6 (↑x10) (x4 x16)] = Bool.false) →               False := by
  dsimp only
  intro C hC hsize a b hab hpos hneg
  have fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
        = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hi' : i < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih _ hi', List.getD_append w _ false i hi]
  have wires_input (x : Fin 26 → Bool) (w : ℕ) (hw : w < 26) :
      (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
    have hlen0 : w < (List.ofFn x).length := by
      simpa [List.length_ofFn] using hw
    have := fold_getD_lt C.gates (List.ofFn x) w hlen0
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x)).getD w false = x ⟨w, hw⟩
    rw [this, List.getD_eq_getElem (l := List.ofFn x) (n := w) false hlen0]
    exact List.getElem_ofFn (f := x) hlen0
  have mem0 : (0 : ℕ) ∈ [(8191 : ℕ), (7668 : ℕ), (6624 : ℕ), (5584 : ℕ), (3492 : ℕ), (1408 : ℕ),
      (7492 : ℕ), (7316 : ℕ), (6272 : ℕ), (7472 : ℕ), (4176 : ℕ), (2084 : ℕ), (6144 : ℕ),
      (5120 : ℕ), (4160 : ℕ), (2304 : ℕ), (2052 : ℕ), (4112 : ℕ), (4096 : ℕ), (0 : ℕ)].toFinset := by
    decide
  have memAll : (8191 : ℕ) ∈ [(8191 : ℕ), (7668 : ℕ), (6624 : ℕ), (5584 : ℕ), (3492 : ℕ),
      (1408 : ℕ), (7492 : ℕ), (7316 : ℕ), (6272 : ℕ), (7472 : ℕ), (4176 : ℕ), (2084 : ℕ),
      (6144 : ℕ), (5120 : ℕ), (4160 : ℕ), (2304 : ℕ), (2052 : ℕ), (4112 : ℕ), (4096 : ℕ),
      (0 : ℕ)].toFinset := by
    decide
  have or_true_left (u v : Bool) (h : u = true) : GateOp.or.eval [u, v] = true := by
    change (u || (v || false)) = true
    simp only [h, Bool.true_or]
  have or_true_right (u v : Bool) (h : v = true) : GateOp.or.eval [u, v] = true := by
    change (u || (v || false)) = true
    simp only [h, Bool.or_false, Bool.or_true]
  have testBit_all : ∀ p : Fin 13, (8191 : ℕ).testBit p.val = true := by decide
  let D : Finset (Fin 13) := [(0 : Fin 13), 1, 3, 9].toFinset
  let Sall : Finset (Fin 13) :=
    {p : Fin 13 | (8191 : ℕ).testBit ↑(p - (0 : Fin 13)) = Bool.true}
  let Semp : Finset (Fin 13) :=
    {p : Fin 13 | (0 : ℕ).testBit ↑(p - (0 : Fin 13)) = Bool.true}
  let row (S : Finset (Fin 13)) (v : Fin 26) : Bool :=
    decide ((∃ p ∈ S, v = Fin.castAdd 13 p) ∨
      ∃ l : Fin 13, v = Fin.natAdd 13 l ∧ ∀ p ∈ S, ¬∃ d ∈ D, p = l + d)
  have point_on_all (w : ℕ) (hw : w < 13) : row Sall ⟨w, by omega⟩ = true := by
    apply decide_eq_true
    refine Or.inl ⟨⟨w, hw⟩, ?_, ?_⟩
    · have : (8191 : ℕ).testBit (⟨w, hw⟩ - (0 : Fin 13)).val = true := by
        have hv : (⟨w, hw⟩ - (0 : Fin 13)).val = w := by
          simp
        rw [hv]
        exact testBit_all ⟨w, hw⟩
      simpa [Sall] using this
    · apply Fin.ext
      simp
  have line_on_empty (w : ℕ) (h13 : 13 ≤ w) (hw : w < 26) : row Semp ⟨w, hw⟩ = true := by
    apply decide_eq_true
    refine Or.inr ⟨⟨w - 13, by omega⟩, ?_, fun p hp => ?_⟩
    · apply Fin.ext
      simp
      omega
    · have hempty : Semp = ∅ := by
        ext q
        simp [Semp]
      exact (Finset.notMem_empty p (hempty ▸ hp)).elim
  have hsz : C.size = C.gates.length := rfl
  have hnegAll := hneg (8191 : ℕ) (0 : Fin 13) memAll
  have hneg0 := hneg (0 : ℕ) (0 : Fin 13) mem0
  by_cases ha : a.val < 26
  · by_cases hp : a.val < 13
    · have hAw : (C.wires (List.ofFn (row Sall))).getD a.val false = true := by
        rw [wires_input _ _ (Nat.lt_trans hp (by decide))]
        exact point_on_all a.val hp
      have hfalse := hnegAll
      have htrue : GateOp.or.eval
          [(C.wires (List.ofFn (row Sall))).getD a.val false,
           (C.wires (List.ofFn (row Sall))).getD b.val false] = true :=
        or_true_left _ _ hAw
      cases (htrue.symm.trans hfalse)
    · have h13 : 13 ≤ a.val := Nat.le_of_not_lt hp
      have hAw : (C.wires (List.ofFn (row Semp))).getD a.val false = true := by
        rw [wires_input _ _ ha]
        exact line_on_empty a.val h13 ha
      have hfalse := hneg0
      have htrue : GateOp.or.eval
          [(C.wires (List.ofFn (row Semp))).getD a.val false,
           (C.wires (List.ofFn (row Semp))).getD b.val false] = true :=
        or_true_left _ _ hAw
      cases (htrue.symm.trans hfalse)
  by_cases hb : b.val < 26
  · by_cases hp : b.val < 13
    · have hBw : (C.wires (List.ofFn (row Sall))).getD b.val false = true := by
        rw [wires_input _ _ (Nat.lt_trans hp (by decide))]
        exact point_on_all b.val hp
      have hfalse := hnegAll
      have htrue : GateOp.or.eval
          [(C.wires (List.ofFn (row Sall))).getD a.val false,
           (C.wires (List.ofFn (row Sall))).getD b.val false] = true :=
        or_true_right _ _ hBw
      cases (htrue.symm.trans hfalse)
    · have h13 : 13 ≤ b.val := Nat.le_of_not_lt hp
      have hBw : (C.wires (List.ofFn (row Semp))).getD b.val false = true := by
        rw [wires_input _ _ hb]
        exact line_on_empty b.val h13 hb
      have hfalse := hneg0
      have htrue : GateOp.or.eval
          [(C.wires (List.ofFn (row Semp))).getD a.val false,
           (C.wires (List.ofFn (row Semp))).getD b.val false] = true :=
        or_true_right _ _ hBw
      cases (htrue.symm.trans hfalse)
  have ha26 : 26 ≤ a.val := Nat.le_of_not_lt ha
  have hb26 : 26 ≤ b.val := Nat.le_of_not_lt hb
  have haig : a.val - 26 < C.gates.length := by
    have : a.val < 26 + C.size := a.isLt
    omega
  have hmem : NestedCover.gateAt C (a.val - 26) ∈ C.gates := by
    change C.gates.getD (a.val - 26) ⟨GateOp.or, []⟩ ∈ C.gates
    rw [List.getD_eq_getElem (l := C.gates) (n := a.val - 26) ⟨GateOp.or, []⟩ haig]
    exact List.getElem_mem haig
  have hCgate : (NestedCover.gateAt C (a.val - 26)).op = GateOp.and ∨
      (NestedCover.gateAt C (a.val - 26)).op = GateOp.or :=
    (hC _ hmem).1
  rcases hCgate with hand | hor
  · exact hAND C a b hC hsize hab ha26 hb26 hand hpos hneg
  · exact hOR C a b hC hsize hab ha26 hb26 hor hpos hneg
