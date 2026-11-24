import PEqualNP.Defs

-- A reduction of L-meta-1682, the order-3 plane bound of 64 gates for fan-in-two
-- AND/OR circuits that are true at every incident pair and false at every generic
-- maximal false input, to two smaller statements, split by the operation of the
-- gate that produces the output wire of the circuit: an OR output gate, and an
-- AND output gate. No hypothesis is needed for a circuit whose output wire is
-- not produced by a gate: such a circuit computes one input or the constant
-- false, and neither is true at every incident pair, as the implication below
-- shows. The incidence conditions are written with the line of w spelled out as
-- the four points w, w + 1, w + 3, w + 9.

theorem PEqualNP.Outside.R_meta_1682_1
    (h_or : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧
      (∀ p w : Fin 13, (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) →
        PEqualNP.MetaComplexity.circuitFun (13 + 13) C
          (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
      (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13,
          (∀ pp ∈ P, ¬ (pp = w2 ∨ pp = w2 + 1 ∨ pp = w2 + 3 ∨ pp = w2 + 9)) ∧
          (v = w2 ∨ v = w2 + 1 ∨ v = w2 + 3 ∨ v = w2 + 9)) →
        ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (p3 = w3 ∨ p3 = w3 + 1 ∨ p3 = w3 + 3 ∨ p3 = w3 + 9)) ∧
        ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13,
          (∀ pp ∈ P, ¬ (pp = w4 ∨ pp = w4 + 1 ∨ pp = w4 + 3 ∨ pp = w4 + 9)) →
          (v4 = w4 ∨ v4 = w4 + 1 ∨ v4 = w4 + 3 ∨ v4 = w4 + 9)) →
        PEqualNP.MetaComplexity.circuitFun (13 + 13) C
          (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
            (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
              (∀ pp ∈ P, ¬ (pp = ww ∨ pp = ww + 1 ∨ pp = ww + 3 ∨ pp = ww + 9))))) = false) ∧
      (∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.output = 13 + 13 + k ∧
        C.gates[k]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)))
    (h_and : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧
      (∀ p w : Fin 13, (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) →
        PEqualNP.MetaComplexity.circuitFun (13 + 13) C
          (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
      (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13,
          (∀ pp ∈ P, ¬ (pp = w2 ∨ pp = w2 + 1 ∨ pp = w2 + 3 ∨ pp = w2 + 9)) ∧
          (v = w2 ∨ v = w2 + 1 ∨ v = w2 + 3 ∨ v = w2 + 9)) →
        ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (p3 = w3 ∨ p3 = w3 + 1 ∨ p3 = w3 + 3 ∨ p3 = w3 + 9)) ∧
        ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13,
          (∀ pp ∈ P, ¬ (pp = w4 ∨ pp = w4 + 1 ∨ pp = w4 + 3 ∨ pp = w4 + 9)) →
          (v4 = w4 ∨ v4 = w4 + 1 ∨ v4 = w4 + 3 ∨ v4 = w4 + 9)) →
        PEqualNP.MetaComplexity.circuitFun (13 + 13) C
          (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
            (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
              (∀ pp ∈ P, ¬ (pp = ww ∨ pp = ww + 1 ∨ pp = ww + 3 ∨ pp = ww + 9))))) = false) ∧
      (∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.output = 13 + 13 + k ∧
        C.gates[k]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and))) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  intro hex
  obtain ⟨C, hmono, hsize, htrue, hfalse⟩ := hex
  have key : ∀ a b : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), a = b + dd) ↔
      (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) := by
    intro a b
    simp
  simp only [key] at htrue hfalse
  -- Wire values: the fold that computes the wires keeps the input prefix, and a
  -- wire index past the end of the wire list reads false.
  have wires_eq : ∀ y : List Bool, C.wires y = C.gates.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y := fun y => rfl
  have getD_app : ∀ (l l' : List Bool) (i : ℕ), i < l.length →
      (l ++ l').getD i false = l.getD i false := by
    intro l l' i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_none : ∀ (l : List Bool) (i : ℕ), l.length ≤ i → l.getD i false = false := by
    intro l i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have fold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (y : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).length =
        y.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro y; rfl
    | cons g gs ih =>
      intro y
      rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]
      omega
  have fold_getD : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (y : List Bool) (i : ℕ),
      i < y.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD
        i false = y.getD i false := by
    intro gs
    induction gs with
    | nil => intro y i _; rfl
    | cons g gs ih =>
      intro y i hi
      rw [List.foldl_cons, ih _ _ (by rw [List.length_append, List.length_singleton]; omega)]
      exact getD_app _ _ _ hi
  have eval_input : ∀ (h : C.output < 13 + 13) (x : Fin (13 + 13) → Bool),
      PEqualNP.MetaComplexity.circuitFun (13 + 13) C x = x ⟨C.output, h⟩ := by
    intro h x
    show (C.wires (List.ofFn x)).getD C.output false = x ⟨C.output, h⟩
    rw [wires_eq, fold_getD _ _ _ (by simpa using h),
      List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [h]
  have eval_false : ∀ (h : 13 + 13 + C.gates.length ≤ C.output) (x : Fin (13 + 13) → Bool),
      PEqualNP.MetaComplexity.circuitFun (13 + 13) C x = false := by
    intro h x
    show (C.wires (List.ofFn x)).getD C.output false = false
    apply getD_none
    rw [wires_eq, fold_len]
    simpa using h
  -- Every input coordinate is missed by some incident pair: the pair through the
  -- point 0 or 1 (or the line 0 or 1) whose two coordinates both differ from it.
  have avoid : ∀ m : Fin (13 + 13), ∃ p w : Fin 13,
      (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) ∧
      m ≠ Fin.castAdd 13 p ∧ m ≠ Fin.natAdd 13 w := by
    intro m
    by_cases hm : m.val < 13
    · refine ⟨⟨if m.val = 0 then 1 else 0, by split <;> omega⟩,
        ⟨if m.val = 0 then 1 else 0, by split <;> omega⟩, Or.inl rfl, ?_, ?_⟩
      · intro hcon
        have hv : m.val = (if m.val = 0 then 1 else 0) := by
          have h2 := congrArg Fin.val hcon
          rwa [Fin.val_castAdd] at h2
        split at hv <;> omega
      · intro hcon
        have hv : m.val = 13 + (if m.val = 0 then 1 else 0) := by
          have h2 := congrArg Fin.val hcon
          rwa [Fin.val_natAdd] at h2
        omega
    · refine ⟨⟨if m.val = 13 then 1 else 0, by split <;> omega⟩,
        ⟨if m.val = 13 then 1 else 0, by split <;> omega⟩, Or.inl rfl, ?_, ?_⟩
      · intro hcon
        have hv : m.val = (if m.val = 13 then 1 else 0) := by
          have h2 := congrArg Fin.val hcon
          rwa [Fin.val_castAdd] at h2
        split at hv <;> omega
      · intro hcon
        have hv : m.val = 13 + (if m.val = 13 then 1 else 0) := by
          have h2 := congrArg Fin.val hcon
          rwa [Fin.val_natAdd] at h2
        split at hv <;> omega
  by_cases hgate : ∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      C.output = 13 + 13 + k ∧ C.gates[k]? = some g
  · obtain ⟨k, g, hout, hg⟩ := hgate
    have hgmem : g ∈ C.gates := by
      obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hg
      exact List.getElem_mem hk
    obtain ⟨hop, -⟩ := hmono g hgmem
    have hop' : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact hop
    rcases hop' with hopand | hopor
    · exact h_and ⟨C, hmono, hsize, htrue, hfalse, k, g, hout, hg, hopand⟩
    · exact h_or ⟨C, hmono, hsize, htrue, hfalse, k, g, hout, hg, hopor⟩
  · -- No gate produces the output wire. Then the circuit computes a single input
    -- or the constant false, and neither is true at every incident pair.
    by_cases hout : C.output < 13 + 13
    · obtain ⟨p, w, hinc, hne1, hne2⟩ := avoid ⟨C.output, hout⟩
      have hval := htrue p w hinc
      rw [eval_input hout] at hval
      have hprop : (⟨C.output, hout⟩ : Fin (13 + 13)) = Fin.castAdd 13 p ∨
          (⟨C.output, hout⟩ : Fin (13 + 13)) = Fin.natAdd 13 w :=
        of_decide_eq_true hval
      rcases hprop with h | h
      · exact hne1 h
      · exact hne2 h
    · by_cases hlen : C.output < 13 + 13 + C.gates.length
      · exact hgate ⟨C.output - (13 + 13),
          C.gates[C.output - (13 + 13)]'(by omega), by omega,
          List.getElem?_eq_getElem (by omega)⟩
      · have hle : 13 + 13 + C.gates.length ≤ C.output := by omega
        have ht := htrue 0 0 (Or.inl rfl)
        have hf := eval_false hle (fun k => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨
          k = Fin.natAdd 13 (0 : Fin 13)))
        rw [ht] at hf
        exact absurd hf (by decide)
