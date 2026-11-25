import Mathlib
import PEqualNP.Defs

-- Cut: a double re-read gate forces nested AND gates; least circuits are flat (h1); flat
-- circuits need 27 gates (h2).
-- Model: every gate is AND or OR and reads two distinct earlier wires. F: the Fano incidence
-- function of the statement (point p on line l iff p - l is 0, 1 or 3 mod 7).
-- NESTED: some AND gate lies strictly inside the cone (InCone) of an AND gate which is the
-- output or lies in the cone of the output (the nesting of the accepted reduction
-- R_meta_1692_1 for the plane of order 3, restricted to the live part of the circuit).
-- h1 (open core, the single-level claim for the Fano plane up to 27 gates): a least circuit of
-- the model for F with at most 27 gates has no nested AND gates. Below 27 gates this is the
-- shrink step of R_meta_1692_1 in least-circuit form; at 27 gates it says optimal circuits are
-- flat. Evidence: the cheap nestings, such as (T OR x_c) AND Y_c = T OR x_c Y_c for a line
-- star T through the point c, cost what a flat MIXED star design costs, and a star design
-- reaches 27 only with all 7 lines or all 7 points as centres (the only vertex covers of size
-- 7 of the Heawood graph); on two lines of the plane, a SAT search gives least size 7 and no
-- nested circuit of 7 gates (a nested one needs 8).
-- h2 (finishable, star counting): a circuit of the model for F with no nested AND gates has at
-- least 27 gates. Sketch: every AND gate then reads OR trees of inputs and is below F, so by
-- the absence of 4-cycles it is a star (one centre c, leaves in N(c)); the output is an OR
-- tree over stars (an input or a lower OR in it would make F true on one variable); an OR gate
-- under a leaf operand covers at least two inputs and serves one centre only; for each centre
-- c the stars of centre c and the OR gates under them number at least the leaves met at c;
-- the stars cover all 21 incidences, so at least 7 stars, and the top OR tree has at least
-- (number of stars - 1) gates: 21 + 7 - 1 = 27 (|E| + tau - 1 for the Heawood graph).
-- Proof below: with h1 and h2 a least circuit has at least 27 gates, so the given circuit is
-- least and h1 makes it flat. But an operand of the double re-read gate is true at 1_(0,7)
-- and false at 1_0 and at 1_7, so it is not an input wire; following OR gates (some operand
-- keeps the property) one reaches an AND gate inside the cone of the double re-read gate.
theorem PEqualNP.Outside.R_meta_1965_102 (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) → (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) → (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) → (∀ (y1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), y1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) → (∀ (x2 : Fin (14 : ℕ) → Bool), y1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) → x1.size ≤ y1.size) → ¬(∃ (x2 : ℕ) (x3 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))))) (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) → (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) → ¬(∃ (x2 : ℕ) (x3 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ)))) → (27 : ℕ) ≤ x1.size) : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x3 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false ∧ PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  classical
  rintro ⟨C, hsize, hmodel, hcorrect, g, hgand, hgcone, hgval, hops⟩
  -- pass to a least circuit: by h1 it is flat, by h2 it has at least 27 gates
  have hex : ∃ (s : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), D.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), D.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ D.size = s :=
    ⟨C.size, C, hmodel, hcorrect, rfl⟩
  obtain ⟨M, hMm, hMc, hMs⟩ := Nat.find_spec hex
  have hMmin : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), D.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) → (∀ (x2 : Fin (14 : ℕ) → Bool), D.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) → M.size ≤ D.size := by
    intro D hDm hDc
    rw [hMs]
    exact Nat.find_min' hex ⟨D, hDm, hDc, rfl⟩
  have hMC : M.size ≤ C.size := hMmin C hmodel hcorrect
  have hM27 : (27 : ℕ) ≤ M.size := h2 M hMm hMc (h1 M (by omega) hMm hMc hMmin)
  have hCmin : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), D.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) → (∀ (x2 : Fin (14 : ℕ) → Bool), D.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) → C.size ≤ D.size := by
    intro D hDm hDc
    have hD := hMmin D hDm hDc
    omega
  -- so the given circuit is least; it remains to show that it is nested
  apply h1 C hsize hmodel hcorrect hCmin
  -- wire semantics of the root model
  have wlen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [PEqualNP.CircuitLowerBounds.Circuit.wires]
    | cons a gs ih =>
      intro w
      change (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)])).length = _
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have wlt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ), i < w.length →
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons a gs ih =>
      intro w i hi
      change (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)])).getD i false = _
      have hlt : i < (w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih _ i hlt]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hi]
  have wsnoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (a : PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [a], 0⟩ w = PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w ++
        [a.op.eval (a.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w).getD i false)] := by
    intro gs a w
    simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have wchar : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j : ℕ), j < gs.length →
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w).getD (w.length + j) false =
        (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op.eval ((gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.map fun i =>
          if i < w.length + j then (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w).getD i false else false) := by
    intro gs w
    induction gs using List.reverseRecOn with
    | nil => intro j hj; simp at hj
    | append_singleton gs a ih =>
      intro j hj
      rw [wsnoc]
      have hlen := wlen gs w
      simp only [List.length_append, List.length_singleton] at hj
      have key : ∀ i, i < w.length + gs.length →
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w ++ [a.op.eval (a.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w).getD i false)]).getD i false
            = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w).getD i false := by
        intro i hi
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_or_ge j gs.length with h | h
      · have e1 : (gs ++ [a]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [e1, key _ (by omega), ih j h]
        congr 1
        apply List.map_congr_left
        intro i _
        split_ifs with hi
        · rw [key i (by omega)]
        · rfl
      · have hj' : j = gs.length := by omega
        subst hj'
        have e1 : (gs ++ [a]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = a := by
          simp [List.getD_eq_getElem?_getD]
        rw [e1]
        have e2 : (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w ++ [a.op.eval (a.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w).getD i false)]).getD (w.length + gs.length) false =
            a.op.eval (a.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w).getD i false) := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [e2]
        congr 1
        apply List.map_congr_left
        intro i _
        split_ifs with hi
        · rw [key i hi]
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by omega)]
          rfl
  -- specialised to the circuit C on 14 inputs
  have hCw : ∀ x : List Bool, C.wires x = PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.gates, 0⟩ x := fun x => rfl
  have vin : ∀ (v : Fin 14 → Bool) (w : ℕ) (hw : w < 14), (C.wires (List.ofFn v)).getD w false = v ⟨w, hw⟩ := by
    intro v w hw
    rw [hCw, wlt C.gates (List.ofFn v) w (by simpa using hw)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw, Option.getD_some]
  have vbeyond : ∀ (v : Fin 14 → Bool) (w : ℕ), 14 + C.gates.length ≤ w → (C.wires (List.ofFn v)).getD w false = false := by
    intro v w hw
    have hl : (C.wires (List.ofFn v)).length ≤ w := by
      rw [hCw, wlen]
      simpa using hw
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl, Option.getD_none]
  have vgate : ∀ (v : Fin 14 → Bool) (j : ℕ), j < C.gates.length →
      (C.wires (List.ofFn v)).getD (14 + j) false =
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map fun i =>
          if i < 14 + j then (C.wires (List.ofFn v)).getD i false else false) := by
    intro v j hj
    have h := wchar C.gates (List.ofFn v) j hj
    simp only [List.length_ofFn] at h
    rw [hCw]
    exact h
  -- the gates of C
  have hgate : ∀ j, j < C.gates.length → ∃ a b : ℕ,
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b] ∧ a < 14 + j ∧ b < 14 + j := by
    intro j hj
    have hget : C.gates[j]? = Option.some (C.gates[j]) := List.getElem?_eq_getElem hj
    obtain ⟨hop, a, b, hin, -, ha, hb⟩ := hmodel j _ hget
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some]
    rw [hg]
    exact ⟨a, b, hop, hin, ha, hb⟩
  -- cones
  have clen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
      (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons a gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      simp [PEqualNP.EdgeOwnership.coneStep]
      omega
  have cchar : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (i j : ℕ), i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, 14 ≤ w ∧ w < 14 + j ∧
        (i = w - 14 ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs a ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).length = gs.length := by
        rw [clen]; simp
      have key : ∀ k, k < gs.length →
          (PEqualNP.EdgeOwnership.coneStep 14 (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) a).getD k [] = (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD k [] := by
        intro k hk
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [a]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, k1, k2, k3⟩
          refine ⟨by simp; omega, w, hw, k1, k2, ?_⟩
          rw [key (w - 14) (by omega)]
          exact k3
        · rintro ⟨_, w, hw, k1, k2, k3⟩
          refine ⟨h, w, hw, k1, k2, ?_⟩
          rw [key (w - 14) (by omega)] at k3
          exact k3
      · subst h
        have e1 : (gs ++ [a]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = a := by
          simp [List.getD_eq_getElem?_getD]
        have e2 : (PEqualNP.EdgeOwnership.coneStep 14 (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) a).getD gs.length [] =
            (a.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + gs.length))).flatMap
              (fun w => (w - 14) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
          simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [e2, e1]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, k1, k2⟩, k3⟩
          refine ⟨by simp, w, hw, k1, k2, ?_⟩
          rw [key (w - 14) (by omega)]
          exact k3
        · rintro ⟨_, w, hw, k1, k2, k3⟩
          rw [key (w - 14) (by omega)] at k3
          exact ⟨w, ⟨hw, k1, k2⟩, k3⟩
      · have e0 : (PEqualNP.EdgeOwnership.coneStep 14 (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) a).getD j [] = [] := by
          simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩
          simp at h0
          omega
  -- a gate reading the wire of gate k (k itself or a gate in the cone of k) has it in its cone
  have inCone_read : ∀ i j k : ℕ, j < C.gates.length → k < j →
      14 + k ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs →
      (i = k ∨ PEqualNP.EdgeOwnership.InCone 14 C i k) → PEqualNP.EdgeOwnership.InCone 14 C i j := by
    intro i j k hj hkj hin hik
    unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones
    rw [cchar]
    refine ⟨hj, 14 + k, hin, by omega, by omega, ?_⟩
    have e : 14 + k - 14 = k := by omega
    rw [e]
    exact hik
  -- no input wire is true at 1_(0,7) and false at 1_0 and at 1_7
  have hinputs : ∀ (w : ℕ) (hw : w < 14),
      PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14) ⟨w, hw⟩ = true →
      PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (0 : Fin 14) ⟨w, hw⟩ = false →
      PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) (7 : Fin 14) ⟨w, hw⟩ = false → False := by
    intro w hw hx h0 h7
    simp [PEqualNP.EdgeOwnership.pairInput, Fin.ext_iff] at hx h0 h7
    all_goals omega
  -- creation: a wire true at 1_(0,7) and false at 1_0 and at 1_7 is a gate wire with an AND
  -- gate in its reflexive cone
  have create : ∀ w : ℕ, (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14)))).getD w false = true → (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (0 : Fin 14)))).getD w false = false →
      (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) (7 : Fin 14)))).getD w false = false → 14 ≤ w ∧ ∃ i : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (i = w - 14 ∨ PEqualNP.EdgeOwnership.InCone 14 C i (w - 14)) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hx h0 h7
      by_cases hw : w < 14
      · rw [vin _ w hw] at hx
        rw [vin _ w hw] at h0
        rw [vin _ w hw] at h7
        exact (hinputs w hw hx h0 h7).elim
      · by_cases hlt : w < 14 + C.gates.length
        · obtain ⟨j, rfl⟩ : ∃ j, w = 14 + j := ⟨w - 14, by omega⟩
          have hj : j < C.gates.length := by omega
          obtain ⟨a, b, hop, hin, ha, hb⟩ := hgate j hj
          have hjj : 14 + j - 14 = j := by omega
          rw [hjj]
          rcases hop with hand | hor
          · exact ⟨by omega, j, hand, Or.inl rfl⟩
          · have ev : ∀ v : Fin 14 → Bool, (C.wires (List.ofFn v)).getD (14 + j) false =
                ((C.wires (List.ofFn v)).getD a false || (C.wires (List.ofFn v)).getD b false) := by
              intro v
              rw [vgate v j hj, hor, hin]
              simp [PEqualNP.CircuitLowerBounds.GateOp.eval, ha, hb]
            rw [ev] at hx
            rw [ev] at h0
            rw [ev] at h7
            rw [Bool.or_eq_false_iff] at h0
            rw [Bool.or_eq_false_iff] at h7
            have hx' : (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14)))).getD a false = true ∨ (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14)))).getD b false = true := by
              simpa using hx
            rcases hx' with hxa | hxb
            · obtain ⟨ha14, i, hi, hc⟩ := ih a (by omega) hxa h0.1 h7.1
              refine ⟨by omega, i, hi, Or.inr ?_⟩
              apply inCone_read i j (a - 14) hj (by omega)
              · rw [hin, show 14 + (a - 14) = a by omega]
                simp
              · exact hc
            · obtain ⟨hb14, i, hi, hc⟩ := ih b (by omega) hxb h0.2 h7.2
              refine ⟨by omega, i, hi, Or.inr ?_⟩
              apply inCone_read i j (b - 14) hj (by omega)
              · rw [hin, show 14 + (b - 14) = b by omega]
                simp
              · exact hc
        · rw [vbeyond _ w (by omega)] at hx
          exact absurd hx (by simp)
  -- the double re-read gate g reads a wire that creates the incidence (0, 0)
  have hg : g < C.gates.length := by
    by_contra hge
    have hle : C.gates.length ≤ g := by omega
    have hd : PEqualNP.MetaComplexity.NestedCover.gateAt C g = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle, Option.getD_none]
    rw [hd] at hgand
    exact absurd hgand (by simp)
  obtain ⟨a, b, -, hin, ha, hb⟩ := hgate g hg
  have hval : (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14)))).getD (14 + g) false =
      ((C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14)))).getD a false && (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14)))).getD b false) := by
    rw [vgate _ g hg, hgand, hin]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval, ha, hb]
  have hgv : (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) (7 : Fin 14)))).getD (14 + g) false = true := hgval
  rw [hval, Bool.and_eq_true] at hgv
  have hopnd : PEqualNP.TopForm.opnd C g 0 = a := by
    unfold PEqualNP.TopForm.opnd
    rw [hin]
    rfl
  obtain ⟨h0, h7⟩ := hops 0
  rw [hopnd] at h0
  rw [hopnd] at h7
  obtain ⟨ha14, i, hi, hc⟩ := create a hgv.1 h0 h7
  refine ⟨i, g, hi, hgand, ?_, hgcone⟩
  apply inCone_read i g (a - 14) hg (by omega)
  · rw [hin, show 14 + (a - 14) = a by omega]
    simp
  · exact hc
