import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2341_691
    (flat : ∀ (C : Circuit) (missingPoint missingLine : Fin 13), Monotone2 C → NestedCover.ReadsBack 26 C →
      let differences : Finset (Fin 13) := {0, 1, 3, 9}
      let positiveRow (point line : Fin 13) :=
        List.ofFn (fun index : Fin 13 => decide (index = point)) ++
          List.ofFn (fun index : Fin 13 => decide (index = line))
      let negativeRow (quadrangle : Finset (Fin 13)) :=
        List.ofFn (fun point : Fin 13 => decide (point ∈ quadrangle)) ++
          List.ofFn (fun line : Fin 13 => decide (∀ point ∈ quadrangle, point - line ∉ differences))
      (∀ point line, point - line ∈ differences → (point ≠ missingPoint ∨ line ≠ missingLine) →
        C.eval (positiveRow point line) = true) →
      (∀ quadrangle, quadrangle.card = 4 →
        (∀ line : Fin 13, (quadrangle.filter (fun point => point - line ∈ differences)).card ≤ 2) →
        C.eval (negativeRow quadrangle) = false) →
      ¬ (∃ i j : ℕ, (NestedCover.gateAt C i).op = GateOp.and ∧
        (NestedCover.gateAt C j).op = GateOp.and ∧ EdgeOwnership.InCone 26 C i j) → 63 ≤ C.size)
    (nested : ∀ (C : Circuit) (missingPoint missingLine : Fin 13), Monotone2 C → NestedCover.ReadsBack 26 C →
      let differences : Finset (Fin 13) := {0, 1, 3, 9}
      let positiveRow (point line : Fin 13) :=
        List.ofFn (fun index : Fin 13 => decide (index = point)) ++
          List.ofFn (fun index : Fin 13 => decide (index = line))
      let negativeRow (quadrangle : Finset (Fin 13)) :=
        List.ofFn (fun point : Fin 13 => decide (point ∈ quadrangle)) ++
          List.ofFn (fun line : Fin 13 => decide (∀ point ∈ quadrangle, point - line ∉ differences))
      (∀ point line, point - line ∈ differences → (point ≠ missingPoint ∨ line ≠ missingLine) →
        C.eval (positiveRow point line) = true) →
      (∀ quadrangle, quadrangle.card = 4 →
        (∀ line : Fin 13, (quadrangle.filter (fun point => point - line ∈ differences)).card ≤ 2) →
        C.eval (negativeRow quadrangle) = false) →
      (∃ i j : ℕ, (NestedCover.gateAt C i).op = GateOp.and ∧
        (NestedCover.gateAt C j).op = GateOp.and ∧ EdgeOwnership.InCone 26 C i j) → 63 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ x2 ∨ x12 ≠ x3 → x1.eval (x8 x11 x12 ++ [x4]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [x4]) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  let shifted (n wire : ℕ) : ℕ :=
    if wire < n then wire else wire - 1

  let patched (n : ℕ) (bit : Bool) (gate : Gate) : Gate :=
    let inputs := (gate.inputs.filter (· != n)).map (shifted n)
    GateOp.rec (motive := fun _ => Gate)
      (if !bit && gate.inputs.contains n then ⟨.or, []⟩ else ⟨.and, inputs⟩)
      (if bit && gate.inputs.contains n then ⟨.and, []⟩ else ⟨.or, inputs⟩)
      ⟨.not, inputs⟩ (fun modulus => ⟨.mod modulus, inputs⟩) ⟨.maj, inputs⟩ gate.op

  have readShifted (beforePin suffix : List Bool) (n : ℕ) (bit : Bool)
      (width : beforePin.length = n) (wire : ℕ) (different : wire ≠ n) :
      (beforePin ++ suffix).getD (shifted n wire) false =
        (beforePin ++ bit :: suffix).getD wire false := by
    by_cases before : wire < n
    · have inPrefix : wire < beforePin.length := by omega
      simp only [shifted, ite_eq_left before, List.getD_append _ _ _ _ inPrefix]
    · have oldPast : beforePin.length ≤ wire := by omega
      have newPast : beforePin.length ≤ wire - 1 := by omega
      have offset : wire - beforePin.length = (wire - 1 - beforePin.length) + 1 := by omega
      simp only [shifted, ite_eq_right before, List.getD_append_right _ _ _ _ oldPast,
        List.getD_append_right _ _ _ _ newPast, offset, List.getD_cons_succ]

  have readPinned (beforePin suffix : List Bool) (n : ℕ) (bit : Bool)
      (width : beforePin.length = n) :
      (beforePin ++ bit :: suffix).getD n false = bit := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [width]

  have validGate (n : ℕ) (bit : Bool) (gate : Gate)
      (valid : gate.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ gate.inputs.length ≤ 2) :
      (patched n bit gate).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        (patched n bit gate).inputs.length ≤ 2 := by
    rcases gate with ⟨op, inputs⟩
    have size := valid.2
    change inputs.length ≤ 2 at size
    have shortened : (inputs.filter (· != n)).length ≤ 2 :=
      (List.length_filter_le _ _).trans size
    obtain choice | choice : op = .and ∨ op = .or := by simpa using valid.1
    · subst op
      simp only [patched]
      split <;> simp [shortened]
    · subst op
      simp only [patched]
      split <;> simp [shortened]

  have patchedReads (n : ℕ) (bit : Bool) (gate : Gate) (wire : ℕ)
      (read : wire ∈ (patched n bit gate).inputs) :
      ∃ original ∈ gate.inputs, original ≠ n ∧ wire = shifted n original := by
    have part (h : wire ∈ (gate.inputs.filter (· != n)).map (shifted n)) :
        ∃ original ∈ gate.inputs, original ≠ n ∧ wire = shifted n original := by
      obtain ⟨original, retained, equal⟩ := List.mem_map.mp h
      obtain ⟨member, different⟩ := List.mem_filter.mp retained
      exact ⟨original, member, by simpa using different, equal.symm⟩
    cases gate with
    | mk op inputs =>
      cases op <;> simp only [patched] at read
      · split at read <;> first | exact part read | simp at read
      · split at read <;> first | exact part read | simp at read
      · exact part read
      · exact part read
      · exact part read

  have gateMeaning (beforePin suffix : List Bool) (n : ℕ) (bit : Bool) (width : beforePin.length = n)
      (gate : Gate) (valid : gate.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ gate.inputs.length ≤ 2) :
      (patched n bit gate).op.eval
        ((patched n bit gate).inputs.map (fun v => (beforePin ++ suffix).getD v false)) =
        gate.op.eval (gate.inputs.map (fun v => (beforePin ++ bit :: suffix).getD v false)) := by
    let original := fun v => (beforePin ++ bit :: suffix).getD v false
    let reduced := fun v => (beforePin ++ suffix).getD v false
    have sameAtPin : original n = bit := readPinned beforePin suffix n bit width
    have rest :
        ((gate.inputs.filter (· != n)).map (shifted n)).map reduced =
          (gate.inputs.filter (· != n)).map original := by
      rw [List.map_map]
      apply List.map_congr_left
      intro wire mem
      have different : wire ≠ n := by simpa using (List.mem_filter.mp mem).2
      exact readShifted beforePin suffix n bit width wire different
    have absent (missing : n ∉ gate.inputs) : gate.inputs.filter (· != n) = gate.inputs := by
      apply List.filter_eq_self.mpr
      intro wire member
      have different : wire ≠ n := fun equal => missing (equal ▸ member)
      simpa using different
    have andNeutral (hb : bit = true) :
        ((gate.inputs.filter (· != n)).map original).all id =
          (gate.inputs.map original).all id := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.mem_map, id_eq]
      constructor
      · intro smaller value member
        obtain ⟨wire, hwire, rfl⟩ := member
        by_cases same : wire = n
        · simp [same, sameAtPin, hb]
        · exact smaller _ ⟨wire, List.mem_filter.mpr ⟨hwire, by simpa using same⟩, rfl⟩
      · intro larger value member
        obtain ⟨wire, hwire, rfl⟩ := member
        exact larger _ ⟨wire, (List.mem_filter.mp hwire).1, rfl⟩
    have orNeutral (hb : bit = false) :
        ((gate.inputs.filter (· != n)).map original).any id =
          (gate.inputs.map original).any id := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_map, id_eq]
      constructor
      · rintro ⟨value, ⟨wire, member, rfl⟩, v⟩
        exact ⟨_, ⟨wire, (List.mem_filter.mp member).1, rfl⟩, v⟩
      · rintro ⟨value, ⟨wire, member, rfl⟩, v⟩
        have diff : wire ≠ n := by
          intro h
          rw [h, sameAtPin, hb] at v
          contradiction
        exact ⟨_, ⟨wire, List.mem_filter.mpr ⟨member, by simpa using diff⟩, rfl⟩, v⟩
    have andAbsorb (hb : bit = false) (hp : n ∈ gate.inputs) :
        (gate.inputs.map original).all id = false := by
      rw [← Bool.not_eq_true]
      intro all
      have atPin := List.all_eq_true.mp all (original n) (List.mem_map_of_mem hp)
      rw [sameAtPin, hb] at atPin
      exact Bool.false_ne_true atPin
    have orAbsorb (hb : bit = true) (hp : n ∈ gate.inputs) :
        (gate.inputs.map original).any id = true :=
      List.any_eq_true.mpr ⟨original n, List.mem_map_of_mem hp, sameAtPin.trans hb⟩
    change (patched n bit gate).op.eval ((patched n bit gate).inputs.map reduced) =
      gate.op.eval (gate.inputs.map original)
    cases gate with
    | mk op inputs =>
      obtain opEq | opEq : op = .and ∨ op = .or := by simpa using valid.1
      · subst op
        cases bit
        · by_cases hp : n ∈ inputs
          · have pin : inputs.contains n = true := List.contains_iff_mem.mpr hp
            simp only [patched, Bool.not_false, Bool.true_and, pin, ite_true]
            change false = (inputs.map original).all id
            exact (andAbsorb rfl hp).symm
          · have pin : inputs.contains n = false := by simpa [List.contains_eq_mem] using hp
            simp only [patched, pin, Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_false]
            change (((inputs.filter (· != n)).map (shifted n)).map reduced).all id =
              (inputs.map original).all id
            rw [rest, absent hp]
        · simp only [patched, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
          change (((inputs.filter (· != n)).map (shifted n)).map reduced).all id =
            (inputs.map original).all id
          rw [rest, andNeutral rfl]
      · subst op
        cases bit
        · simp only [patched, Bool.false_and, Bool.false_eq_true, ite_false]
          change (((inputs.filter (· != n)).map (shifted n)).map reduced).any id =
            (inputs.map original).any id
          rw [rest, orNeutral rfl]
        · by_cases hp : n ∈ inputs
          · have pin : inputs.contains n = true := List.contains_iff_mem.mpr hp
            simp only [patched, Bool.true_and, pin, ite_true]
            change true = (inputs.map original).any id
            exact (orAbsorb rfl hp).symm
          · have pin : inputs.contains n = false := by simpa [List.contains_eq_mem] using hp
            simp only [patched, pin, Bool.true_and, Bool.false_eq_true, ite_false]
            change (((inputs.filter (· != n)).map (shifted n)).map reduced).any id =
              (inputs.map original).any id
            rw [rest, absent hp]

  let push (wires : List Bool) (gate : Gate) : List Bool :=
    wires ++ [gate.op.eval (gate.inputs.map fun v => wires.getD v false)]

  have runMeaning (beforePin : List Bool) (n : ℕ) (bit : Bool) (width : beforePin.length = n)
      (gates : List Gate)
      (valid : ∀ gate ∈ gates, gate.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ gate.inputs.length ≤ 2)
      (suffix : List Bool) :
      ∃ tail : List Bool,
        (gates.map (patched n bit)).foldl push (beforePin ++ suffix) = beforePin ++ tail ∧
        gates.foldl push (beforePin ++ bit :: suffix) = beforePin ++ bit :: tail := by
    induction gates generalizing suffix with
    | nil => exact ⟨suffix, rfl, rfl⟩
    | cons gate rest ih =>
      let byte := gate.op.eval (gate.inputs.map fun v => (beforePin ++ bit :: suffix).getD v false)
      have eval := gateMeaning beforePin suffix n bit width gate (valid gate List.mem_cons_self)
      have oldMove : push (beforePin ++ bit :: suffix) gate = beforePin ++ bit :: (suffix ++ [byte]) := by
        simp [push, byte, List.append_assoc]
      have newMove : push (beforePin ++ suffix) (patched n bit gate) = beforePin ++ (suffix ++ [byte]) := by
        simp only [push, eval, List.append_assoc, byte]
      obtain ⟨tail, old, fresh⟩ := ih (fun g member => valid g (List.mem_cons_of_mem gate member))
        (suffix ++ [byte])
      exact ⟨tail, by simpa only [List.map_cons, List.foldl_cons, newMove] using old,
        by simpa only [List.foldl_cons, oldMove] using fresh⟩

  have pin (n : ℕ) (C : Circuit) (bit : Bool) :
      Monotone2 C →
      (∀ (i : Fin C.gates.length), ∀ w ∈ (C.gates.get i).inputs, w < n + 1 + i.val) →
      C.output ≠ n →
      ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧
        ∀ row : List Bool, row.length = n → D.eval row = C.eval (row ++ [bit]) := by
    intro valid reads output
    let D : Circuit := ⟨C.gates.map (patched n bit), shifted n C.output⟩
    refine ⟨D, ?_, ?_, ?_, ?_⟩
    · intro gate member
      obtain ⟨original, found, rfl⟩ := List.mem_map.mp member
      exact validGate n bit original (valid original found)
    · intro j hj wire read
      have earlier : j < C.gates.length := by simpa [D] using hj
      have form : gateAt D j = patched n bit (C.gates.get ⟨j, earlier⟩) := by
        unfold gateAt D
        rw [List.getD_eq_getElem _ _ hj]
        simp [D]
      rw [form] at read
      obtain ⟨original, member, diff, rfl⟩ := patchedReads n bit _ wire read
      have bound := reads ⟨j, earlier⟩ original member
      change original < n + 1 + j at bound
      by_cases before : original < n <;> simp [shifted, before] <;> omega
    · change (C.gates.map (patched n bit)).length ≤ C.gates.length
      simp only [List.length_map, le_refl]
    · intro row width
      obtain ⟨tail, fresh, old⟩ := runMeaning row n bit width C.gates valid []
      simp only [List.append_nil] at fresh
      have oldEq : C.gates.foldl push (row ++ [bit]) = row ++ bit :: tail := old
      change ((C.gates.map (patched n bit)).foldl push row).getD (shifted n C.output) false =
        (C.gates.foldl push (row ++ [bit])).getD C.output false
      rw [fresh, oldEq]
      exact readShifted row tail n bit width C.output output
  intro candidate omittedPoint omittedLine bit monotone earlier
  dsimp only
  intro accepts rejects
  let differences : Finset (Fin 13) := {0, 1, 3, 9}
  let positiveRow (point line : Fin 13) :=
    List.ofFn (fun index : Fin 13 => decide (index = point)) ++
      List.ofFn (fun index : Fin 13 => decide (index = line))
  let negativeRow (quadrangle : Finset (Fin 13)) :=
    List.ofFn (fun point : Fin 13 => decide (point ∈ quadrangle)) ++
      List.ofFn (fun line : Fin 13 => decide (∀ point ∈ quadrangle, point - line ∉ differences))
  let good (quadrangle : Finset (Fin 13)) :=
    quadrangle.card = 4 ∧ ∀ line : Fin 13, (quadrangle.filter (fun point => point - line ∈ differences)).card ≤ 2
  let step (wires : List Bool) (gate : Gate) :=
    wires ++ [gate.op.eval (gate.inputs.map fun index => wires.getD index false)]
  have invariant (gates : List Gate) (wires : List Bool) (index : ℕ) (inRange : index < wires.length) :
      (gates.foldl step wires).getD index false = wires.getD index false := by
    induction gates generalizing wires with
    | nil => rfl
    | cons gate remaining inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis (step wires gate) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ inRange
  have posLength (point line : Fin 13) : (positiveRow point line).length = 26 := by
    simp [positiveRow]
  have negLength (quadrangle : Finset (Fin 13)) : (negativeRow quadrangle).length = 26 := by
    simp [negativeRow]
  have notConstant : candidate.output ≠ 26 := by
    intro pinned
    have alwaysBit (row : List Bool) (length : row.length = 26) :
        candidate.eval (row ++ [bit]) = bit := by
      change (candidate.gates.foldl step (row ++ [bit])).getD candidate.output false = bit
      rw [pinned, invariant _ _ _ (by simp [length]), ← length]
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl row.length)]
      simp
    have moves : ∀ point : Fin 13, point + 1 ≠ point := by decide +kernel
    let point := omittedPoint + 1
    have diag : point - point ∈ differences := by simp [differences]
    have positive := accepts point point diag (Or.inl (moves omittedPoint))
    have bitTrue : bit = true := (alwaysBit (positiveRow point point) (posLength point point)).symm.trans positive
    let quadrangle : Finset (Fin 13) := {0, 1, 2, 5}
    have proper : good quadrangle := by decide +kernel
    have negative := rejects quadrangle proper
    have bitFalse : bit = false := (alwaysBit (negativeRow quadrangle) (negLength quadrangle)).symm.trans negative
    exact Bool.false_ne_true (bitFalse.symm.trans bitTrue)
  obtain ⟨normalised, normalisedMono, readsBack, size, same⟩ :=
    pin 26 candidate bit monotone earlier notConstant
  have pos (point line : Fin 13) (edge : point - line ∈ differences)
      (other : point ≠ omittedPoint ∨ line ≠ omittedLine) :
      normalised.eval (positiveRow point line) = true :=
    (same (positiveRow point line) (posLength point line)).trans (accepts point line edge other)
  have neg (quadrangle : Finset (Fin 13)) (proper : good quadrangle) :
      normalised.eval (negativeRow quadrangle) = false :=
    (same (negativeRow quadrangle) (negLength quadrangle)).trans (rejects quadrangle proper)
  by_cases hasNested : ∃ i j : ℕ, (NestedCover.gateAt normalised i).op = GateOp.and ∧
      (NestedCover.gateAt normalised j).op = GateOp.and ∧ EdgeOwnership.InCone 26 normalised i j
  · exact (nested normalised omittedPoint omittedLine normalisedMono readsBack pos (fun Q card lines => neg Q ⟨card, lines⟩) hasNested).trans size
  · exact (flat normalised omittedPoint omittedLine normalisedMono readsBack pos (fun Q card lines => neg Q ⟨card, lines⟩) hasNested).trans size
