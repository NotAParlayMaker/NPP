import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A 15-gate counterexample would end at wire 23. All missing reads can
-- use the same false wire 24, and a NOT needs only its first operand.
theorem PEqualNP.Outside.R_meta_3200_731
    (short : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (search :
      let target (x : Fin 9 → Bool) :=
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (D : Circuit) (j : ℕ), D.gates.length = 15 → D.output = 23 → 6 < j → j < 15 →
        FanInTwo D →
        (∀ i : Fin D.gates.length, (D.gates.get i).op = GateOp.not ↔ i.val = 6 ∨ i.val = j) →
        (∀ i : Fin D.gates.length, let g := D.gates.get i
          (∀ pin ∈ g.inputs, pin < 9 + i.val ∨ pin = 24) ∧
          (g.op = GateOp.not → g.inputs.length ≤ 1)) →
        (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
        ∃ x : Fin 9 → Bool, D.eval (List.ofFn x) ≠ target x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (6 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  classical
  intro C fan negations first computes
  by_contra! tooSmall
  change C.gates.length < 16 at tooSmall
  let target (x : Fin 9 → Bool) :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let coded (x : Fin 9 → Bool) := ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have targetEq : ∀ x : Fin 9 → Bool, target x = coded x := by decide +kernel
  have exactC (x : Fin 9 → Bool) : C.eval (List.ofFn x) = target x := congrFun computes x
  have size : C.gates.length = 15 := by
    by_contra differs
    exact short ⟨C, fan, by change C.gates.length ≤ 14; omega,
      fun x => (exactC x).trans (targetEq x)⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have length (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g tail ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have preserve (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g tail ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have output : C.output = 23 := by
    have valid : C.output < 24 := by
      by_contra! invalid
      have yes := exactC (fun _ => true)
      change (C.gates.foldl step (List.ofFn (fun _ : Fin 9 => true))).getD C.output false = true at yes
      rw [List.getD_eq_default _ _ (by rw [length, List.length_ofFn, size]; exact invalid)] at yes
      contradiction
    by_contra differs
    have early : C.output < 23 := by omega
    let E : Circuit := ⟨C.gates.take 14, C.output⟩
    apply short
    refine ⟨E, (fun g hg => fan g (List.mem_of_mem_take hg)), ?_, fun x => ?_⟩
    · change (C.gates.take 14).length ≤ 14
      simp [size]
    · have eq := preserve (C.gates.drop 14) ((C.gates.take 14).foldl step (List.ofFn x))
        C.output (by rw [length, List.length_ofFn, List.length_take, size]; exact early)
      rw [← List.foldl_append, List.take_append_drop] at eq
      exact eq.symm.trans ((exactC x).trans (targetEq x))
  let clip (j i : ℕ) := if i < 9 + j then i else 24
  let norm (j : ℕ) (g : Gate) : Gate :=
    ⟨g.op, (g.inputs.take (if g.op = GateOp.not then 1 else 2)).map (clip j)⟩
  have normStep (j : ℕ) (w : List Bool) (g : Gate) (hw : w.length = 9 + j)
      (bound : j < 15) (arity : g.inputs.length ≤ 2) : step w (norm j g) = step w g := by
    have read (i : ℕ) : w.getD (clip j i) false = w.getD i false := by
      by_cases hi : i < 9 + j
      · simp only [clip, ite_eq_left hi]
      · rw [show clip j i = 24 by simp only [clip, ite_eq_right hi],
          List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    change w ++ [g.op.eval ((norm j g).inputs.map fun i => w.getD i false)] =
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    simp only [norm, List.map_map, Function.comp_def, read]
    by_cases hnot : g.op = GateOp.not
    · simp only [hnot, ite_true]
      cases g.inputs <;> rfl
    · rw [ite_eq_right hnot, List.take_of_length_le arity]
  have normalized (gs : List Gate) (j : ℕ) (w : List Bool) (hw : w.length = 9 + j)
      (bound : j + gs.length ≤ 15) (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      (gs.mapIdx (fun i g => norm (j + i) g)).foldl step w = gs.foldl step w := by
    induction gs generalizing j w with
    | nil => rfl
    | cons g tail ih =>
      rw [List.mapIdx_cons, List.foldl_cons, List.foldl_cons, Nat.add_zero,
        normStep j w g hw (by simp only [List.length_cons] at bound; omega) (arity g List.mem_cons_self)]
      have eq : (fun i (k : Gate) => norm (j + (i + 1)) k) =
          (fun i (k : Gate) => norm ((j + 1) + i) k) := by
        funext i k
        rw [show j + (i + 1) = (j + 1) + i by omega]
      rw [eq]
      exact ih (j + 1) (step w g) (by simp [step, hw, Nat.add_assoc])
        (by simp only [List.length_cons] at bound; omega) (fun k hk => arity k (List.mem_cons_of_mem g hk))
  let D : Circuit := ⟨C.gates.mapIdx norm, 23⟩
  have lengthD : D.gates.length = 15 := by simp [D, size]
  have allWires (x : Fin 9 → Bool) : D.wires (List.ofFn x) = C.wires (List.ofFn x) := by
    change (C.gates.mapIdx norm).foldl step (List.ofFn x) = C.gates.foldl step (List.ofFn x)
    simpa only [Nat.zero_add] using
      normalized C.gates 0 (List.ofFn x) (by rw [List.length_ofFn]) (by simp [size]) (fun g hg => (fan g hg).2)
  let original (i : Fin D.gates.length) : Fin C.gates.length := ⟨i.val, by rw [size, ← lengthD]; exact i.isLt⟩
  have sameOp (i : Fin D.gates.length) : D.gates.get i = norm i.val (C.gates.get (original i)) :=
    List.getElem_mapIdx
  have fanD : FanInTwo D := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    let ix : Fin D.gates.length := ⟨i, hi⟩
    change (D.gates.get ix).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (D.gates.get ix).inputs.length ≤ 2
    rw [sameOp]
    refine ⟨(fan _ (List.get_mem _ _)).1, ?_⟩
    simp only [norm, List.length_map, List.length_take]
    split <;> omega
  have pins (i : Fin D.gates.length) : let g := D.gates.get i
      (∀ a ∈ g.inputs, a < 9 + i.val ∨ a = 24) ∧ (g.op = GateOp.not → g.inputs.length ≤ 1) := by
    dsimp only
    rw [sameOp]
    constructor
    · intro a ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      unfold clip
      split <;> simp_all
    · intro h
      change (C.gates.get (original i)).op = GateOp.not at h
      simp only [norm, h, ite_true, List.length_map, List.length_take]
      omega
  obtain ⟨a, b, order, aIndex, aNot, bNot, only⟩ := negations
  have pattern (i : Fin D.gates.length) : (D.gates.get i).op = GateOp.not ↔ i.val = 6 ∨ i.val = b.val := by
    rw [sameOp]
    change (C.gates.get (original i)).op = GateOp.not ↔ _
    constructor
    · intro isNot
      simpa only [original, ← aIndex, Fin.ext_iff] using only (original i) isNot
    · intro atNot
      rcases atNot with ha | hb
      · have eq : original i = a := Fin.ext (ha.trans aIndex.symm)
        rwa [eq]
      · have eq : original i = b := Fin.ext hb
        rwa [eq]
  obtain ⟨x, diff⟩ := search D b.val lengthD rfl (by omega) (by rw [← size]; exact b.isLt)
    fanD pattern pins (fun x => by rw [allWires]; exact first x)
  apply diff
  change (D.wires (List.ofFn x)).getD 23 false = target x
  rw [allWires, ← output]
  exact exactC x
