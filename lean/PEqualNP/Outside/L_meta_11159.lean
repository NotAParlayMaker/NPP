import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11159

open PEqualNP.CircuitLowerBounds

def foldWires (rule : Gate → (ℕ → Bool) → Bool) (gs : List Gate)
    (input : List Bool) : List Bool :=
  gs.foldl (fun prev g => prev ++ [rule g (fun i => prev.getD i false)]) input

theorem fold_cons (rule : Gate → (ℕ → Bool) → Bool) (gs : List Gate)
    (g : Gate) (w : List Bool) :
    foldWires rule (g :: gs) w =
      foldWires rule gs (w ++ [rule g (fun i => w.getD i false)]) := rfl

theorem fold_length (rule : Gate → (ℕ → Bool) → Bool) (gs : List Gate) (w : List Bool) :
    (foldWires rule gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [foldWires]
  | cons g gs ih =>
    rw [fold_cons, ih]
    simp
    omega

theorem fold_prefix (rule : Gate → (ℕ → Bool) → Bool) (gs : List Gate)
    (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (foldWires rule gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [fold_cons, ih _ (by simp; omega)]
    simp [List.getD, List.getElem?_append_left hi]

theorem fold_gate (rule : Gate → (ℕ → Bool) → Bool) (gs : List Gate)
    (w : List Bool) (j : ℕ) (g : Gate) (atGate : gs[j]? = some g) :
    (foldWires rule gs w).getD (w.length + j) false =
      rule g (fun i => if i < w.length + j
        then (foldWires rule gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at atGate
  | cons g0 gs ih =>
    rw [fold_cons]
    let next := w ++ [rule g0 (fun i => w.getD i false)]
    change (foldWires rule gs next).getD (w.length + j) false = _
    cases j with
    | zero =>
      have eq : g0 = g := by simpa using atGate
      subst g
      simp only [Nat.add_zero]
      rw [fold_prefix _ _ _ _ (by simp [next])]
      have point : (fun i => if i < w.length
        then (foldWires rule gs next).getD i false else false) =
          fun i => w.getD i false := by
        funext i
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, fold_prefix _ _ _ _ (by simp [next]; omega)]
          simp [next, List.getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]
          exact (List.getD_eq_default _ _ (Nat.le_of_not_gt hi)).symm
      rw [point]
      simp [next, List.getD]
    | succ j =>
      have h : gs[j]? = some g := by simpa using atGate
      have idx : next.length + j = w.length + (j + 1) := by
        simp [next]; omega
      rw [← idx]
      exact ih next j h

def ordinaryRule (g : Gate) (read : ℕ → Bool) : Bool :=
  g.op.eval (g.inputs.map read)

def derivativeRule (normal : ℕ → Bool) (g : Gate) (read : ℕ → Bool) : Bool :=
  match g.op, g.inputs with
  | .and, [a, b] => (normal a && read b) || (read a && normal b)
  | .or, [a, b] => read a || read b
  | _, _ => false

theorem normalized (n : ℕ) (C : Circuit)
    (legal : ∀ j g, C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j)
    (base seed : Fin n → Bool) (weight : ℕ → ℕ)
    (initialZero : ∀ i : Fin n, base i = true → weight i.val = 0)
    (initialOne : ∀ i : Fin n, seed i = true → weight i.val ≤ 1)
    (recurrence : ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = GateOp.and → weight (n + j) ≤ weight a + weight b) ∧
      (g.op = GateOp.or → weight (n + j) ≤ min (weight a) (weight b))) :
    ∃ d : ℕ → Bool,
      (∀ i : Fin n, d i.val = seed i) ∧
      (∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
        (g.op = GateOp.and →
          d (n + j) = ((C.wires (List.ofFn base)).getD a false && d b ||
            d a && (C.wires (List.ofFn base)).getD b false)) ∧
        (g.op = GateOp.or → d (n + j) = (d a || d b))) ∧
      ∀ i, d i = true → weight i ≤ 1 := by
  let normal (i : ℕ) : Bool := (C.wires (List.ofFn base)).getD i false
  let d (i : ℕ) : Bool :=
    (foldWires (derivativeRule normal) C.gates (List.ofFn seed)).getD i false
  have dInput (i : Fin n) : d i.val = seed i := by
    unfold d
    rw [fold_prefix _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  have normalInput (i : Fin n) : normal i.val = base i := by
    change (foldWires ordinaryRule C.gates (List.ofFn base)).getD i.val false = base i
    rw [fold_prefix _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  have normalGate (j : ℕ) (g : Gate) (a b : ℕ)
      (atGate : C.gates[j]? = some g) (inputs : g.inputs = [a,b])
      (ha : a < n + j) (hb : b < n + j) :
      normal (n + j) = g.op.eval [normal a, normal b] := by
    change (foldWires ordinaryRule C.gates (List.ofFn base)).getD (n + j) false = _
    have h := fold_gate ordinaryRule C.gates (List.ofFn base) j g atGate
    simpa only [List.length_ofFn, ordinaryRule, inputs, List.map_cons, List.map_nil,
      ite_eq_left ha, ite_eq_left hb, normal, foldWires, Circuit.wires] using h
  have dGate (j : ℕ) (g : Gate) (a b : ℕ)
      (atGate : C.gates[j]? = some g) (inputs : g.inputs = [a,b])
      (ha : a < n + j) (hb : b < n + j) :
      (g.op = GateOp.and →
        d (n + j) = (normal a && d b || d a && normal b)) ∧
      (g.op = GateOp.or → d (n + j) = (d a || d b)) := by
    have h := fold_gate (derivativeRule normal) C.gates (List.ofFn seed) j g atGate
    constructor
    · intro op
      simpa only [List.length_ofFn, derivativeRule, inputs, op, ite_eq_left ha, ite_eq_left hb, d] using h
    · intro op
      simpa only [List.length_ofFn, derivativeRule, inputs, op, ite_eq_left ha, ite_eq_left hb, d] using h
  refine ⟨d, dInput, ?_, ?_⟩
  · intro j g a b atGate inputs
    obtain ⟨_, c, e, written, _, hc, he⟩ := legal j g atGate
    have pair : a = c ∧ b = e := by simpa [inputs] using written
    rw [pair.1, pair.2] at inputs ⊢
    exact dGate j g c e atGate inputs hc he
  have both : ∀ i, (normal i = true → weight i = 0) ∧
      (d i = true → weight i ≤ 1) := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases small : i < n
      · exact ⟨fun h => initialZero ⟨i,small⟩ ((normalInput ⟨i,small⟩).symm.trans h),
          fun h => initialOne ⟨i,small⟩ ((dInput ⟨i,small⟩).symm.trans h)⟩
      · let j := i - n
        have idx : i = n + j := by dsimp [j]; omega
        by_cases hj : j < C.gates.length
        · let g := C.gates[j]
          have atGate : C.gates[j]? = some g := List.getElem?_eq_getElem hj
          obtain ⟨op, a, b, inputs, _, ha, hb⟩ := legal j g atGate
          have ng := normalGate j g a b atGate inputs ha hb
          have dg := dGate j g a b atGate inputs ha hb
          have bounds := recurrence j g a b atGate inputs
          have pa := ih a (by omega)
          have pb := ih b (by omega)
          rcases op with h | h
          · have hn := bounds.1 h
            rw [h] at ng
            constructor
            · intro yes
              have : normal a = true ∧ normal b = true := by
                rw [idx, ng] at yes
                simpa [GateOp.eval] using yes
              rw [idx]
              have leftZero := pa.1 this.1
              have rightZero := pb.1 this.2
              omega
            · intro yes
              rw [idx, dg.1 h] at yes
              simp only [Bool.or_eq_true, Bool.and_eq_true] at yes
              rw [idx]
              rcases yes with h₁ | h₂
              · have := pa.1 h₁.1
                have := pb.2 h₁.2
                omega
              · have := pa.2 h₂.1
                have := pb.1 h₂.2
                omega
          · have hn := bounds.2 h
            rw [h] at ng
            have leA := hn.trans (min_le_left _ _)
            have leB := hn.trans (min_le_right _ _)
            constructor
            · intro yes
              have : normal a = true ∨ normal b = true := by
                rw [idx, ng] at yes
                simpa [GateOp.eval] using yes
              rw [idx]
              rcases this with side | side
              · have := pa.1 side
                omega
              · have := pb.1 side
                omega
            · intro yes
              rw [idx, dg.2 h, Bool.or_eq_true] at yes
              rw [idx]
              exact yes.elim (fun h => leA.trans (pa.2 h)) (fun h => leB.trans (pb.2 h))
        · have large : n + C.gates.length ≤ i := by omega
          have nFalse : normal i = false := by
            change (foldWires ordinaryRule C.gates (List.ofFn base)).getD i false = false
            apply List.getD_eq_default
            simpa only [fold_length, List.length_ofFn] using large
          have dFalse : d i = false := by
            apply List.getD_eq_default
            simpa only [fold_length, List.length_ofFn] using large
          simp [nFalse, dFalse]
  exact fun i => (both i).2

end PEqualNP.Outside.L_meta_11159

theorem PEqualNP.Outside.L_meta_11159 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < x1 + x3 ∧ x7 < x1 + x3) →     ∀ (x4 x5 : Fin x1 → Bool) (x6 : ℕ → ℕ),       (∀ (x7 : Fin x1), x4 x7 = Bool.true → x6 ↑x7 = (0 : ℕ)) →         (∀ (x8 : Fin x1), x5 x8 = Bool.true → x6 ↑x8 ≤ (1 : ℕ)) →           (∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate) (x11 x12 : ℕ), x2.gates[x9]? = Option.some x10 → x10.inputs = [x11, x12] → (x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 (x1 + x9) ≤ x6 x11 + x6 x12) ∧ (x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 (x1 + x9) ≤ Min.min (x6 x11) (x6 x12))) →             ∃ (x10 : ℕ → Bool),               (∀ (x11 : Fin x1), x10 ↑x11 = x5 x11) ∧                 (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate) (x13 x14 : ℕ),                     x2.gates[x11]? = Option.some x12 →                       x12.inputs = [x13, x14] →                         have x17 : List Bool := x2.wires (List.ofFn x4);                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x10 (x1 + x11) = (x17.getD x13 Bool.false && x10 x14 || x10 x13 && x17.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10 (x1 + x11) = (x10 x13 || x10 x14))) ∧                   ∀ (x11 : ℕ), x10 x11 = Bool.true → x6 x11 ≤ (1 : ℕ) := by
  exact PEqualNP.Outside.L_meta_11159.normalized
