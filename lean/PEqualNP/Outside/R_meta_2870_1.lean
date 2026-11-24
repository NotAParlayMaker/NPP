import Mathlib
import PEqualNP.Defs
-- The bounded-order hypothesis is the statement of L_meta_2862.lean, Bastian Milan, PR 5259.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 900000 in
theorem PEqualNP.Outside.R_meta_2870_1
    (boundedOrder : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x1 < (200 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size)
    (rectangleBound : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      200 ≤ q → n = q^2 + q + 1 →
      (∀ l, Fintype.card {p : Fin n // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (A : ℕ → Fin n → Fin n → Prop) (B : ℕ → Finset (Fin n) → Prop), o < n+n+s →
      (∀ (x p l : Fin n), A x.val p l → p = x) →
      (∀ (x : Fin n) Y, B x.val Y → ∃ l ∈ Y, I x l) →
      (∀ (y p l : Fin n), A (n+y.val) p l → l = y) →
      (∀ (y : Fin n) Y, B (n+y.val) Y → y ∉ Y) →
      (∀ j < s, ∃ a < n+n+j, ∃ b < n+n+j, ∀ p l Y,
        A (n+n+j) p l ∧ B (n+n+j) Y → (A a p l ∧ B a Y) ∨ (A b p l ∧ B b Y)) →
      (∀ p l, I p l → A o p l) → (∀ Y : Finset (Fin n), Y.card ≤ q → B o Y) → n*q ≤ 100*s) :
      have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (1 : ℕ) ≤ x16.card → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  intro _ q n I inst C hq hn degrees joins mono output reads pos neg marked sub nonempty exactMarked few
  by_cases hsmall : q < 200
  · exact boundedOrder q n I C hq hsmall hn degrees joins mono pos neg
  classical
  let yes (p l : Fin n) (i : Fin (n+n)) := decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)
  let no (Y : Finset (Fin n)) : Fin (n+n) → Bool := Fin.append
    (fun p => decide (¬ ∃ l ∈ Y, I p l)) (fun l => decide (l ∈ Y))
  let step (v : List Bool) (g : Gate) := v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]
  let run (gs : List Gate) (v : List Bool) := gs.foldl step v
  let val (w : ℕ) (x : Fin (n+n) → Bool) := (run C.gates (List.ofFn x)).getD w false
  let A (w : ℕ) (p l : Fin n) := val w (yes p l) = true
  let B (w : ℕ) (Y : Finset (Fin n)) := val w (no Y) = false
  have preserve (gs : List Gate) (v : List Bool) (i : ℕ) (hi : i < v.length) :
      (run gs v).getD i false = v.getD i false := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step v g)).getD i false = _
      rw [ih (step v g) (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have lengthRun (gs : List Gate) (v : List Bool) : (run gs v).length = v.length + gs.length := by
    induction gs generalizing v with
    | nil => simp only [run, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih =>
      change (run gs (step v g)).length = _
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
  have input (x : Fin (n+n) → Bool) (i : Fin (n+n)) : val i.val x = x i := by
    change (run C.gates (List.ofFn x)).getD i.val false = _
    rw [preserve C.gates _ i.val (by simpa only [List.length_ofFn] using i.isLt)]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  have gate (j : ℕ) (hj : j < C.size) (a b : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
      (pins : g.inputs = [a,b]) (ha : a < n+n+j) (hb : b < n+n+j) (x : Fin (n+n) → Bool) :
      val (n+n+j) x = g.op.eval [val a x, val b x] := by
    have hj' : j < C.gates.length := hj
    have head : C.gates[j] = g := by simpa only [List.getElem?_eq_getElem hj', Option.some.injEq] using hg
    let v := run (C.gates.take j) (List.ofFn x)
    have len : v.length = n+n+j := by simp only [v, lengthRun, List.length_ofFn, List.length_take, Nat.min_eq_left hj'.le]
    have splitG : C.gates = (C.gates.take j ++ [g]) ++ C.gates.drop (j+1) := by
      rw [← head, ← List.take_succ_eq_append_getElem hj', List.take_append_drop]
    have allVal (w : ℕ) : val w x = (run (C.gates.drop (j+1)) (step v g)).getD w false := by
      change (C.gates.foldl step (List.ofFn x)).getD w false = _
      conv_lhs => rw [splitG, List.foldl_append, List.foldl_append]
      rfl
    have before (w : ℕ) (hw : w < n+n+j) : val w x = v.getD w false := by
      rw [allVal, preserve _ _ _ (by simp only [step, List.length_append, List.length_cons, List.length_nil, len]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (len.symm ▸ hw)]
    rw [before a ha, before b hb, allVal, preserve _ _ _ (by simp only [step, List.length_append, List.length_cons, List.length_nil, len]; omega)]
    rw [← len]
    simp [step, pins, List.getD_eq_getElem?_getD]
  have sep (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro eq
    have v := congrArg Fin.val eq
    change p.val = n + l.val at v
    have h := p.isLt
    omega
  apply rectangleBound q n I (by omega) hn degrees joins C.size C.output A B output
  · intro p x l he
    change val (Fin.castAdd n p).val (yes x l) = true at he
    rw [input] at he
    have test := of_decide_eq_true he
    exact (Fin.castAdd_inj.mp (test.resolve_right (sep p l))).symm
  · intro p Y hY
    change val (Fin.castAdd n p).val (no Y) = false at hY
    rw [input] at hY
    change Fin.append _ _ (Fin.castAdd n p) = false at hY
    rw [Fin.append_left] at hY
    by_contra h
    exact Bool.noConfusion ((decide_eq_true h).symm.trans hY)
  · intro l p y he
    change val (Fin.natAdd n l).val (yes p y) = true at he
    rw [input] at he
    have test := of_decide_eq_true he
    have eq := test.resolve_left (Ne.symm (sep p l))
    apply Fin.ext
    have := congrArg Fin.val eq
    change n+l.val = n+y.val at this
    omega
  · intro l Y hY
    change val (Fin.natAdd n l).val (no Y) = false at hY
    rw [input] at hY
    change Fin.append _ _ (Fin.natAdd n l) = false at hY
    rw [Fin.append_right] at hY
    exact of_decide_eq_false hY
  · intro j hj
    have hj' : j < C.gates.length := hj
    let g := C.gates[j]
    have get : C.gates[j]? = some g := List.getElem?_eq_getElem hj'
    obtain ⟨a,b,pins,hab,hb⟩ := reads j g get
    have ha := hab.trans hb
    refine ⟨a, ha, b, hb, ?_⟩
    intro p l Y hz
    change val (n+n+j) (yes p l) = true ∧ val (n+n+j) (no Y) = false at hz
    change (val a (yes p l) = true ∧ val a (no Y) = false) ∨
      (val b (yes p l) = true ∧ val b (no Y) = false)
    rw [gate j hj a b g get pins ha hb, gate j hj a b g get pins ha hb] at hz
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := (mono g (List.getElem_mem hj')).1
    rcases hop with op | op <;> rw [op] at hz
    · have h (x y : Bool) : GateOp.and.eval [x, y] = (x && y) := by
        cases x <;> cases y <;> rfl
      simp only [h] at hz
      cases ea : val a (no Y) <;> simp [ea] at hz ⊢ <;> tauto
    · have h (x y : Bool) : GateOp.or.eval [x, y] = (x || y) := by
        cases x <;> cases y <;> rfl
      simp only [h] at hz
      cases ea : val a (yes p l) <;> simp [ea] at hz ⊢ <;> tauto
  · exact pos
  · intro Y budget
    apply neg (no Y)
    · have count : Fintype.card {l : Fin n // no Y (Fin.natAdd n l) = true} = Y.card := by
        rw [← Fintype.card_coe]
        apply Fintype.card_congr
        apply Equiv.subtypeEquivRight
        intro l
        change (Fin.append _ _ (Fin.natAdd n l) = true) ↔ l ∈ Y
        rw [Fin.append_right, decide_eq_true_eq]
      exact count.trans_le budget
    · rintro ⟨p,l,inc,hp,hl⟩
      change Fin.append _ _ (Fin.castAdd n p) = true at hp
      change Fin.append _ _ (Fin.natAdd n l) = true at hl
      rw [Fin.append_left] at hp
      rw [Fin.append_right] at hl
      exact (of_decide_eq_true hp) ⟨l,of_decide_eq_true hl,inc⟩
