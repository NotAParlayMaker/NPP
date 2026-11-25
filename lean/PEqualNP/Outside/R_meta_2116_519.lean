import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Remove the output gate. Its operands are internal wires, since the graph has
-- no singleton edge and every vertex is absent from some edge. For a binary
-- output, both operands compute proper factors by minimality. The two factors
-- must be available in the same list of at most fourteen gates.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2116_519
    (meet : let f := (fun x : Fin 9 → Bool => ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any
        fun mask => decide (∀ k : Fin 9, mask.testBit k.val = true → x k = true));
      ∀ (gs : List Gate) (a b : Fin gs.length), FanInTwo ⟨gs, 0⟩ → gs.length ≤ 14 →
      (∀ j : Fin gs.length, ∀ w ∈ (gs.get j).inputs, w < 9 + j.val) →
      (∀ v ∈ ([4,6,7] : List (Fin 9)), ∀ i j : Fin gs.length,
        v.val ∈ (gs.get i).inputs → v.val ∈ (gs.get j).inputs → i = j ∧ (gs.get i).op = .or) →
      let A := circuitFun 9 ⟨gs, 9 + a.val⟩
      let B := circuitFun 9 ⟨gs, 9 + b.val⟩
      A ≠ f → B ≠ f → (∀ x, (A x && B x) = f x) → False)
    (join : let f := (fun x : Fin 9 → Bool => ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any
        fun mask => decide (∀ k : Fin 9, mask.testBit k.val = true → x k = true));
      ∀ (gs : List Gate) (a b : Fin gs.length), FanInTwo ⟨gs, 0⟩ → gs.length ≤ 14 →
      (∀ j : Fin gs.length, ∀ w ∈ (gs.get j).inputs, w < 9 + j.val) →
      (∀ v ∈ ([4,6,7] : List (Fin 9)), ∀ i j : Fin gs.length,
        v.val ∈ (gs.get i).inputs → v.val ∈ (gs.get j).inputs → i = j ∧ (gs.get i).op = .or) →
      let A := circuitFun 9 ⟨gs, 9 + a.val⟩
      let B := circuitFun 9 ⟨gs, 9 + b.val⟩
      A ≠ f → B ≠ f → (∀ x, (A x || B x) = f x) → False)
    (neg : let f := (fun x : Fin 9 → Bool => ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any
        fun mask => decide (∀ k : Fin 9, mask.testBit k.val = true → x k = true));
      ∀ (gs : List Gate) (a : Fin gs.length), FanInTwo ⟨gs, 0⟩ → gs.length ≤ 14 →
      (∀ j : Fin gs.length, ∀ w ∈ (gs.get j).inputs, w < 9 + j.val) →
      (∀ v ∈ ([4,6,7] : List (Fin 9)), ∀ i j : Fin gs.length,
        v.val ∈ (gs.get i).inputs → v.val ∈ (gs.get j).inputs → i = j ∧ (gs.get i).op = .or) →
      (∀ x, (!(circuitFun 9 ⟨gs, 9 + a.val⟩ x)) = f x) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  dsimp only
  intro C model single
  obtain ⟨minimal, budget, computes, normal, _⟩ := model
  let f := fun x : Fin 9 → Bool => ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any
    fun mask => decide (∀ k : Fin 9, mask.testBit k.val = true → x k = true)
  have target : circuitFun 9 C = f := by rw [computes]; decide +kernel
  have present : C.gates ≠ [] := by
    intro nil
    have one := (single 4 (by simp)).1
    have size0 : C.size = 0 := by change C.gates.length = 0; simp [nil]
    obtain ⟨k, _⟩ := Finset.card_eq_one.mp one
    have := k.isLt
    omega
  obtain ⟨gs, g, shape⟩ := (List.eq_nil_or_concat' C.gates).resolve_left present
  have sizeEq : C.size = gs.length + 1 := by change C.gates.length = _; simp [shape]
  have before : gs.length ≤ 14 := by omega
  let last : Fin C.size := ⟨gs.length, by omega⟩
  have lastGet : C.gates.get last = g := by
    have ix : gs.length < C.gates.length := by simp [shape]
    change C.gates[gs.length] = g
    simp [shape]
  let emb (i : Fin gs.length) : Fin C.size := ⟨i.val, by omega⟩
  have prefixGet (i : Fin gs.length) : C.gates.get (emb i) = gs.get i := by
    have ix : i.val < C.gates.length := by rw [shape, List.length_append]; have := i.isLt; omega
    change C.gates[i.val] = gs[i.val]
    simp [shape, List.getElem_append_left, i.isLt]
  have proper : FanInTwo ⟨gs, 0⟩ := by
    intro a ha
    apply minimal.1 a
    rw [shape]
    exact List.mem_append_left _ ha
  have back (i : Fin gs.length) (w) (hw : w ∈ (gs.get i).inputs) : w < 9 + i.val := by
    have h := (normal (emb i)).1
    rw [prefixGet] at h
    exact h w hw
  have pins (v : Fin 9) (hv : v ∈ ([4,6,7] : List (Fin 9))) (i j : Fin gs.length)
      (hi : v.val ∈ (gs.get i).inputs) (hj : v.val ∈ (gs.get j).inputs) :
      i = j ∧ (gs.get i).op = .or := by
    let readers : Finset (Fin C.size) := Finset.univ.filter fun k => v.val ∈ (C.gates.get k).inputs
    obtain ⟨one, op⟩ := single v hv
    change readers.card = 1 at one
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp one
    have inI : emb i ∈ readers := by simpa [readers, prefixGet] using hi
    have inJ : emb j ∈ readers := by simpa [readers, prefixGet] using hj
    have ei : emb i = k := by simpa [hk] using inI
    have ej : emb j = k := by simpa [hk] using inJ
    have eq := ei.trans ej.symm
    exact ⟨Fin.ext (congrArg (fun j : Fin C.size => j.val) eq), by simpa [prefixGet] using op (emb i) inI⟩
  let step (w : List Bool) (a : Gate) := w ++ [a.op.eval (a.inputs.map fun k => w.getD k false)]
  let wires (x : Fin 9 → Bool) := gs.foldl step (List.ofFn x)
  let val (k : ℕ) (x : Fin 9 → Bool) := (wires x).getD k false
  have extend (t : List Gate) (w : List Bool) : ∃ tail : List Bool,
      t.foldl step w = w ++ tail ∧ tail.length = t.length := by
    induction t generalizing w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons a t ih =>
      obtain ⟨tail, eq, len⟩ := ih (step w a)
      refine ⟨a.op.eval (a.inputs.map fun k => w.getD k false) :: tail, ?_, by simp [len]⟩
      simpa [step, List.append_assoc] using eq
  have wlen (x : Fin 9 → Bool) : (wires x).length = 9 + gs.length := by
    obtain ⟨tail, eq, len⟩ := extend gs (List.ofFn x)
    change (gs.foldl step (List.ofFn x)).length = _
    rw [eq, List.length_append, List.length_ofFn, len]
  have raw (k : Fin 9) (x : Fin 9 → Bool) : val k.val x = x k := by
    obtain ⟨tail, eq, _⟩ := extend gs (List.ofFn x)
    change (gs.foldl step (List.ofFn x)).getD k.val false = x k
    rw [eq, List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using k.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, k.isLt, dite_true, Option.getD_some]
  have allWires (x : Fin 9 → Bool) : C.wires (List.ofFn x) =
      wires x ++ [g.op.eval (g.inputs.map fun k => val k x)] := by
    change C.gates.foldl step (List.ofFn x) = _
    rw [shape, List.foldl_append]
    rfl
  have shorter (k : ℕ) : val k ≠ f := by
    intro equal
    have fan : FanInTwo ⟨gs,k⟩ := proper
    have same : circuitFun 9 ⟨gs,k⟩ = circuitFun 9 C := by
      rw [target]
      exact equal
    have bound := minimal.2 ⟨gs,k⟩ fan same
    change C.size ≤ gs.length at bound
    omega
  have out : C.output = 9 + gs.length := by
    by_contra different
    apply shorter C.output
    rw [← target]
    funext x
    change (wires x).getD C.output false = (C.wires (List.ofFn x)).getD C.output false
    rw [allWires]
    rcases lt_or_gt_of_ne different with h | h
    · symm
      exact List.getD_append _ _ _ _ (by rw [wlen]; exact h)
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (wires x).length ≤ C.output by rw [wlen]; omega),
        List.getElem?_eq_none (show (wires x ++ [_]).length ≤ C.output by simp [wlen]; omega)]
  have output (x : Fin 9 → Bool) : g.op.eval (g.inputs.map fun k => val k x) = f x := by
    have eq := congrFun target x
    change (C.wires (List.ofFn x)).getD C.output false = f x at eq
    rw [out, allWires, ← wlen x] at eq
    simpa using eq
  have well := normal last
  change (∀ w ∈ (C.gates.get last).inputs, w < 9 + gs.length) ∧ _ at well
  rw [lastGet] at well
  have ops := (minimal.1 g (by simp [shape])).1
  change g.op = .and ∨ g.op = .or ∨ g.op = .not at ops
  have hasOne : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, x i = true ∧ f x = false := by decide +kernel
  have hasZero : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, x i = false ∧ f x = true := by decide +kernel
  have zero : f (fun _ => false) = false := by decide +kernel
  have binary (isMeet : Bool) (a b : ℕ) (ha : a < 9 + gs.length) (hb : b < 9 + gs.length)
      (eq : ∀ x, (if isMeet then val a x && val b x else val a x || val b x) = f x) : False := by
    have internal (k l : ℕ)
        (e : ∀ x, (if isMeet then val k x && val l x else val k x || val l x) = f x) : 9 ≤ k := by
      by_contra! h
      let i : Fin 9 := ⟨k,h⟩
      cases isMeet with
      | false =>
        obtain ⟨x, on, off⟩ := hasOne i
        have bit : val k x = true := (raw i x).trans on
        simpa [bit, off] using e x
      | true =>
        obtain ⟨x, off, on⟩ := hasZero i
        have bit : val k x = false := (raw i x).trans off
        simpa [bit, on] using e x
    have ia := internal a b eq
    have ib := internal b a (by simpa only [Bool.and_comm, Bool.or_comm] using eq)
    let p : Fin gs.length := ⟨a-9,by omega⟩
    let q : Fin gs.length := ⟨b-9,by omega⟩
    have ap : 9 + p.val = a := by dsimp [p]; omega
    have bq : 9 + q.val = b := by dsimp [q]; omega
    cases isMeet with
    | false =>
      apply join gs p q proper before back pins
      · change val (9 + p.val) ≠ f
        rw [ap]
        exact shorter a
      · change val (9 + q.val) ≠ f
        rw [bq]
        exact shorter b
      · change ∀ x, (val (9 + p.val) x || val (9 + q.val) x) = f x
        rw [ap, bq]
        exact eq
    | true =>
      apply meet gs p q proper before back pins
      · change val (9 + p.val) ≠ f
        rw [ap]
        exact shorter a
      · change val (9 + q.val) ≠ f
        rw [bq]
        exact shorter b
      · change ∀ x, (val (9 + p.val) x && val (9 + q.val) x) = f x
        rw [ap, bq]
        exact eq
  have andEq (x y : Bool) : GateOp.and.eval [x,y] = (x && y) := by cases x <;> cases y <;> rfl
  have orEq (x y : Bool) : GateOp.or.eval [x,y] = (x || y) := by cases x <;> cases y <;> rfl
  have notEq (x : Bool) : GateOp.not.eval [x] = !x := rfl
  rcases ops with op | op | op
  · have len : g.inputs.length = 2 := well.2.2.resolve_left (by simp [op]) |>.2
    obtain ⟨a,b,ab⟩ := List.length_eq_two.mp len
    apply binary true a b (well.1 a (by simp [ab])) (well.1 b (by simp [ab]))
    intro x
    simpa [op, ab, andEq, orEq, notEq] using output x
  · have len : g.inputs.length = 2 := well.2.2.resolve_left (by simp [op]) |>.2
    obtain ⟨a,b,ab⟩ := List.length_eq_two.mp len
    apply binary false a b (well.1 a (by simp [ab])) (well.1 b (by simp [ab]))
    intro x
    simpa [op, ab, andEq, orEq, notEq] using output x
  · have len : g.inputs.length = 1 := well.2.2.resolve_right (by simp [op]) |>.2
    obtain ⟨a,ab⟩ := List.length_eq_one_iff.mp len
    have comp (x : Fin 9 → Bool) : (!(val a x)) = f x := by
      simpa [op, ab, andEq, orEq, notEq] using output x
    have internal : 9 ≤ a := by
      by_contra! h
      let i : Fin 9 := ⟨a,h⟩
      have bit : val a (fun _ => false) = false := raw i _
      simpa [bit, zero] using comp (fun _ => false)
    have upper := well.1 a (by simp [ab])
    let p : Fin gs.length := ⟨a-9,by omega⟩
    have ap : 9 + p.val = a := by dsimp [p]; omega
    apply neg gs p proper before back pins
    change ∀ x, (!(val (9 + p.val) x)) = f x
    rw [ap]
    exact comp
