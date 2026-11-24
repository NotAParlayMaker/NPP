import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

namespace PEqualNP.Outside.L_meta_2826

def source (gs : List Gate) (x : List Bool) := (Circuit.mk gs 0).wires x

def target (bs : List BinaryGate) (x : List Bool) := (BinaryCircuit.mk bs 0).wires (x ++ [false])

-- The pair names a target wire and records whether to complement it.
def value (w : List Bool) (r : ℕ × Bool) := w.getD r.1 false != r.2

def produced (gs : List Gate) (g : Gate) (x : List Bool) :=
  g.op.eval (g.inputs.map fun i => (source gs x).getD i false)

lemma source_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    source (gs ++ [g]) x = source gs x ++ [produced gs g x] := by
  simp [source, produced, Circuit.wires, List.foldl_append]

lemma target_snoc (bs : List BinaryGate) (g : BinaryGate) (x : List Bool) :
    target (bs ++ [g]) x = target bs x ++
      [g.op ((target bs x).getD g.left false) ((target bs x).getD g.right false)] := by
  simp [target, BinaryCircuit.wires, List.foldl_append]

lemma source_len (gs : List Gate) (x : List Bool) :
    (source gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [source, Circuit.wires]
  | append_singleton gs g ih => simp [source_snoc, ih, Nat.add_assoc]

lemma target_len (bs : List BinaryGate) (x : List Bool) :
    (target bs x).length = x.length + 1 + bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp [target, BinaryCircuit.wires]
  | append_singleton bs g ih => simp [target_snoc, ih, Nat.add_assoc]

lemma at_end (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma other_index (w : List Bool) (v : Bool) {i : ℕ} (hne : i ≠ w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  by_cases h : i < w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma zero_wire (bs : List BinaryGate) (x : List Bool) (hx : x.length = 10) :
    (target bs x).getD 10 false = false := by
  induction bs using List.reverseRecOn with
  | nil => change (x ++ [false]).getD 10 false = false; rw [← hx, at_end]
  | append_singleton bs g ih =>
    rw [target_snoc, List.getD_append _ _ _ _ (by rw [target_len, hx]; omega), ih]

def shape (bs : List BinaryGate) := ∀ g ∈ bs, ∃ a b : Bool,
  g.op = fun x y => (x == a) && (y == b)

def ready (gs : List Gate) := ∃ (bs : List BinaryGate) (wire : ℕ → ℕ × Bool),
  shape bs ∧ bs.length + notCount ⟨gs, 0⟩ ≤ gs.length ∧
  (∀ i, (wire i).1 < 11 + bs.length) ∧
  ∀ x : List Bool, x.length = 10 → ∀ i, value (target bs x) (wire i) = (source gs x).getD i false

def op (t : Bool) : GateOp := if t then .or else .and

def combine (t a b : Bool) := if t then a || b else a && b

-- For OR the gate detects two false inputs and its output is complemented.
def joint (t : Bool) (a b : ℕ × Bool) : BinaryGate :=
  ⟨fun x y => (x == (a.2 == t)) && (y == (b.2 == t)), a.1, b.1⟩

lemma joint_val (t : Bool) (a b : ℕ × Bool) (w : List Bool) :
    ((joint t a b).op (w.getD a.1 false) (w.getD b.1 false) != t) =
    combine t (value w a) (value w b) := by
  unfold joint combine value
  cases a.2 <;> cases b.2 <;> cases t <;> cases w.getD a.1 false <;> cases w.getD b.1 false <;> rfl

-- Pad a missing operand with the identity of the source operation.
-- Wire ten is the extra false input, so either Boolean constant is available.
def operand (t : Bool) (wire : ℕ → ℕ × Bool) (ins : List ℕ) (j : ℕ) :=
  (ins.map wire).getD j (10, !t)

lemma operands (t : Bool) (wire : ℕ → ℕ × Bool) (ins : List ℕ) (hlen : ins.length ≤ 2)
    (w v : List Bool) (hz : w.getD 10 false = false)
    (hw : ∀ i, value w (wire i) = v.getD i false) :
    combine t (value w (operand t wire ins 0)) (value w (operand t wire ins 1)) =
      (op t).eval (ins.map fun i => v.getD i false) := by
  have hd (b : Bool) : value w (10, b) = b := by
    change (w.getD 10 false != b) = b
    rw [hz]
    cases b <;> rfl
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩
  · cases t <;> simp [op, operand, combine, GateOp.eval, hd]
  · cases t <;> simp [op, operand, combine, GateOp.eval, hd, hw]
  · cases t <;> simp [op, operand, combine, GateOp.eval, hw]
  · simp at hlen

lemma compile (gs : List Gate) (fan : FanInTwo ⟨gs, 0⟩) : ready gs := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], (fun i => (min i 10, false)), by simp [shape], by simp [notCount], ?_, ?_⟩
    · intro i; simp
    · intro x hx i
      change ((x ++ [false]).getD (min i 10) false != false) = x.getD i false
      by_cases h : i < 10
      · rw [Nat.min_eq_left (by omega), List.getD_append _ _ _ _ (by omega)]
        simp
      · rw [Nat.min_eq_right (by omega), ← hx, at_end, List.getD_eq_default _ _ (by omega)]
        rfl
  | append_singleton gs g ih =>
    obtain ⟨bs, wire, shapeB, costB, bound, corr⟩ := ih (fun a ha => fan a (by simp [ha]))
    have hg := fan g (by simp)
    have finish (cs : List BinaryGate) (r : ℕ × Bool) (sh : shape cs)
        (cost : cs.length + notCount ⟨gs ++ [g], 0⟩ ≤ (gs ++ [g]).length)
        (le : bs.length ≤ cs.length) (hr : r.1 < 11 + cs.length)
        (keep : ∀ x : List Bool, x.length = 10 → ∀ i,
          value (target cs x) (wire i) = value (target bs x) (wire i))
        (new : ∀ x : List Bool, x.length = 10 → value (target cs x) r = produced gs g x) :
        ready (gs ++ [g]) := by
      refine ⟨cs, (fun i => if i = 10 + gs.length then r else wire i), sh, cost, ?_, ?_⟩
      · intro i
        dsimp only
        split
        · exact hr
        · have := bound i; omega
      · intro x hx i
        rw [source_snoc]
        have hlen : (source gs x).length = 10 + gs.length := by rw [source_len, hx]
        dsimp only
        split
        · rename_i h
          rw [h, ← hlen, at_end, new x hx]
        · rename_i h
          rw [other_index _ _ (by rwa [hlen]), keep x hx i, corr x hx i]
    have binary (t : Bool) (hop : g.op = op t) : ready (gs ++ [g]) := by
      let a := operand t wire g.inputs 0
      let b := operand t wire g.inputs 1
      let z := joint t a b
      apply finish (bs ++ [z]) (11 + bs.length, t)
      · intro q hq
        rcases List.mem_append.mp hq with h | h
        · exact shapeB q h
        · have eq : q = z := by simpa using h
          exact ⟨a.2 == t, b.2 == t, eq ▸ rfl⟩
      · have hne : g.op ≠ GateOp.not := by rw [hop]; cases t <;> intro h <;> cases h
        simp [notCount, List.filter_append, hne] at costB ⊢
        omega
      · simp
      · simp
      · intro x hx i
        unfold value
        rw [target_snoc, List.getD_append _ _ _ _ (by rw [target_len, hx]; exact bound i)]
      · intro x hx
        have len : (target bs x).length = 11 + bs.length := by rw [target_len, hx]
        change ((target (bs ++ [z]) x).getD (11 + bs.length) false != t) = _
        rw [target_snoc, ← len, at_end]
        change ((joint t a b).op ((target bs x).getD a.1 false) ((target bs x).getD b.1 false) != t) = _
        rw [joint_val t a b (target bs x)]
        unfold produced
        rw [hop]
        exact operands t wire g.inputs hg.2 _ _ (zero_wire bs x hx) (corr x hx)
    rcases hg.1 with ha | ho | hn
    · exact binary false ha
    · exact binary true ho
    · change g.op = GateOp.not at hn
      let r := (g.inputs.map wire).headD (10, false)
      apply finish bs (r.1, !r.2) shapeB
      · simp [notCount, List.filter_append, hn] at costB ⊢
        omega
      · exact Nat.le_refl _
      · cases h : g.inputs with
        | nil => simp [r, h]; omega
        | cons i is => simpa [r, h] using bound i
      · intro x hx i; rfl
      · intro x hx
        have neg (s : ℕ × Bool) :
            value (target bs x) (s.1, !s.2) = !value (target bs x) s := by
          unfold value
          cases s.2 <;> cases (target bs x).getD s.1 false <;> rfl
        rw [neg]
        cases h : g.inputs with
        | nil =>
          simp only [r, h, List.map_nil, List.headD_nil, produced, hn, GateOp.eval, value]
          rw [zero_wire bs x hx]
          rfl
        | cons i is => simp [r, h, corr x hx, produced, hn, GateOp.eval]

end PEqualNP.Outside.L_meta_2826

theorem PEqualNP.Outside.L_meta_2826 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → ∃ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Bool), (∀ x5 ∈ x3.gates, ∃ (x7 : Bool) (x8 : Bool), x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) ∧ x3.size + PEqualNP.NotBracket.notCount x1 ≤ x1.size ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → (x3.eval (x5 ++ [Bool.false]) != x4) = x1.eval x5 := by
  rintro ⟨gs, o⟩ fan
  obtain ⟨bs, wire, sh, cost, bound, sim⟩ := PEqualNP.Outside.L_meta_2826.compile gs fan
  exact ⟨⟨bs, (wire o).1⟩, (wire o).2, sh, cost, fun x hx => sim x hx o⟩
