import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3835

/-- Reading a wire at or past the end of the list gives `false`. Stated in the
`getElem?` form, which is the normal form `simp` rewrites `List.getD` into. -/
theorem getElem?_false_of_le (x : List Bool) (a : ℕ) (h : x.length ≤ a) :
    (x[a]?).getD false = false := by
  simp [List.getElem?_eq_none_iff.mpr h]

/-- Peeling the first gate off a circuit: evaluating `⟨g :: gs, o⟩` on `x` is the
same as evaluating `⟨gs, o⟩` on `x` with the first gate's value appended. The
wire numbering aligns because the peeled circuit has one fewer gate and one
more input. -/
theorem eval_cons (g : Gate) (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨g :: gs, o⟩ x =
      Circuit.eval ⟨gs, o⟩ (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

/-- The value of one fan-in-two gate on an input list of length `n`. Either it is
a (possibly negated) literal read at one of the positions `0, ..., n` — position
`n` reads `false`, which also gives the two constants — or it is an AND/OR of
two distinct inputs. Dead wires (indices `≥ n`) read `false` and are absorbed
by the cases. -/
theorem gate_value (n : ℕ) (op : GateOp) (inputs : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : inputs.length ≤ 2) :
    (∃ (i : Fin (n + 1)) (b : Bool), ∀ x : List Bool, x.length = n →
        op.eval (inputs.map fun i => x.getD i false) = (b != x.getD (↑i) false)) ∨
    (∃ (i j : Fin n) (b : Bool), i < j ∧ ∀ x : List Bool, x.length = n →
        op.eval (inputs.map fun i => x.getD i false)
          = if b = true then x.getD (↑i) false || x.getD (↑j) false
            else x.getD (↑i) false && x.getD (↑j) false) := by
  have hop' : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by
    simpa using hop
  rcases hop' with rfl | rfl | rfl
  · -- op = and
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, inputs⟩⟩⟩
    · -- inputs = []: the value is `true`
      refine Or.inl ⟨⟨n, by omega⟩, true, fun x hx => ?_⟩
      simp [GateOp.eval, getElem?_false_of_le x n (by omega)]
    · -- inputs = [a]: the value is `x.getD a false`
      by_cases ha : a < n
      · refine Or.inl ⟨⟨a, by omega⟩, false, fun x hx => ?_⟩
        simp [GateOp.eval]
      · refine Or.inl ⟨⟨n, by omega⟩, false, fun x hx => ?_⟩
        simp [GateOp.eval, getElem?_false_of_le x a (by omega),
          getElem?_false_of_le x n (by omega)]
    · -- inputs = [a, b]: the value is `x.getD a false && x.getD b false`
      by_cases ha : a < n <;> by_cases hb : b < n
      · rcases lt_trichotomy a b with h | h | h
        · refine Or.inr ⟨⟨a, ha⟩, ⟨b, hb⟩, false, by exact h, fun x hx => ?_⟩
          simp [GateOp.eval]
        · refine Or.inl ⟨⟨a, by omega⟩, false, fun x hx => ?_⟩
          simp [GateOp.eval, h]
        · refine Or.inr ⟨⟨b, hb⟩, ⟨a, ha⟩, false, by exact h, fun x hx => ?_⟩
          simp [GateOp.eval, Bool.and_comm]
      · refine Or.inl ⟨⟨n, by omega⟩, false, fun x hx => ?_⟩
        simp [GateOp.eval, getElem?_false_of_le x b (by omega),
          getElem?_false_of_le x n (by omega)]
      · refine Or.inl ⟨⟨n, by omega⟩, false, fun x hx => ?_⟩
        simp [GateOp.eval, getElem?_false_of_le x a (by omega),
          getElem?_false_of_le x n (by omega)]
      · refine Or.inl ⟨⟨n, by omega⟩, false, fun x hx => ?_⟩
        simp [GateOp.eval, getElem?_false_of_le x a (by omega),
          getElem?_false_of_le x b (by omega), getElem?_false_of_le x n (by omega)]
    · -- inputs has at least three entries, contradicting `hlen`
      simp only [List.length_cons] at hlen
      omega
  · -- op = or
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, inputs⟩⟩⟩
    · -- inputs = []: the value is `false`
      refine Or.inl ⟨⟨n, by omega⟩, false, fun x hx => ?_⟩
      simp [GateOp.eval, getElem?_false_of_le x n (by omega)]
    · -- inputs = [a]: the value is `x.getD a false`
      by_cases ha : a < n
      · refine Or.inl ⟨⟨a, by omega⟩, false, fun x hx => ?_⟩
        simp [GateOp.eval]
      · refine Or.inl ⟨⟨n, by omega⟩, false, fun x hx => ?_⟩
        simp [GateOp.eval, getElem?_false_of_le x a (by omega),
          getElem?_false_of_le x n (by omega)]
    · -- inputs = [a, b]: the value is `x.getD a false || x.getD b false`
      by_cases ha : a < n <;> by_cases hb : b < n
      · rcases lt_trichotomy a b with h | h | h
        · refine Or.inr ⟨⟨a, ha⟩, ⟨b, hb⟩, true, by exact h, fun x hx => ?_⟩
          simp [GateOp.eval]
        · refine Or.inl ⟨⟨a, by omega⟩, false, fun x hx => ?_⟩
          simp [GateOp.eval, h]
        · refine Or.inr ⟨⟨b, hb⟩, ⟨a, ha⟩, true, by exact h, fun x hx => ?_⟩
          simp [GateOp.eval, Bool.or_comm]
      · -- b is dead: the value is `x.getD a false`
        refine Or.inl ⟨⟨a, by omega⟩, false, fun x hx => ?_⟩
        simp [GateOp.eval, getElem?_false_of_le x b (by omega)]
      · -- a is dead: the value is `x.getD b false`
        refine Or.inl ⟨⟨b, by omega⟩, false, fun x hx => ?_⟩
        simp [GateOp.eval, getElem?_false_of_le x a (by omega)]
      · refine Or.inl ⟨⟨n, by omega⟩, false, fun x hx => ?_⟩
        simp [GateOp.eval, getElem?_false_of_le x a (by omega),
          getElem?_false_of_le x b (by omega), getElem?_false_of_le x n (by omega)]
    · -- inputs has at least three entries, contradicting `hlen`
      simp only [List.length_cons] at hlen
      omega
  · -- op = not: only the first input matters
    rcases inputs with _ | ⟨a, inputs⟩
    · -- inputs = []: the value is `!false = true`
      refine Or.inl ⟨⟨n, by omega⟩, true, fun x hx => ?_⟩
      simp [GateOp.eval, getElem?_false_of_le x n (by omega)]
    · -- the value is `!(x.getD a false)`
      by_cases ha : a < n
      · refine Or.inl ⟨⟨a, by omega⟩, true, fun x hx => ?_⟩
        simp [GateOp.eval]
      · refine Or.inl ⟨⟨n, by omega⟩, true, fun x hx => ?_⟩
        simp [GateOp.eval, getElem?_false_of_le x a (by omega),
          getElem?_false_of_le x n (by omega)]

end PEqualNP.Outside.L_meta_3835

theorem PEqualNP.Outside.L_meta_3835 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x2 → (0 : ℕ) < x2.size →
      ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size + (1 : ℕ) = x2.size ∧
        ((∃ (x6 : Fin (x1 + (1 : ℕ))) (x7 : Bool),
            ∀ (x8 : List Bool), x8.length = x1 →
              x2.eval x8 = x5.eval (x8 ++ [x7 != x8.getD (↑x6) Bool.false])) ∨
          ∃ (x6 : Fin x1) (x7 : Fin x1) (x8 : Bool), x6 < x7 ∧
            ∀ (x9 : List Bool), x9.length = x1 →
              x2.eval x9 = x5.eval (x9 ++ [if x8 = Bool.true then
                x9.getD (↑x6) Bool.false || x9.getD (↑x7) Bool.false
              else
                x9.getD (↑x6) Bool.false && x9.getD (↑x7) Bool.false])) := by
  intro n C hfan hsize
  rcases C with ⟨_ | ⟨g, gs⟩, o⟩
  · simp [Circuit.size] at hsize
  · obtain ⟨hop, hlen⟩ := hfan g List.mem_cons_self
    have hfan' : FanInTwo ⟨gs, o⟩ := by
      intro g' hg'
      exact hfan g' (List.mem_cons_of_mem g hg')
    rcases PEqualNP.Outside.L_meta_3835.gate_value n g.op g.inputs hop hlen with
      ⟨i, b, hi⟩ | ⟨i, j, b, hij, hj⟩
    · refine ⟨⟨gs, o⟩, hfan', by simp [Circuit.size], Or.inl ⟨i, b, fun x hx => ?_⟩⟩
      rw [PEqualNP.Outside.L_meta_3835.eval_cons]
      exact congrArg (fun v => Circuit.eval ⟨gs, o⟩ (x ++ [v])) (hi x hx)
    · refine ⟨⟨gs, o⟩, hfan', by simp [Circuit.size], Or.inr ⟨i, j, b, hij, fun x hx => ?_⟩⟩
      rw [PEqualNP.Outside.L_meta_3835.eval_cons]
      exact congrArg (fun v => Circuit.eval ⟨gs, o⟩ (x ++ [v])) (hj x hx)
