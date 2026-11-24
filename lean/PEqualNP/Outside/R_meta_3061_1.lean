import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Zero effective readers cannot change the output under selector replacement.
-- Four or more effective readers already give the desired gate count.
-- A constant selector can be removed, and L_meta_2036 rules out the smaller low-cofactor circuit.
theorem PEqualNP.Outside.R_meta_3061_1
  (removeConstant :
    ∀ (n : ℕ) (A B : Circuit) (f : (Fin n → Bool) → Bool) (c : Bool),
      FanInTwo A → FanInTwo B → A.output + 1 = n + A.size → A.gates ≠ [] →
      (∃ x y, f x ≠ f y) →
      (∀ x, circuitFun n A x = c) →
      (∀ x, B.eval (A.wires (List.ofFn x) ++ [circuitFun n A x]) = f x) →
      HasCircuitSize n f (A.size + B.size - 1))
  (edgeLower :
    let f : (Fin 8 → Bool) → Bool := fun x =>
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
      x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
      x 5 && x 7 || x 7 && x 4
    ¬ HasCircuitSize 8 f 12)
  (one :
    let f : (Fin 8 → Bool) → Bool := fun x =>
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
      x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
      x 5 && x 7 || x 7 && x 4
    let h : (Fin 8 → Bool) → Bool := fun x => f x || x 0 || x 3
    ∀ (A B : Circuit) (k : Bool), FanInTwo A → FanInTwo B → A.output + 1 = 8 + A.size →
      let readers := B.gates.countP (fun g =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).contains (8 + A.size))
      readers = 1 →
      (¬ ∃ c : Bool, ∀ x, circuitFun 8 A x = c) →
      (∀ i : Fin 8, (circuitFun 8 A ≠ fun x => x i) ∧
        (circuitFun 8 A ≠ fun x => !x i)) →
      (∀ x, f x ≠ h x → circuitFun 8 A x = !k) →
      (∀ x, B.eval (A.wires (List.ofFn x) ++ [circuitFun 8 A x]) = f x) →
      (∀ x, B.eval (A.wires (List.ofFn x) ++ [k]) = h x) →
      14 ≤ A.size + B.size)
  (many :
    let f : (Fin 8 → Bool) → Bool := fun x =>
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
      x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
      x 5 && x 7 || x 7 && x 4
    let h : (Fin 8 → Bool) → Bool := fun x => f x || x 0 || x 3
    ∀ (A B : Circuit) (k : Bool), FanInTwo A → FanInTwo B → A.output + 1 = 8 + A.size →
      let readers := B.gates.countP (fun g =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).contains (8 + A.size))
      (readers = 2 ∨ readers = 3) →
      (¬ ∃ c : Bool, ∀ x, circuitFun 8 A x = c) →
      (∀ i : Fin 8, (circuitFun 8 A ≠ fun x => x i) ∧
        (circuitFun 8 A ≠ fun x => !x i)) →
      (∀ x, f x ≠ h x → circuitFun 8 A x = !k) →
      (∀ x, B.eval (A.wires (List.ofFn x) ++ [circuitFun 8 A x]) = f x) →
      (∀ x, B.eval (A.wires (List.ofFn x) ++ [k]) = h x) →
      14 ≤ A.size + B.size) :
  have f : (Fin 8 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
    x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
    x 5 && x 7 || x 7 && x 4;
  have h : (Fin 8 → Bool) → Bool := fun x => f x || x 0 || x 3;
  ∀ (A B : Circuit) (k : Bool), FanInTwo A → FanInTwo B → A.output + 1 = 8 + A.size →
    10 + B.gates.countP (fun g =>
      (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).contains (8 + A.size))
      ≤ A.size + B.size →
    (∀ i : Fin 8, (circuitFun 8 A ≠ fun x => x i) ∧ (circuitFun 8 A ≠ fun x => !x i)) →
    (∀ x, f x ≠ h x → circuitFun 8 A x = !k) →
    (∀ x, B.eval (A.wires (List.ofFn x) ++ [circuitFun 8 A x]) = f x) →
    (∀ x, B.eval (A.wires (List.ofFn x) ++ [k]) = h x) →
    14 ≤ A.size + B.size := by
  intro f h A B k fanA fanB last budget notLiteral toggles lo hi
  let reserved := 8 + A.size
  let reads (g : Gate) : List ℕ :=
    if g.op.eval [false, false] then g.inputs.take 1 else g.inputs
  let uses (g : Gate) := (reads g).contains reserved
  let tally := B.gates.countP uses
  change 10 + tally ≤ A.size + B.size at budget
  by_cases large : 4 ≤ tally
  · omega
  have nonzero : tally ≠ 0 := by
    intro zero
    have avoids (g) (mem : g ∈ B.gates) : reserved ∉ reads g := by
      have absent := List.countP_eq_zero.mp zero g mem
      simpa [uses, List.contains_iff_mem] using absent
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let run (gs : List Gate) (w : List Bool) := gs.foldl step w
    have lengthRun (gs : List Gate) (w : List Bool) :
        (run gs w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp [run]
      | cons g gs ih =>
        change (run gs (step w g)).length = _
        rw [ih]
        simp [step]
        omega
    have keep (gs : List Gate) (w : List Bool) (i : ℕ) (within : i < w.length) :
        (run gs w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change (run gs (step w g)).getD i false = _
        rw [ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ within
    have simplify (g : Gate) (mem : g ∈ B.gates) (value : ℕ → Bool) :
        g.op.eval (g.inputs.map value) = g.op.eval ((reads g).map value) := by
      have op := (fanB g mem).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
      rcases op with hop | hop | hop
      · unfold reads
        rw [hop]
        rfl
      · unfold reads
        rw [hop]
        rfl
      · unfold reads
        rw [hop]
        cases g.inputs <;> rfl
    have agree (gs : List Gate) (within : ∀ g ∈ gs, g ∈ B.gates) (w z : List Bool)
        (sameLen : w.length = z.length)
        (same : ∀ i, i ≠ reserved → w.getD i false = z.getD i false) :
        ∀ i, i ≠ reserved → (run gs w).getD i false = (run gs z).getD i false := by
      induction gs generalizing w z with
      | nil => exact same
      | cons g gs ih =>
        change ∀ i, i ≠ reserved →
          (run gs (step w g)).getD i false = (run gs (step z g)).getD i false
        apply ih (fun a mem => within a (List.mem_cons_of_mem _ mem))
        · simp [step, sameLen]
        · intro i off
          have member := within g (List.mem_cons_self)
          have values : g.op.eval (g.inputs.map fun a => w.getD a false) =
              g.op.eval (g.inputs.map fun a => z.getD a false) := by
            rw [simplify g member, simplify g member]
            congr 1
            exact List.map_congr_left (fun a ha => same a (fun eq => avoids g member (eq ▸ ha)))
          unfold step
          rw [values]
          by_cases before : i < w.length
          · rw [List.getD_append _ _ _ _ before, List.getD_append _ _ _ _ (sameLen ▸ before)]
            exact same i off
          · have after : w.length ≤ i := Nat.le_of_not_gt before
            rw [List.getD_append_right _ _ _ _ after,
              List.getD_append_right _ _ _ _ (sameLen ▸ after), sameLen]
    have baseLen (x : Fin 8 → Bool) : (A.wires (List.ofFn x)).length = reserved := by
      change (run A.gates (List.ofFn x)).length = 8 + A.gates.length
      rw [lengthRun, List.length_ofFn]
    let noInput : Fin 8 → Bool := fun _ => false
    let oneInput : Fin 8 → Bool := fun i => decide (i = 0)
    have zeroLow : f oneInput = false := by rfl
    have zeroHigh : h noInput = false := by rfl
    have oneHigh : h oneInput = true := by rfl
    have outputDifferent : B.output ≠ reserved := by
      intro output
      have atOutput (x : Fin 8 → Bool) : B.eval (A.wires (List.ofFn x) ++ [k]) = k := by
        change (run B.gates (A.wires (List.ofFn x) ++ [k])).getD B.output false = k
        have inside : reserved < (A.wires (List.ofFn x) ++ [k]).length := by
          rw [List.length_append, baseLen x]
          exact Nat.lt_succ_self reserved
        rw [output, keep _ _ _ inside]
        rw [List.getD_append_right _ _ _ _ (by rw [baseLen x]), baseLen x, Nat.sub_self]
        rfl
      exact Bool.noConfusion
        (zeroHigh.symm.trans ((hi noInput).symm.trans ((atOutput noInput).trans
          ((atOutput oneInput).symm.trans ((hi oneInput).trans oneHigh)))))
    let w := A.wires (List.ofFn oneInput)
    have len : w.length = reserved := baseLen oneInput
    have agreesAtStart (i : ℕ) (other : i ≠ reserved) :
        (w ++ [circuitFun 8 A oneInput]).getD i false = (w ++ [k]).getD i false := by
      by_cases before : i < w.length
      · rw [List.getD_append _ _ _ _ before, List.getD_append _ _ _ _ before]
      · have after : w.length ≤ i := Nat.le_of_not_gt before
        rw [List.getD_append_right _ _ _ _ after, List.getD_append_right _ _ _ _ after]
        have positive : 0 < i - w.length := by omega
        obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
        simp [hn]
    have equal := agree B.gates (fun _ mem => mem) (w ++ [circuitFun 8 A oneInput])
      (w ++ [k]) (by simp) agreesAtStart B.output outputDifferent
    change B.eval (A.wires (List.ofFn oneInput) ++ [circuitFun 8 A oneInput]) =
      B.eval (A.wires (List.ofFn oneInput) ++ [k]) at equal
    exact Bool.noConfusion (zeroLow.symm.trans ((lo oneInput).symm.trans
      (equal.trans ((hi oneInput).trans oneHigh))))
  by_contra! below
  have nonconstant : ¬ ∃ c : Bool, ∀ x, circuitFun 8 A x = c := by
    rintro ⟨c, fixed⟩
    have notEmpty : A.gates ≠ [] := by
      intro empty
      have atLast : A.output = 7 := by
        change A.output + 1 = 8 + A.gates.length at last
        rw [empty, List.length_nil] at last
        omega
      apply (notLiteral (7 : Fin 8)).1
      funext x
      change (A.gates.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x)).getD A.output false = x 7
      rw [empty, atLast]
      rfl
    have varying : ∃ x y, f x ≠ f y := by
      refine ⟨(fun _ => false), (fun i => decide (i = 0 ∨ i = 1)), ?_⟩
      decide +kernel
    obtain ⟨C, fanC, sizeC, computesC⟩ :=
      removeConstant 8 A B f c fanA fanB last notEmpty varying fixed lo
    exact edgeLower ⟨C, fanC, by omega, computesC⟩
  by_cases exactlyOne : tally = 1
  · exact (Nat.not_le_of_lt below)
      (one A B k fanA fanB last exactlyOne nonconstant notLiteral toggles lo hi)
  · have counts : tally = 2 ∨ tally = 3 := by omega
    exact (Nat.not_le_of_lt below)
      (many A B k fanA fanB last counts nonconstant notLiteral toggles lo hi)
