import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_3260_1
    (pin :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let seeded (a b : Fin 11) (x : Fin 9 → Bool) :=
        let w := List.ofFn x ++ [x 0 && x 3]
        w ++ [w.getD a.val false || w.getD b.val false]
      let reads (g : Gate) : Bool :=
        let binary := g.inputs.contains 4
        GateOp.rec binary binary ((g.inputs.take 1).contains 4) (fun _ => binary) binary g.op
      ∀ (C : Circuit) (a b : Fin 11), FanInTwo C → C.size ≤ 13 →
      (∀ x, C.eval (seeded a b x) = f x) →
      (2 ≤ (if a == 4 || b == 4 then 1 else 0) + C.gates.countP reads ∨
        ∃ i : Fin C.gates.length, let g := C.gates.get i
          reads g = true ∧ (g.op ≠ .or ∨ ∀ j ∈ g.inputs, j = 4 ∨ 11 + i.val ≤ j)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧
        (∀ x : Fin 8 → Bool, (D.wires (List.ofFn x)).getD 8 false = (x 0 && x 3)) ∧
        ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = f (Fin.insertNth (4 : Fin 9) false x))
    (minorBound :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ D : Circuit, ¬ (FanInTwo D ∧ D.size ≤ 13 ∧
        (∀ x : Fin 8 → Bool, (D.wires (List.ofFn x)).getD 8 false = (x 0 && x 3)) ∧
        ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = f (Fin.insertNth (4 : Fin 9) false x)))
    (oneOr :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let seeded (a b : Fin 11) (x : Fin 9 → Bool) :=
        let w := List.ofFn x ++ [x 0 && x 3]
        w ++ [w.getD a.val false || w.getD b.val false]
      let reads (g : Gate) : Bool :=
        let binary := g.inputs.contains 4
        GateOp.rec binary binary ((g.inputs.take 1).contains 4) (fun _ => binary) binary g.op
      ∀ (C : Circuit) (a b : Fin 11), FanInTwo C →
      11 * a.val + b.val ∈ [1,2,3,4,6,13,15,16,17,18,19,20,50,53,73,75] →
      C.size ≤ 13 → (∀ x, C.eval (seeded a b x) = f x) →
      (a == 4 || b == 4) = false → C.gates.countP reads = 1 →
      (∃ (i : Fin C.gates.length) (j : ℕ), let g := C.gates.get i
        reads g = true ∧ g.op = .or ∧ j ∈ g.inputs ∧ 11 ≤ j ∧ j < 11 + i.val) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (11 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     (11 : ℕ) * ↑x2 + ↑x3 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (13 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (20 : ℕ), (50 : ℕ), (53 : ℕ), (73 : ℕ), (75 : ℕ)] →       have x6 : (Fin (9 : ℕ) → Bool) → Bool := fun (x6 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x7 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x7.1 && x6 x7.2;       have x7 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x7 : Fin (9 : ℕ) → Bool) => List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ))];       have x8 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.head? == Option.some (4 : ℕ) || x8.op.eval [Bool.true, Bool.true] && x8.inputs.contains (4 : ℕ);       (∀ (x9 : Fin (9 : ℕ) → Bool), x1.eval (x7 x9 ++ [(x7 x9).getD (↑x2) Bool.false || (x7 x9).getD (↑x3) Bool.false]) = x6 x9) → (if (x2 == (4 : Fin (11 : ℕ)) || x3 == (4 : Fin (11 : ℕ))) = Bool.true then (1 : ℕ) else (0 : ℕ)) + List.countP x8 x1.gates ≤ (2 : ℕ) → (14 : ℕ) ≤ x1.size := by
  let target (x : Fin 9 → Bool) : Bool :=
    ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8),
      (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2

  let allowed (a b : Fin 11) : Prop :=
    11 * a.val + b.val ∈ [1,2,3,4,6,13,15,16,17,18,19,20,50,53,73,75]

  let seed (a b : Fin 11) (x : Fin 9 → Bool) : List Bool :=
    let base := List.ofFn x ++ [x 0 && x 3]
    base ++ [base.getD a.val false || base.getD b.val false]

  let active (g : Gate) : List ℕ :=
    GateOp.rec (motive := fun _ => List ℕ)
      g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs g.op

  let readsFour (g : Gate) : Bool :=
    let binary := g.inputs.contains 4
    GateOp.rec binary binary ((g.inputs.take 1).contains 4) (fun _ => binary) binary g.op

  have readForm (g : Gate) : readsFour g = (active g).contains 4 := by
    obtain ⟨op, ins⟩ := g
    cases op <;> rfl

  let prefixFour (a b : Fin 11) : Bool := a == 4 || b == 4

  let badPattern (C : Circuit) (a b : Fin 11) : Prop :=
    2 ≤ (if prefixFour a b then 1 else 0) + C.gates.countP readsFour ∨
    ∃ i : Fin C.gates.length,
      let g := C.gates[i]
      readsFour g = true ∧ (g.op ≠ .or ∨ ∀ j ∈ g.inputs, j = 4 ∨ 11 + i.val ≤ j)

  let sample (i : ℕ) : ℕ := [1,10,5,8,0,40,65,129,257,9].getD i 0

  let testBits (a b j : Fin 11) : ℕ :=
    if j.val < 10 then sample j.val else if a == 4 then sample b.val else sample a.val

  let row (bits : ℕ) (x : Fin 9) : Bool := bits.testBit x.val

  have testRows : ∀ a b j : Fin 11,
      11 * a.val + b.val ∈ [1,2,3,4,6,13,15,16,17,18,19,20,50,53,73,75] →
      j.val ≠ 4 → (prefixFour a b = false ∨ j.val = 10) →
      let bits := testBits a b j
      let lo := row bits
      let hi := row (bits + 16)
      target lo = false ∧ target hi = true ∧
        (seed a b lo).getD j.val false = true ∧ seed a b hi = (seed a b lo).set 4 true := by
    decide

  let run (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have evalActive (g : Gate) (w : List Bool) :
      g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval ((active g).map fun i => w.getD i false) := by
    obtain ⟨op, ins⟩ := g
    cases op <;> try rfl
    cases ins <;> rfl

  have agreeThrough (gs : List Gate) (a b : List Bool)
      (len : a.length = b.length) (hasFour : 4 < a.length)
      (same : ∀ i, i ≠ 4 → a.getD i false = b.getD i false)
      (allowedGates : ∀ g ∈ gs, readsFour g = false ∨
        ∃ j, g.op = .or ∧ j ∈ g.inputs ∧ j < a.length ∧
          a.getD j false = true ∧ b.getD j false = true) :
      ∀ i, i ≠ 4 → (run gs a).getD i false = (run gs b).getD i false := by
    induction gs generalizing a b with
    | nil => exact same
    | cons g rest ih =>
      let evaluate (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have step : evaluate a = evaluate b := by
        rcases allowedGates g (List.mem_cons_self) with absent | ⟨j, hop, hj, _, ha, hb⟩
        · dsimp only [evaluate]
          rw [evalActive g a, evalActive g b]
          apply congrArg g.op.eval
          apply List.map_congr_left
          intro i hi
          apply same
          intro eq
          subst i
          have yes : readsFour g = true := (readForm g).trans (List.contains_iff_mem.mpr hi)
          simp [yes] at absent
        · have yes (w : List Bool) (h : w.getD j false = true) : evaluate w = true := by
            change g.op.eval (g.inputs.map fun i => w.getD i false) = true
            rw [hop]
            change (g.inputs.map fun i => w.getD i false).any id = true
            exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨j, hj, rfl⟩, h⟩
          exact (yes a ha).trans (yes b hb).symm
      change ∀ i, i ≠ 4 → (run rest (a ++ [evaluate a])).getD i false =
        (run rest (b ++ [evaluate b])).getD i false
      apply ih
      · simp [len]
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro i hi
        by_cases h : i < a.length
        · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (by omega)]
          exact same i hi
        · simp only [List.getD_eq_getElem?_getD,
            List.getElem?_append_right (show a.length ≤ i by omega),
            List.getElem?_append_right (show b.length ≤ i by omega), step, len]
      · intro d hd
        rcases allowedGates d (List.mem_cons_of_mem _ hd) with h | ⟨j, op, hj, bound, ha, hb⟩
        · exact Or.inl h
        · refine Or.inr ⟨j, op, hj, by simp; omega, ?_, ?_⟩
          · rw [List.getD_append _ _ _ _ bound]
            exact ha
          · rw [List.getD_append _ _ _ _ (show j < b.length by omega)]
            exact hb

  have runKeeps (gs : List Gate) (w : List Bool) (i : ℕ) (bound : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      let value := g.op.eval (g.inputs.map fun p => w.getD p false)
      change (run gs (w ++ [value])).getD i false = w.getD i false
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ bound]

  have outputNotFour {C : Circuit} {a b : Fin 11}
      (correct : ∀ x, C.eval (seed a b x) = target x) : C.output ≠ 4 := by
    intro out
    have h := correct (row 6)
    have got := runKeeps C.gates (seed a b (row 6)) 4 (by simp [seed])
    change (run C.gates (seed a b (row 6))).getD C.output false = target (row 6) at h
    rw [out, got] at h
    have low : (seed a b (row 6)).getD 4 false = false := by
      unfold seed
      rw [List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simp)]
      decide
    rw [low] at h
    exact Bool.false_ne_true (h.trans (by decide))

  have maskContradiction {C : Circuit} {a b : Fin 11}
      (pairs : allowed a b) (correct : ∀ x, C.eval (seed a b x) = target x)
      (j : Fin 11) (different : j.val ≠ 4)
      (supports : prefixFour a b = false ∨ j.val = 10)
      (gates : ∀ g ∈ C.gates, readsFour g = false ∨ g.op = .or ∧ j.val ∈ g.inputs) : False := by
    let low := row (testBits a b j)
    let high := row (testBits a b j + 16)
    have test := testRows a b j pairs different supports
    change target low = false ∧ target high = true ∧
      (seed a b low).getD j.val false = true ∧
      seed a b high = (seed a b low).set 4 true at test
    obtain ⟨lowVal, highVal, seedTrue, setFour⟩ := test
    have same : ∀ i, i ≠ 4 → (seed a b low).getD i false = (seed a b high).getD i false := by
      intro i hi
      rw [setFour, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne hi.symm]
    have masked (g : Gate) (hg : g ∈ C.gates) : readsFour g = false ∨
        ∃ i, g.op = .or ∧ i ∈ g.inputs ∧ i < (seed a b low).length ∧
          (seed a b low).getD i false = true ∧ (seed a b high).getD i false = true := by
      rcases gates g hg with absent | ⟨hop, hj⟩
      · exact Or.inl absent
      · exact Or.inr ⟨j.val, hop, hj, by simp [seed],
          seedTrue, (same j.val different).symm.trans seedTrue⟩
    have agrees := agreeThrough C.gates (seed a b low) (seed a b high) (by simp [seed])
      (by simp [seed]) same masked C.output (outputNotFour correct)
    change C.eval (seed a b low) = C.eval (seed a b high) at agrees
    rw [correct, correct, lowVal, highVal] at agrees
    exact Bool.false_ne_true agrees

  let minor (x : Fin 8 → Bool) : Bool :=
    target (Fin.insertNth (4 : Fin 9) false x)

  let minorWithPrefix (D : Circuit) : Prop :=
    FanInTwo D ∧ D.size ≤ 13 ∧
      (∀ x : Fin 8 → Bool, (D.wires (List.ofFn x)).getD 8 false = (x 0 && x 3)) ∧
      ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = minor x

  change (∀ D : Circuit, ¬ minorWithPrefix D) at minorBound
  change (∀ (C : Circuit) (a b : Fin 11), FanInTwo C → C.size ≤ 13 →
    (∀ x, C.eval (seed a b x) = target x) → badPattern C a b →
    ∃ D, minorWithPrefix D) at pin
  change (∀ (C : Circuit) (a b : Fin 11), FanInTwo C → allowed a b →
    C.size ≤ 13 → (∀ x, C.eval (seed a b x) = target x) → prefixFour a b = false →
    C.gates.countP readsFour = 1 →
    (∃ (i : Fin C.gates.length) (j : ℕ), let g := C.gates[i]
      readsFour g = true ∧ g.op = .or ∧ j ∈ g.inputs ∧ 11 ≤ j ∧ j < 11 + i.val) → False) at oneOr
  intro C a b fan pairs
  dsimp only
  intro correct _
  by_contra tooSmall
  change allowed a b at pairs
  change (∀ x, C.eval (seed a b x) = target x) at correct
  have size : C.size ≤ 13 := by omega
  have good : ¬ badPattern C a b := by
    intro bad
    obtain ⟨D, hD⟩ := pin C a b fan size correct bad
    exact minorBound D hD
  have total : (if prefixFour a b then 1 else 0) + C.gates.countP readsFour < 2 := by
    exact Nat.lt_of_not_ge fun h => good (Or.inl h)
  have someRead : 0 < C.gates.countP readsFour := by
    by_contra h
    apply maskContradiction pairs correct (10 : Fin 11) (by decide) (Or.inr rfl)
    intro g hg
    left
    cases hg' : readsFour g
    · rfl
    · exact False.elim (h (List.countP_pos_iff.mpr ⟨g, hg, hg'⟩))
  have noPrefix : prefixFour a b = false := by
    cases hp : prefixFour a b
    · rfl
    · have many : 2 ≤ 1 + C.gates.countP readsFour := by omega
      exact False.elim (good (Or.inl (by rw [hp]; exact many)))
  have exactlyOne : C.gates.countP readsFour = 1 := by
    have atMost : C.gates.countP readsFour < 2 := by
      simpa only [noPrefix, Bool.false_eq_true, ite_false, Nat.zero_add] using total
    omega
  let matching := C.gates.filter readsFour
  have listLength : matching.length = 1 := by
    simpa [matching, List.countP_eq_length_filter] using exactlyOne
  obtain ⟨reader, lone⟩ := List.length_eq_one_iff.mp listLength
  have member : reader ∈ C.gates ∧ readsFour reader = true := by
    apply List.mem_filter.mp
    change reader ∈ matching
    simp [lone]
  obtain ⟨slot, bound, identifies⟩ := List.getElem_of_mem member.1
  let i : Fin C.gates.length := ⟨slot, bound⟩
  have lookup : C.gates[i] = reader := identifies
  have valid : ¬ (reader.op ≠ .or ∨
      ∀ j ∈ reader.inputs, j = 4 ∨ 11 + i.val ≤ j) := by
    intro h
    apply good (Or.inr ⟨i, ?_⟩)
    simpa only [lookup] using And.intro member.2 h
  obtain ⟨hop, earlier⟩ := not_or.mp valid
  push Not at earlier
  obtain ⟨j, hj, diff, before⟩ := earlier
  have tailWire : 11 ≤ j := by
    by_contra h
    let q : Fin 11 := ⟨j, by omega⟩
    apply maskContradiction pairs correct q diff (Or.inl noPrefix)
    intro g hg
    cases hit : readsFour g
    · exact Or.inl rfl
    · right
      have sameReader : g = reader := by
        have yes : g ∈ matching := List.mem_filter.mpr ⟨hg, hit⟩
        simpa [lone] using yes
      subst g
      exact ⟨not_ne_iff.mp hop, hj⟩
  exact oneOr C a b fan pairs size correct noPrefix exactlyOne
    ⟨i, j, by rw [lookup]; exact ⟨member.2, not_ne_iff.mp hop, hj, tailWire, before⟩⟩
