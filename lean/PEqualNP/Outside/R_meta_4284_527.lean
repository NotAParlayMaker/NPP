import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each column records the twelve edge inputs followed by the twelve maximal
-- independent sets. The target column has exactly its first twelve bits set.
-- The two hypotheses rule out an exact column and a strict intersection,
-- respectively.
theorem PEqualNP.Outside.R_meta_4284_527
    (single : ∀ s : List (Bool × Fin 25 × Fin 25), s.length = 13 →
      let w := s.foldl (fun w g =>
        let read := fun i : Fin 25 => ite (i.val = 24) 16777215 (w.getD i.val 0)
        w ++ [ite (g.1 = true) (read g.2.1 &&& read g.2.2) (read g.2.1 ||| read g.2.2)])
        ([5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661] : List (BitVec 24));
      ∀ a : ℕ, 10 ≤ a → a < 23 → w.getD a 0 ≠ 4095)
    (intersection : ∀ s : List (Bool × Fin 25 × Fin 25), s.length = 13 →
      let w := s.foldl (fun w g =>
        let read := fun i : Fin 25 => ite (i.val = 24) 16777215 (w.getD i.val 0)
        w ++ [ite (g.1 = true) (read g.2.1 &&& read g.2.2) (read g.2.1 ||| read g.2.2)])
        ([5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661] : List (BitVec 24));
      ∀ a b : ℕ, 10 ≤ a → a < b → b < 23 →
        w.getD a 0 ≠ 4095 → w.getD b 0 ≠ 4095 → w.getD a 0 &&& w.getD b 0 ≠ 4095) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 = (0 : ℕ) →         (10 : ℕ) ≤ x2 →           x2 ≤ x3 →             x3 < (23 : ℕ) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);                 (x11.getD x2 Bool.false && x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  let Word := BitVec 24
  let Instr := Bool × Fin 25 × Fin 25

  let col (w : List Word) (i : Fin 25) : Word :=
    if i.val = 24 then 16777215 else w.getD i.val 0

  let step (w : List Word) (g : Instr) : List Word :=
    w ++ [if g.1 then col w g.2.1 &&& col w g.2.2 else col w g.2.1 ||| col w g.2.2]

  let boolStep (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let agree (w : List Word) (v : List Bool) (r : Fin 24) : Prop :=
    w.length = v.length ∧ ∀ i, (w.getD i 0).getLsbD r.val = v.getD i false

  -- Index 23 is absent at every gate evaluation, including the last gate.
  -- Index 24 supplies true for an empty AND.
  let src (i : ℕ) : Fin 25 :=
    if h : i < 23 then ⟨i, by omega⟩ else 23

  have col_src {w : List Word} {v : List Bool} {r : Fin 24}
      (h : agree w v r) (hlen : w.length < 23) (i : ℕ) :
      (col w (src i)).getLsbD r.val = v.getD i false := by
    by_cases hi : i < 23
    · simpa [col, src, hi, Nat.ne_of_lt (show i < 24 by omega)] using h.2 i
    · have hv : v.length ≤ i := by have := h.1; omega
      have hw : w.length ≤ 23 := by omega
      unfold src
      rw [dite_eq_right hi]
      change (w.getD 23 0).getLsbD r.val = v.getD i false
      rw [List.getD_eq_default w 0 hw, List.getD_eq_default v false hv]
      exact BitVec.getLsbD_zero

  have append_agree {w : List Word} {v : List Bool} {r : Fin 24}
      (h : agree w v r) {a : Word} {b : Bool} (hab : a.getLsbD r.val = b) :
      agree (w ++ [a]) (v ++ [b]) r := by
    refine ⟨by simp [h.1], fun i => ?_⟩
    by_cases hi : i < w.length
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by rwa [← h.1])]
      exact h.2 i
    · have hw : w.length ≤ i := by omega
      have hv : v.length ≤ i := by rwa [← h.1]
      rw [List.getD_append_right _ _ _ _ hw, List.getD_append_right _ _ _ _ hv, ← h.1]
      cases i - w.length with
      | zero => simpa using hab
      | succ j => simp [List.getD_eq_getElem?_getD]; exact BitVec.getLsbD_zero

  let isAnd (op : GateOp) : Bool :=
    GateOp.casesOn op true false false (fun _ => false) false
  -- Use the recursors so this proof elaborates without auxiliary declarations.
  let instruction (g : Gate) : Instr :=
    List.casesOn g.inputs
      (Bool.rec (false, 23, 23) (true, 24, 24) (isAnd g.op))
      (fun a tail => List.casesOn tail (false, src a, src a)
        (fun b _ => (isAnd g.op, src a, src b)))

  have step_agree {w : List Word} {v : List Bool} {r : Fin 24}
      (h : agree w v r) (hlen : w.length < 23) (g : Gate)
      (hop : g.op = .and ∨ g.op = .or) (hfan : g.inputs.length ≤ 2) :
      agree (step w (instruction g)) (boolStep v g) r := by
    apply append_agree h
    have hfalse : (w.getD 23 0).getLsbD r.val = false := by
      rw [List.getD_eq_default _ _ (by omega)]
      exact BitVec.getLsbD_zero
    have htrue : (16777215 : Word).getLsbD r.val = true := by
      change (BitVec.allOnes 24).getLsbD r.val = true
      rw [BitVec.getLsbD_allOnes]
      exact decide_eq_true r.isLt
    have hsrc (i : ℕ) := col_src h hlen i
    have hsrc' (i : ℕ) : (col w (src i) ||| col w (src i)).getLsbD r.val = v.getD i false := by
      rw [BitVec.getLsbD_or, hsrc, Bool.or_self]
    obtain ⟨op, xs⟩ := g
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
    · rcases hop with ho | ho <;> cases ho <;>
        first | exact (by change (w.getD 23 0 ||| w.getD 23 0).getLsbD r.val = false; rw [BitVec.getLsbD_or, hfalse]; rfl)
              | exact (by change ((16777215 : Word) &&& 16777215).getLsbD r.val = true; rw [BitVec.getLsbD_and, htrue]; rfl)
    · rcases hop with ho | ho <;> cases ho
      · change (col w (src a) ||| col w (src a)).getLsbD r.val = (_ && true)
        rw [Bool.and_true]
        exact hsrc' a
      · change (col w (src a) ||| col w (src a)).getLsbD r.val = (_ || false)
        rw [Bool.or_false]
        exact hsrc' a
    · rcases hop with ho | ho <;> cases ho <;>
        first | exact (by change (col w (src a) &&& col w (src b)).getLsbD r.val = (_ && (_ && true)); rw [BitVec.getLsbD_and, hsrc, hsrc, Bool.and_true]; rfl)
              | exact (by change (col w (src a) ||| col w (src b)).getLsbD r.val = (_ || (_ || false)); rw [BitVec.getLsbD_or, hsrc, hsrc, Bool.or_false]; rfl)
    · simp at hfan

  have replay (gs : List Gate) (w : List Word) (v : List Bool) (r : Fin 24)
      (h : agree w v r) (hlen : w.length + gs.length ≤ 23)
      (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
      agree ((gs.map instruction).foldl step w) (gs.foldl boolStep v) r := by
    induction gs generalizing w v with
    | nil => exact h
    | cons g gs ih =>
        have hg' := hg g (by simp)
        have hw : w.length < 23 := by simp at hlen; omega
        have hstep := step_agree h hw g hg'.1 hg'.2
        apply ih _ _ hstep
        · simpa [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
        · intro g' hg'
          exact hg g' (by simp [hg'])


  let seeds : List Word := [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661]

  -- Each natural number encodes the variables set to true on that row.
  let row (r : Fin 24) : Fin 9 → Bool :=
    fun i => ([3,6,12,24,17,33,66,132,264,160,320,288,42,50,69,104,116,138,201,208,261,276,385,402].getD r.val 0 : ℕ).testBit i.val

  let input (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 3]

  let edge (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5

  have init_agree (r : Fin 24) : agree seeds (input (row r)) r := by
    have h : ∀ (t : Fin 24) (i : Fin 10),
        (seeds.getD i.val 0).getLsbD t.val = (input (row t)).getD i.val false := by decide
    refine ⟨by rfl, fun i => ?_⟩
    by_cases hi : i < 10
    · exact h r ⟨i, hi⟩
    · rw [List.getD_eq_default seeds 0 (by change 10 ≤ i; omega),
          List.getD_eq_default (input (row r)) false (by change 10 ≤ i; omega)]
      exact BitVec.getLsbD_zero

  have row_target : ∀ r : Fin 24, (4095 : Word).getLsbD r.val = edge (row r) := by
    decide

  intro gs a b hlen hfan hzero ha hab hb
  have hg (g : Gate) (hmem : g ∈ gs) : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    obtain ⟨hop, hsize⟩ := hfan g hmem
    refine ⟨?_, hsize⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exfalso
      apply (List.countP_eq_zero.mp hzero g hmem)
      rw [hop]
      rfl
  -- Replay the same instructions on all rows, then isolate the differing bit.
  let s := gs.map instruction
  let w := s.foldl step seeds
  have hs : s.length = 13 := by simp [s, hlen]
  have hsingle (i : ℕ) (hi : 10 ≤ i) (hi' : i < 23) : w.getD i 0 ≠ 4095 :=
    single s hs i hi hi'
  have hword : w.getD a 0 &&& w.getD b 0 ≠ 4095 := by
    rcases eq_or_lt_of_le hab with rfl | hlt
    · rw [BitVec.and_self]
      exact hsingle a ha hb
    · exact intersection s hs a b ha hlt hb
        (hsingle a ha (by omega)) (hsingle b (by omega) hb)
  by_contra hn
  apply hword
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 24 := ⟨i, hi⟩
  have hr := replay gs seeds (input (row r)) r (init_agree r)
    (by change 10 + gs.length ≤ 23; omega) hg
  rw [BitVec.getLsbD_and]
  change ((w.getD a 0).getLsbD r.val && (w.getD b 0).getLsbD r.val) = (4095 : Word).getLsbD r.val
  rw [hr.2 a, hr.2 b, row_target r]
  exact Classical.not_not.mp (fun h => hn ⟨row r, h⟩)
