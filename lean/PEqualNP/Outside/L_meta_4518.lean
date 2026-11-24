import Mathlib
import PEqualNP.Defs

/-!
A gate that reads only inputs can be moved to the front of a circuit.

The new circuit starts with that gate, then runs the other gates in their old order. Each wire
read by a gate is renamed to the new place of the gate that made it. A gate of the old circuit
may read a wire that does not exist yet, which gives false; such a read is sent to a wire past
the end of the new circuit, which gives false as well.
-/

namespace PEqualNP.Outside.L_meta_4518

open PEqualNP.CircuitLowerBounds

/-- One evaluation step of a circuit. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (w : ℕ) :
    (W ++ [v]).getD w false = if w = W.length then v else W.getD w false := by
  rcases Nat.lt_trichotomy w W.length with h | h | h
  · rw [if_neg (Nat.ne_of_lt h), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h]
  · subst h
    rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
    simp
  · rw [if_neg (Nat.ne_of_gt h), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem getD_big (W : List Bool) (w : ℕ) (h : W.length ≤ w) : W.getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem step_length (W : List Bool) (g : Gate) : (step W g).length = W.length + 1 := by
  simp [step]

theorem foldl_length (gs : List Gate) : ∀ W : List Bool,
    (gs.foldl step W).length = W.length + gs.length := by
  induction gs with
  | nil =>
    intro W
    simp
  | cons g gs ih =>
    intro W
    rw [List.foldl_cons, ih, step_length, List.length_cons]
    omega

theorem foldl_prefix (gs : List Gate) : ∀ (W : List Bool) (i : ℕ), i < W.length →
    (gs.foldl step W).getD i false = W.getD i false := by
  induction gs with
  | nil =>
    intro W i _
    rfl
  | cons g gs ih =>
    intro W i hi
    rw [List.foldl_cons, ih (step W g) i (by rw [step_length]; omega)]
    show (W ++ [_]).getD i false = _
    rw [getD_snoc, if_neg (Nat.ne_of_lt hi)]

/-- The value of the wire of gate `j`, from the final wire values: the gate reads the earlier
wires, and false for any other index. -/
theorem wire_spec (gs : List Gate) : ∀ (W : List Bool) (j : ℕ) (h : Gate), gs[j]? = some h →
    (gs.foldl step W).getD (W.length + j) false =
      h.op.eval (h.inputs.map fun i =>
        if i < W.length + j then (gs.foldl step W).getD i false else false) := by
  induction gs with
  | nil =>
    intro W j h hj
    simp at hj
  | cons g gs ih =>
    intro W j h hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [List.foldl_cons, Nat.add_zero,
        foldl_prefix gs (step W g) W.length (by rw [step_length]; omega)]
      show (W ++ [_]).getD W.length false = _
      rw [getD_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < W.length
      · rw [if_pos hi, foldl_prefix gs (step W g) i (by rw [step_length]; omega)]
        show _ = (W ++ [_]).getD i false
        rw [getD_snoc, if_neg (Nat.ne_of_lt hi)]
      · rw [if_neg hi, getD_big W i (by omega)]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have key := ih (step W g) j h hj
      rw [step_length] at key
      rw [List.foldl_cons]
      have e : W.length + (j + 1) = W.length + 1 + j := by omega
      rw [e]
      exact key

/-- The new name of the wire `w` when it is read by the old gate number `j`. -/
def rho (p N j w : ℕ) : ℕ :=
  if w < 9 then w else if 9 + j ≤ w then 9 + N else if w < 9 + p then w + 1
  else if w = 9 + p then 9 else w

/-- The old gate number `j` with its wires renamed. -/
def rel (p N j : ℕ) (h : Gate) : Gate := ⟨h.op, h.inputs.map (rho p N j)⟩

/-- The new place of the old gate number `j`. -/
def pos (p j : ℕ) : ℕ := if j < p then j + 1 else if j = p then 0 else j

/-- The gates of the new circuit. -/
def newGates (x2 x3 : List Gate) (g : Gate) : List Gate :=
  g :: ((x2.zipIdx.map fun q => rel x2.length (x2.length + 1 + x3.length) q.2 q.1) ++
    (x3.zipIdx.map fun q =>
      rel x2.length (x2.length + 1 + x3.length) (x2.length + 1 + q.2) q.1))

theorem newGates_length (x2 x3 : List Gate) (g : Gate) :
    (newGates x2 x3 g).length = x2.length + 1 + x3.length := by
  simp [newGates]
  omega

theorem newGate_at (x2 x3 : List Gate) (g : Gate) (j : ℕ) (h : Gate)
    (hj : (x2 ++ g :: x3)[j]? = some h) :
    (newGates x2 x3 g)[pos x2.length j]? =
      some (if j = x2.length then g else rel x2.length (x2.length + 1 + x3.length) j h) := by
  rcases Nat.lt_trichotomy j x2.length with hlt | heq | hgt
  · rw [List.getElem?_append_left hlt] at hj
    have hp : pos x2.length j = j + 1 := by simp [pos, hlt]
    rw [hp, if_neg (Nat.ne_of_lt hlt)]
    obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.1 hj
    simp [newGates, List.getElem?_append_left, hlt]
  · subst heq
    simp [pos, newGates]
  · obtain ⟨m, rfl⟩ : ∃ m, j = x2.length + 1 + m := ⟨j - x2.length - 1, by omega⟩
    have hp : pos x2.length (x2.length + 1 + m) = x2.length + 1 + m := by
      unfold pos
      rw [if_neg (by omega), if_neg (by omega)]
    have e : x2.length + 1 + m - x2.length = m + 1 := by omega
    rw [List.getElem?_append_right (by omega), e, List.getElem?_cons_succ] at hj
    rw [hp, if_neg (by omega)]
    have e2 : x2.length + 1 + m = (x2.length + m) + 1 := by omega
    rw [e2]
    simp [newGates, List.getElem?_append_right, List.getElem?_zipIdx, hj]
    rw [e2]

theorem pos_lt (p j m : ℕ) (hm : m < j) (hj : j ≠ p) : pos p m < pos p j := by
  unfold pos
  split_ifs <;> omega

theorem pos_le (p N j : ℕ) (hp : p < N) (hj : j < N) : pos p j < N + 1 := by
  unfold pos
  split_ifs <;> omega

theorem rho_mid (p N j m : ℕ) (hm : m < j) : rho p N j (9 + m) = 9 + pos p m := by
  unfold rho pos
  split_ifs <;> omega

/-- The wire of the old gate `j` and the wire of its new place carry the same value. -/
theorem value_at (x2 x3 : List Gate) (g : Gate) (hg : ∀ i ∈ g.inputs, i < 9) (l : List Bool)
    (hl : l.length = 9) : ∀ (j : ℕ) (h : Gate), (x2 ++ g :: x3)[j]? = some h →
    ((newGates x2 x3 g).foldl step l).getD (9 + pos x2.length j) false =
      ((x2 ++ g :: x3).foldl step l).getD (9 + j) false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h hj
    have hjN : j < x2.length + 1 + x3.length := by
      have := (List.getElem?_eq_some_iff.1 hj).1
      simp at this
      omega
    have s1 := wire_spec (x2 ++ g :: x3) l j h hj
    have s2 := wire_spec (newGates x2 x3 g) l (pos x2.length j) _ (newGate_at x2 x3 g j h hj)
    rw [hl] at s1 s2
    rw [s1, s2]
    by_cases hjp : j = x2.length
    · rw [if_pos hjp]
      have hh : h = g := by
        rw [hjp] at hj
        simpa using hj.symm
      rw [hh]
      congr 1
      apply List.map_congr_left
      intro i hi
      have h9 := hg i hi
      rw [if_pos (by omega), if_pos (by omega), foldl_prefix _ l i (by omega),
        foldl_prefix _ l i (by omega)]
    · rw [if_neg hjp]
      show h.op.eval ((h.inputs.map (rho x2.length (x2.length + 1 + x3.length) j)).map _) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      show (if rho x2.length (x2.length + 1 + x3.length) j i < 9 + pos x2.length j then
          ((newGates x2 x3 g).foldl step l).getD
            (rho x2.length (x2.length + 1 + x3.length) j i) false else false) = _
      by_cases h9 : i < 9
      · have e : rho x2.length (x2.length + 1 + x3.length) j i = i := by
          unfold rho
          rw [if_pos h9]
        rw [e, if_pos (by omega), if_pos (by omega), foldl_prefix _ l i (by omega),
          foldl_prefix _ l i (by omega)]
      · by_cases hfw : 9 + j ≤ i
        · have e : rho x2.length (x2.length + 1 + x3.length) j i =
              9 + (x2.length + 1 + x3.length) := by
            unfold rho
            rw [if_neg h9, if_pos hfw]
          have hpl := pos_le x2.length (x2.length + 1 + x3.length) j (by omega) hjN
          rw [e, if_neg (by omega), if_neg (by omega)]
        · obtain ⟨m, rfl⟩ : ∃ m, i = 9 + m := ⟨i - 9, by omega⟩
          have hm : m < j := by omega
          have hmN : m < (x2 ++ g :: x3).length := by
            simp
            omega
          rw [rho_mid _ _ _ _ hm, if_pos (by have := pos_lt x2.length j m hm hjp; omega),
            if_pos (by omega)]
          exact ih m hm _ (List.getElem?_eq_getElem hmN)

theorem moved (C : Circuit) (x2 x3 : List Gate) (g : Gate) (hC : C.gates = x2 ++ g :: x3)
    (legal : PEqualNP.MetaComplexity.FanInTwo C) (hg : ∀ i ∈ g.inputs, i < 9) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = C.size ∧
      PEqualNP.MetaComplexity.circuitFun 9 D = PEqualNP.MetaComplexity.circuitFun 9 C ∧
      ∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false =
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
  refine ⟨⟨newGates x2 x3 g,
    rho x2.length (x2.length + 1 + x3.length) (x2.length + 1 + x3.length) C.output⟩, ?_, ?_, ?_, ?_⟩
  · -- the gates keep their operation and their number of inputs
    intro d hd
    have legal' : ∀ d ∈ x2 ++ g :: x3, d.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        d.inputs.length ≤ 2 := by
      intro d hd
      exact legal d (hC ▸ hd)
    simp only [newGates, List.mem_cons, List.mem_append, List.mem_map] at hd
    rcases hd with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact legal' d (by simp)
    · have hm : q.1 ∈ x2 := (List.mem_zipIdx hq |> fun _ => (List.of_mem_zip (by
        rw [List.zipIdx_eq_zip_range'] at hq; exact hq)).1)
      have := legal' q.1 (by simp [hm])
      exact ⟨this.1, by simpa [rel] using this.2⟩
    · have hm : q.1 ∈ x3 := (List.of_mem_zip (by
        rw [List.zipIdx_eq_zip_range'] at hq; exact hq)).1
      have := legal' q.1 (by simp [hm])
      exact ⟨this.1, by simpa [rel] using this.2⟩
  · show (newGates x2 x3 g).length = C.gates.length
    rw [newGates_length, hC]
    simp
    omega
  · funext x
    show ((newGates x2 x3 g).foldl step (List.ofFn x)).getD
        (rho x2.length (x2.length + 1 + x3.length) (x2.length + 1 + x3.length) C.output) false =
      (C.gates.foldl step (List.ofFn x)).getD C.output false
    rw [hC]
    have hl : (List.ofFn x).length = 9 := by simp
    by_cases h9 : C.output < 9
    · have e : rho x2.length (x2.length + 1 + x3.length) (x2.length + 1 + x3.length) C.output =
          C.output := by
        unfold rho
        rw [if_pos h9]
      rw [e, foldl_prefix _ _ _ (by omega), foldl_prefix _ _ _ (by omega)]
    · by_cases hfw : 9 + (x2.length + 1 + x3.length) ≤ C.output
      · have e : rho x2.length (x2.length + 1 + x3.length) (x2.length + 1 + x3.length) C.output =
            9 + (x2.length + 1 + x3.length) := by
          unfold rho
          rw [if_neg h9, if_pos hfw]
        rw [e, getD_big _ _ (by rw [foldl_length, newGates_length, hl]),
          getD_big _ _ (by rw [foldl_length, hl]; simp; omega)]
      · obtain ⟨m, hm⟩ : ∃ m, C.output = 9 + m := ⟨C.output - 9, by omega⟩
        have hmN : m < (x2 ++ g :: x3).length := by
          simp
          omega
        rw [hm, rho_mid _ _ _ _ (by omega)]
        exact value_at x2 x3 g hg _ hl m _ (List.getElem?_eq_getElem hmN)
  · intro x
    show ((newGates x2 x3 g).foldl step (List.ofFn x)).getD 9 false = _
    have hl : (List.ofFn x).length = 9 := by simp
    have s := wire_spec (newGates x2 x3 g) (List.ofFn x) 0 g (by simp [newGates])
    rw [hl] at s
    rw [s]
    congr 1
    apply List.map_congr_left
    intro i hi
    have h9 := hg i hi
    rw [if_pos (by omega), foldl_prefix _ _ i (by omega)]

end PEqualNP.Outside.L_meta_4518

theorem PEqualNP.Outside.L_meta_4518 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates = x2 ++ x4 :: x3 → PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x7 ∈ x4.inputs, x7 < (9 : ℕ)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size = x1.size ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x8 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ∧ ∀ (x9 : Fin (9 : ℕ) → Bool), (x8.wires (List.ofFn x9)).getD (9 : ℕ) Bool.false = x4.op.eval (List.map (fun (x10 : ℕ) => (List.ofFn x9).getD x10 Bool.false) x4.inputs) := by
  intro C x2 x3 g hC legal hg
  exact PEqualNP.Outside.L_meta_4518.moved C x2 x3 g hC legal hg
