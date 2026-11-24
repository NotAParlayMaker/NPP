import Mathlib
import PEqualNP.Defs

-- Symmetry cut for L-meta-3170. The map s = (1 5)(2 8)(6 7) is an automorphism of the graph
-- fixing 0, so it keeps the wire NOT x_0 and sends the pin lists [5, 1] and [5, 5] to [1, 5]
-- and [1, 1]. Relabelling the inputs of the circuit along s moves a refuting input across,
-- so the four pin lists come down to [1, 5] and [1, 1].
theorem PEqualNP.Outside.R_meta_3170_1
    (hA : ∀ (x1 : List ℕ), x1 = [(1 : ℕ), (5 : ℕ)] →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))))
    (h11 : ∀ (x1 : List ℕ), x1 = [(1 : ℕ), (1 : ℕ)] →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  classical
  let s : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  let p : ℕ → ℕ := fun i => if h : i < 9 then (s ⟨i, h⟩).val else i
  have hp_lt : ∀ i, i < 9 → p i < 9 := by
    intro i hi
    simp only [p, dif_pos hi]
    exact (s ⟨i, hi⟩).isLt
  have hp_fix : ∀ i, 9 ≤ i → p i = i := by
    intro i hi
    simp only [p, dif_neg (show ¬ i < 9 by omega)]
  have hp_iff : ∀ i n, 9 ≤ n → (p i < n ↔ i < n) := by
    intro i n hn
    by_cases hi : i < 9
    · have := hp_lt i hi
      constructor <;> intro <;> omega
    · rw [hp_fix i (by omega)]
  let rg : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun g => ⟨g.op, g.inputs.map p⟩
  let rc : PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Circuit :=
    fun C => ⟨C.gates.map rg, p C.output⟩
  have gapp : ∀ (l : List Bool) (v : Bool) (i : ℕ), (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
    intro l v i
    split_ifs with h1 h2
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    · subst h2
      simp [List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      have : i - l.length ≠ 0 := by omega
      simp [List.getElem?_singleton, this]
  have stepw : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l l' : List Bool),
      9 ≤ l.length → l'.length = l.length → (∀ i, l'.getD (p i) false = l.getD i false) →
      9 ≤ (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).length ∧
      ((gs.map rg).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l').length =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).length ∧
      ∀ i, ((gs.map rg).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l').getD (p i) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).getD i false := by
    intro gs
    induction gs with
    | nil => intro l l' h9 hl h; exact ⟨h9, hl, h⟩
    | cons g gs ih =>
      intro l l' h9 hl h
      simp only [List.map_cons, List.foldl_cons]
      have hv : (rg g).op.eval ((rg g).inputs.map fun i => l'.getD i false) =
          g.op.eval (g.inputs.map fun i => l.getD i false) := by
        simp only [rg, List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact h j
      apply ih
      · simp only [List.length_append, List.length_singleton]; omega
      · simp only [List.length_append, List.length_singleton, hl]
      · intro i
        rw [gapp, gapp, hv, hl]
        by_cases hi : i < l.length
        · rw [if_pos ((hp_iff i _ h9).2 hi), if_pos hi]
          exact h i
        · rw [if_neg (fun h' => hi ((hp_iff i _ h9).1 h')), if_neg hi, hp_fix i (by omega)]
  have wires_rc : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (l l' : List Bool),
      9 ≤ l.length → l'.length = l.length → (∀ i, l'.getD (p i) false = l.getD i false) →
      9 ≤ (C.wires l).length ∧ ((rc C).wires l').length = (C.wires l).length ∧
      ∀ i, ((rc C).wires l').getD (p i) false = (C.wires l).getD i false := by
    intro C l l' h9 hl h
    exact stepw C.gates l l' h9 hl h
  have mono_rc : ∀ C, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 (rc C) := by
    intro C hC g hg
    simp only [rc, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hC g0 hg0
    exact ⟨h1, by simpa [rg] using h2⟩
  have fan_rc : ∀ C, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo (rc C) := by
    intro C hC g hg
    simp only [rc, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hC g0 hg0
    exact ⟨h1, by simpa [rg] using h2⟩
  have size_rc : ∀ C, (rc C).size = C.size := by
    intro C
    show (C.gates.map rg).length = C.gates.length
    exact List.length_map _
  have ss : ∀ i, s (s i) = i := by decide
  have s0 : s 0 = 0 := rfl
  have s4 : s 4 = 4 := rfl
  have fe_inv : ∀ y : Fin 9 → Bool, (y (s (0 : Fin (9 : ℕ))) && y (s (1 : Fin (9 : ℕ))) || y (s (1 : Fin (9 : ℕ))) && y (s (2 : Fin (9 : ℕ))) || y (s (2 : Fin (9 : ℕ))) && y (s (3 : Fin (9 : ℕ))) || y (s (3 : Fin (9 : ℕ))) && y (s (4 : Fin (9 : ℕ))) || y (s (4 : Fin (9 : ℕ))) && y (s (0 : Fin (9 : ℕ))) || y (s (0 : Fin (9 : ℕ))) && y (s (5 : Fin (9 : ℕ))) || y (s (1 : Fin (9 : ℕ))) && y (s (6 : Fin (9 : ℕ))) || y (s (2 : Fin (9 : ℕ))) && y (s (7 : Fin (9 : ℕ))) || y (s (3 : Fin (9 : ℕ))) && y (s (8 : Fin (9 : ℕ))) || y (s (5 : Fin (9 : ℕ))) && y (s (7 : Fin (9 : ℕ))) || y (s (6 : Fin (9 : ℕ))) && y (s (8 : Fin (9 : ℕ))) || y (s (8 : Fin (9 : ℕ))) && y (s (5 : Fin (9 : ℕ)))) = (y (0 : Fin (9 : ℕ)) && y (1 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (2 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (3 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (4 : Fin (9 : ℕ)) || y (4 : Fin (9 : ℕ)) && y (0 : Fin (9 : ℕ)) || y (0 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (5 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (6 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (8 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ))) := by
    intro y
    simp only [s, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val]
    generalize y 0 = b0
    generalize y 1 = b1
    generalize y 2 = b2
    generalize y 3 = b3
    generalize y 4 = b4
    generalize y 5 = b5
    generalize y 6 = b6
    generalize y 7 = b7
    generalize y 8 = b8
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8
    decide
  -- the ten base wires: inputs, then NOT x_0
  have base_ok : ∀ (y : Fin 9 → Bool) (i : ℕ),
      (List.ofFn y ++ [!y 0]).getD (p i) false =
        (List.ofFn (fun j => y (s j)) ++ [!y (s 0)]).getD i false := by
    intro y i
    by_cases hi : i < 9
    · have hpi := hp_lt i hi
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simpa using hpi), List.getElem?_append_left (by simpa using hi),
        List.getElem?_ofFn, List.getElem?_ofFn]
      simp [p, hi, hpi]
    · rw [hp_fix i (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp [s0]
  -- transport of a refuting input: from the pins [p a, p b] for rc C to the pins [a, b] for C
  have key : ∀ (a b : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ y : Fin 9 → Bool, (rc C).eval ((List.ofFn y ++ [!y 0]) ++
          [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            ([p a, p b].map fun i => (List.ofFn y ++ [!y 0]).getD i false)]) ≠ (y (0 : Fin (9 : ℕ)) && y (1 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (2 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (3 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (4 : Fin (9 : ℕ)) || y (4 : Fin (9 : ℕ)) && y (0 : Fin (9 : ℕ)) || y (0 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (5 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (6 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (8 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)))) →
      ∃ z : Fin 9 → Bool, C.eval ((List.ofFn z ++ [!z 0]) ++
          [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            ([a, b].map fun i => (List.ofFn z ++ [!z 0]).getD i false)]) ≠ (z (0 : Fin (9 : ℕ)) && z (1 : Fin (9 : ℕ)) || z (1 : Fin (9 : ℕ)) && z (2 : Fin (9 : ℕ)) || z (2 : Fin (9 : ℕ)) && z (3 : Fin (9 : ℕ)) || z (3 : Fin (9 : ℕ)) && z (4 : Fin (9 : ℕ)) || z (4 : Fin (9 : ℕ)) && z (0 : Fin (9 : ℕ)) || z (0 : Fin (9 : ℕ)) && z (5 : Fin (9 : ℕ)) || z (1 : Fin (9 : ℕ)) && z (6 : Fin (9 : ℕ)) || z (2 : Fin (9 : ℕ)) && z (7 : Fin (9 : ℕ)) || z (3 : Fin (9 : ℕ)) && z (8 : Fin (9 : ℕ)) || z (5 : Fin (9 : ℕ)) && z (7 : Fin (9 : ℕ)) || z (6 : Fin (9 : ℕ)) && z (8 : Fin (9 : ℕ)) || z (8 : Fin (9 : ℕ)) && z (5 : Fin (9 : ℕ))) := by
    intro a b C hex
    obtain ⟨y, hy⟩ := hex
    refine ⟨fun j => y (s j), ?_⟩
    have hv : PEqualNP.CircuitLowerBounds.GateOp.or.eval
          ([p a, p b].map fun i => (List.ofFn y ++ [!y 0]).getD i false) =
        PEqualNP.CircuitLowerBounds.GateOp.or.eval
          ([a, b].map fun i => (List.ofFn (fun j => y (s j)) ++ [!y (s 0)]).getD i false) := by
      simp only [List.map_cons, List.map_nil, base_ok]
    have hlen0 : (List.ofFn (fun j => y (s j)) ++ [!y (s 0)]).length = 10 := by simp
    have hget : ∀ i, ((List.ofFn y ++ [!y 0]) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            ([p a, p b].map fun i => (List.ofFn y ++ [!y 0]).getD i false)]).getD (p i) false =
        ((List.ofFn (fun j => y (s j)) ++ [!y (s 0)]) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            ([a, b].map fun i => (List.ofFn (fun j => y (s j)) ++ [!y (s 0)]).getD i false)]).getD i false := by
      intro i
      rw [gapp (List.ofFn y ++ [!y 0]), gapp (List.ofFn (fun j => y (s j)) ++ [!y (s 0)]), hv]
      simp only [List.length_append, List.length_ofFn, List.length_singleton, Nat.reduceAdd]
      by_cases hi : i < 10
      · have hpi : p i < 10 := (hp_iff i 10 (by omega)).2 hi
        simp only [hi, hpi, if_true]
        exact base_ok y i
      · have hpi : ¬ p i < 10 := fun h' => hi ((hp_iff i 10 (by omega)).1 h')
        simp only [hi, hpi, if_false, hp_fix i (by omega)]
    obtain ⟨_, _, hw⟩ := wires_rc C _ _ (by simp) (by simp) hget
    have heval : (rc C).eval ((List.ofFn y ++ [!y 0]) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            ([p a, p b].map fun i => (List.ofFn y ++ [!y 0]).getD i false)]) =
        C.eval ((List.ofFn (fun j => y (s j)) ++ [!y (s 0)]) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            ([a, b].map fun i => (List.ofFn (fun j => y (s j)) ++ [!y (s 0)]).getD i false)]) :=
      hw C.output
    beta_reduce
    rw [← heval]
    show _ ≠ (y (s (0 : Fin (9 : ℕ))) && y (s (1 : Fin (9 : ℕ))) || y (s (1 : Fin (9 : ℕ))) && y (s (2 : Fin (9 : ℕ))) || y (s (2 : Fin (9 : ℕ))) && y (s (3 : Fin (9 : ℕ))) || y (s (3 : Fin (9 : ℕ))) && y (s (4 : Fin (9 : ℕ))) || y (s (4 : Fin (9 : ℕ))) && y (s (0 : Fin (9 : ℕ))) || y (s (0 : Fin (9 : ℕ))) && y (s (5 : Fin (9 : ℕ))) || y (s (1 : Fin (9 : ℕ))) && y (s (6 : Fin (9 : ℕ))) || y (s (2 : Fin (9 : ℕ))) && y (s (7 : Fin (9 : ℕ))) || y (s (3 : Fin (9 : ℕ))) && y (s (8 : Fin (9 : ℕ))) || y (s (5 : Fin (9 : ℕ))) && y (s (7 : Fin (9 : ℕ))) || y (s (6 : Fin (9 : ℕ))) && y (s (8 : Fin (9 : ℕ))) || y (s (8 : Fin (9 : ℕ))) && y (s (5 : Fin (9 : ℕ))))
    rw [fe_inv y]
    exact hy
  intro x1 hlen _ h15 x5 hf hs
  obtain ⟨a, b, rfl⟩ : ∃ a b, x1 = [a, b] := List.length_eq_two.mp hlen
  · have ha : a = 1 ∨ a = 5 := h15 a (by simp)
    have hb : b = 1 ∨ b = 5 := h15 b (by simp)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact h11 [1, 1] rfl x5 hf hs
    · exact hA [1, 5] rfl x5 hf hs
    · exact key 5 1 x5 (hA [p 5, p 1] rfl (rc x5) (fan_rc _ hf) (by rw [size_rc]; exact hs))
    · exact key 5 5 x5 (h11 [p 5, p 5] rfl (rc x5) (fan_rc _ hf) (by rw [size_rc]; exact hs))
