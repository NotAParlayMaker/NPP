import Mathlib
import PEqualNP.Defs

-- Symmetry cut for L-meta-3513. The map s = (1 5)(2 8)(6 7) is an automorphism of the graph
-- (Petersen minus a vertex) that fixes 0, 3 and 4, so it fixes both OR wires up to the choice
-- of x1. Relabelling the inputs of both circuits along s moves the case x1 = s k to the case
-- x1 = k at the same sizes, so the nine cases of x1 come down to 0, 4, 1, 2, 3 and 6.
theorem PEqualNP.Outside.R_meta_3513_1
    (h04 : ∀ (x1 : Fin (9 : ℕ)), (x1 = (0 : Fin (9 : ℕ)) ∨ x1 = (4 : Fin (9 : ℕ))) →
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       (∀ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x1]);           x3.eval (x7 ++ [!x7.getD x2.output Bool.false]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2) →         (13 : ℕ) ≤ x2.size + x3.size)
    (h12 : ∀ (x1 : Fin (9 : ℕ)), (x1 = (1 : Fin (9 : ℕ)) ∨ x1 = (2 : Fin (9 : ℕ))) →
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       (∀ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x1]);           x3.eval (x7 ++ [!x7.getD x2.output Bool.false]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2) →         (13 : ℕ) ≤ x2.size + x3.size)
    (h36 : ∀ (x1 : Fin (9 : ℕ)), (x1 = (3 : Fin (9 : ℕ)) ∨ x1 = (6 : Fin (9 : ℕ))) →
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       (∀ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x1]);           x3.eval (x7 ++ [!x7.getD x2.output Bool.false]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2) →         (13 : ℕ) ≤ x2.size + x3.size) :
    ∀ (x1 : Fin (9 : ℕ)) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       (∀ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x1]);           x3.eval (x7 ++ [!x7.getD x2.output Bool.false]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2) →         (13 : ℕ) ≤ x2.size + x3.size := by
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
  have edges_inv : ∀ y : Fin 9 → Bool,
      ([((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => y (s x8.1) && y (s x8.2)) =
      ([((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => y x8.1 && y x8.2) := by
    intro y
    simp only [List.any_cons, List.any_nil, s, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    simp only [Matrix.cons_val]
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
  -- the 11 input wires, relabelled along p
  have inputs_ok : ∀ (y : Fin 9 → Bool) (k : Fin 9),
      9 ≤ (List.ofFn (fun i => y (s i)) ++ [y (s 0) || y (s 4), y (s 0) || y (s 4) || y k]).length ∧
      (List.ofFn y ++ [y 0 || y 4, y 0 || y 4 || y k]).length =
        (List.ofFn (fun i => y (s i)) ++ [y (s 0) || y (s 4), y (s 0) || y (s 4) || y k]).length ∧
      ∀ i, (List.ofFn y ++ [y 0 || y 4, y 0 || y 4 || y k]).getD (p i) false =
        (List.ofFn (fun i => y (s i)) ++ [y (s 0) || y (s 4), y (s 0) || y (s 4) || y k]).getD i false := by
    intro y k
    refine ⟨by simp, by simp, ?_⟩
    intro i
    by_cases hi : i < 9
    · have hpi := hp_lt i hi
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simpa using hpi), List.getElem?_append_left (by simpa using hi),
        List.getElem?_ofFn, List.getElem?_ofFn]
      simp [p, hi, hpi]
    · rw [hp_fix i (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp [s0, s4]
  intro x1 x2 x3 hm hf he
  -- the transport: from the case s k to the case k, at the same sizes
  have transport : ∀ k : Fin 9,
      (∀ (x6 : Fin (9 : ℕ) → Bool),
        have x7 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 (s k)]);
        x3.eval (x7 ++ [!x7.getD x2.output Bool.false]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2) →
      (∀ (x6 : Fin (9 : ℕ) → Bool),
        have x7 : List Bool := (rc x2).wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 k]);
        (rc x3).eval (x7 ++ [!x7.getD (rc x2).output Bool.false]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2) := by
    intro k hk y
    obtain ⟨h9, hl, hget⟩ := inputs_ok y k
    have hz := hk (fun i => y (s i))
    beta_reduce at hz
    rw [ss k, edges_inv y] at hz
    rw [← hz]
    obtain ⟨h9W, hl2, hw2⟩ := wires_rc x2 _ _ h9 hl hget
    have hL : ∀ i, ((rc x2).wires (List.ofFn y ++ [y 0 || y 4, y 0 || y 4 || y k]) ++
          [!((rc x2).wires (List.ofFn y ++ [y 0 || y 4, y 0 || y 4 || y k])).getD (p x2.output) false]).getD (p i) false =
        (x2.wires (List.ofFn (fun i => y (s i)) ++ [y (s 0) || y (s 4), y (s 0) || y (s 4) || y k]) ++
          [!(x2.wires (List.ofFn (fun i => y (s i)) ++ [y (s 0) || y (s 4), y (s 0) || y (s 4) || y k])).getD x2.output false]).getD i false := by
      intro i
      rw [gapp, gapp, hl2, hw2 x2.output]
      by_cases hi : i < (x2.wires (List.ofFn (fun i => y (s i)) ++ [y (s 0) || y (s 4), y (s 0) || y (s 4) || y k])).length
      · rw [if_pos ((hp_iff i _ h9W).2 hi), if_pos hi]
        exact hw2 i
      · rw [if_neg (fun h' => hi ((hp_iff i _ h9W).1 h')), if_neg hi, hp_fix i (by omega)]
    obtain ⟨_, _, h3⟩ := wires_rc x3 _ _ (by simp only [List.length_append, List.length_singleton]; omega)
      (by simp only [List.length_append, List.length_singleton, hl2]) hL
    exact h3 x3.output
  fin_cases x1
  · exact h04 0 (Or.inl rfl) x2 x3 hm hf he
  · exact h12 1 (Or.inl rfl) x2 x3 hm hf he
  · exact h12 2 (Or.inr rfl) x2 x3 hm hf he
  · exact h36 3 (Or.inl rfl) x2 x3 hm hf he
  · exact h04 4 (Or.inr rfl) x2 x3 hm hf he
  · have h := h12 1 (Or.inl rfl) (rc x2) (rc x3) (mono_rc _ hm) (fan_rc _ hf) (transport 1 he)
    rwa [size_rc, size_rc] at h
  · exact h36 6 (Or.inr rfl) x2 x3 hm hf he
  · have h := h36 6 (Or.inr rfl) (rc x2) (rc x3) (mono_rc _ hm) (fan_rc _ hf) (transport 6 he)
    rwa [size_rc, size_rc] at h
  · have h := h12 2 (Or.inr rfl) (rc x2) (rc x3) (mono_rc _ hm) (fan_rc _ hf) (transport 2 he)
    rwa [size_rc, size_rc] at h
