import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3748

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core

def C0 : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [7, 11] }, { op := GateOp.or, inputs := [14, 13] }, { op := GateOp.and, inputs := [0, 15] }, { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.or, inputs := [17, 12] }, { op := GateOp.and, inputs := [1, 18] }, { op := GateOp.or, inputs := [16, 19] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [21, 13] }, { op := GateOp.and, inputs := [2, 22] }, { op := GateOp.or, inputs := [20, 23] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [25, 10] }, { op := GateOp.and, inputs := [3, 26] }, { op := GateOp.or, inputs := [24, 27] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [29, 11] }, { op := GateOp.and, inputs := [4, 30] }, { op := GateOp.or, inputs := [28, 31] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [33, 12] }, { op := GateOp.and, inputs := [5, 34] }, { op := GateOp.or, inputs := [32, 35] }, { op := GateOp.or, inputs := [10, 12] }, { op := GateOp.or, inputs := [37, 13] }, { op := GateOp.and, inputs := [6, 38] }, { op := GateOp.or, inputs := [36, 39] }, { op := GateOp.and, inputs := [2, 4] }, { op := GateOp.and, inputs := [41, 5] }, { op := GateOp.and, inputs := [42, 6] }, { op := GateOp.and, inputs := [0, 3] }, { op := GateOp.and, inputs := [44, 5] }, { op := GateOp.and, inputs := [45, 6] }, { op := GateOp.or, inputs := [43, 46] }, { op := GateOp.and, inputs := [0, 1] }, { op := GateOp.and, inputs := [48, 4] }, { op := GateOp.and, inputs := [49, 6] }, { op := GateOp.or, inputs := [47, 50] }, { op := GateOp.and, inputs := [0, 1] }, { op := GateOp.and, inputs := [52, 2] }, { op := GateOp.and, inputs := [53, 5] }, { op := GateOp.or, inputs := [51, 54] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.and, inputs := [56, 3] }, { op := GateOp.and, inputs := [57, 6] }, { op := GateOp.or, inputs := [55, 58] }, { op := GateOp.and, inputs := [0, 2] }, { op := GateOp.and, inputs := [60, 3] }, { op := GateOp.and, inputs := [61, 4] }, { op := GateOp.or, inputs := [59, 62] }, { op := GateOp.and, inputs := [1, 3] }, { op := GateOp.and, inputs := [64, 4] }, { op := GateOp.and, inputs := [65, 5] }, { op := GateOp.or, inputs := [63, 66] }, { op := GateOp.or, inputs := [67, 0] }, { op := GateOp.or, inputs := [68, 1] }, { op := GateOp.or, inputs := [69, 3] }, { op := GateOp.and, inputs := [7, 70] }, { op := GateOp.or, inputs := [67, 1] }, { op := GateOp.or, inputs := [72, 2] }, { op := GateOp.or, inputs := [73, 4] }, { op := GateOp.and, inputs := [8, 74] }, { op := GateOp.or, inputs := [71, 75] }, { op := GateOp.or, inputs := [67, 2] }, { op := GateOp.or, inputs := [77, 3] }, { op := GateOp.or, inputs := [78, 5] }, { op := GateOp.and, inputs := [9, 79] }, { op := GateOp.or, inputs := [76, 80] }, { op := GateOp.or, inputs := [67, 3] }, { op := GateOp.or, inputs := [82, 4] }, { op := GateOp.or, inputs := [83, 6] }, { op := GateOp.and, inputs := [10, 84] }, { op := GateOp.or, inputs := [81, 85] }, { op := GateOp.or, inputs := [67, 0] }, { op := GateOp.or, inputs := [87, 4] }, { op := GateOp.or, inputs := [88, 5] }, { op := GateOp.and, inputs := [11, 89] }, { op := GateOp.or, inputs := [86, 90] }, { op := GateOp.or, inputs := [67, 1] }, { op := GateOp.or, inputs := [92, 5] }, { op := GateOp.or, inputs := [93, 6] }, { op := GateOp.and, inputs := [12, 94] }, { op := GateOp.or, inputs := [91, 95] }, { op := GateOp.or, inputs := [67, 0] }, { op := GateOp.or, inputs := [97, 2] }, { op := GateOp.or, inputs := [98, 6] }, { op := GateOp.and, inputs := [13, 99] }, { op := GateOp.or, inputs := [96, 100] }, { op := GateOp.and, inputs := [40, 101] }], output := 102 }

def edges : List (Fin 14 × Fin 14) :=
  [(0, 7), (0, 11), (0, 13), (1, 7), (1, 8), (1, 12), (2, 8), (2, 9), (2, 13), (3, 7), (3, 9), (3, 10), (4, 8), (4, 10), (4, 11), (5, 9), (5, 11), (5, 12), (6, 10), (6, 12), (6, 13)]

def fFano (x : Fin 14 → Bool) : Bool :=
  (x 0 && (x 7 || x 11 || x 13)) ||
  (x 1 && (x 7 || x 8 || x 12)) ||
  (x 2 && (x 8 || x 9 || x 13)) ||
  (x 3 && (x 7 || x 9 || x 10)) ||
  (x 4 && (x 8 || x 10 || x 11)) ||
  (x 5 && (x 9 || x 11 || x 12)) ||
  (x 6 && (x 10 || x 12 || x 13))

def gFano (x : Fin 14 → Bool) (b : Bool) : Bool :=
  (x 7 && (b || x 0 || x 1 || x 3)) ||
  (x 8 && (b || x 1 || x 2 || x 4)) ||
  (x 9 && (b || x 2 || x 3 || x 5)) ||
  (x 10 && (b || x 3 || x 4 || x 6)) ||
  (x 11 && (b || x 0 || x 4 || x 5)) ||
  (x 12 && (b || x 1 || x 5 || x 6)) ||
  (x 13 && (b || x 0 || x 2 || x 6))

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wireStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma foldl_wireStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wireStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (wireStep w g) (by simp only [wireStep, List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [wireStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def wval (x : Fin 14 → Bool) (i : ℕ) : Bool :=
  (C0.wires (List.ofFn x)).getD i false

lemma in_at (x : Fin 14 → Bool) (i : Fin 14) (k : ℕ) (hk : k = i.val := by rfl) :
    wval x k = x i := by
  subst hk
  unfold wval Circuit.wires
  change (C0.gates.foldl wireStep (List.ofFn x)).getD i.val false = x i
  have hi : i.val < (List.ofFn x).length := by simp
  rw [foldl_wireStep_getD_lt C0.gates (List.ofFn x) i.val hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_ofFn]

lemma wires_getD_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hb : ∀ i ∈ C.gates[j].inputs, i < x.length + j) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => (C.wires x).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.getElem_cons_drop hj, List.take_append_drop]
  set w0 := (C.gates.take j).foldl wireStep x
  have hw0 : w0.length = x.length + j := by
    rw [foldl_wireStep_length, List.length_take_of_le (Nat.le_of_lt hj)]
  have hwires : C.wires x = (C.gates.drop (j + 1)).foldl wireStep (wireStep w0 C.gates[j]) := by
    unfold Circuit.wires
    change C.gates.foldl wireStep x = _
    conv_lhs => rw [hsplit]
    simp only [List.foldl_append, List.foldl_cons, w0]
  have hlt : ∀ i < x.length + j, (C.wires x).getD i false = w0.getD i false := by
    intro i hi
    rw [hwires]
    have hi1 : i < (wireStep w0 C.gates[j]).length := by
      simp only [wireStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [foldl_wireStep_getD_lt _ _ i hi1]
    simp only [wireStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < w0.length)]
  conv_lhs => rw [hwires]
  have hlen : x.length + j < (wireStep w0 C.gates[j]).length := by
    simp only [wireStep, List.length_append, List.length_cons, List.length_nil]
    omega
  rw [foldl_wireStep_getD_lt _ _ (x.length + j) hlen]
  simp only [wireStep, List.getD_eq_getElem?_getD, ← hw0, List.getElem?_append_right (le_refl _),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro i hi
  have h1 := hlt i (hb i hi)
  simp only [List.getD_eq_getElem?_getD] at h1
  exact h1.symm

lemma or_at (x : Fin 14 → Bool) (w a b : ℕ)
    (hg : C0.gates[w - 14]? = some { op := GateOp.or, inputs := [a, b] } := by rfl)
    (h : 14 ≤ w ∧ w - 14 < C0.gates.length ∧ a < w ∧ b < w := by decide) :
    wval x w = (wval x a || wval x b) := by
  rcases h with ⟨h14, hj, ha, hb⟩
  have hg' : C0.gates[w - 14] = { op := GateOp.or, inputs := [a, b] } := by
    have := List.getElem?_eq_getElem hj
    rw [this] at hg
    exact Option.some.inj hg
  have hw : (List.ofFn x).length + (w - 14) = w := by simp; omega
  have h1 := wires_getD_gate C0 (List.ofFn x) (w - 14) hj (by
    rw [hg']
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega)
  rw [hw, hg'] at h1
  simpa [wval, GateOp.eval] using h1

lemma and_at (x : Fin 14 → Bool) (w a b : ℕ)
    (hg : C0.gates[w - 14]? = some { op := GateOp.and, inputs := [a, b] } := by rfl)
    (h : 14 ≤ w ∧ w - 14 < C0.gates.length ∧ a < w ∧ b < w := by decide) :
    wval x w = (wval x a && wval x b) := by
  rcases h with ⟨h14, hj, ha, hb⟩
  have hg' : C0.gates[w - 14] = { op := GateOp.and, inputs := [a, b] } := by
    have := List.getElem?_eq_getElem hj
    rw [this] at hg
    exact Option.some.inj hg
  have hw : (List.ofFn x).length + (w - 14) = w := by simp; omega
  have h1 := wires_getD_gate C0 (List.ofFn x) (w - 14) hj (by
    rw [hg']
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega)
  rw [hw, hg'] at h1
  simpa [wval, GateOp.eval] using h1

lemma w40_eq (x : Fin 14 → Bool) : wval x 40 = fFano x := by
  rw [or_at x 40 36 39, or_at x 36 32 35, or_at x 32 28 31, or_at x 28 24 27,
      or_at x 24 20 23, or_at x 20 16 19,
      and_at x 16 0 15, or_at x 15 14 13, or_at x 14 7 11,
      and_at x 19 1 18, or_at x 18 17 12, or_at x 17 7 8,
      and_at x 23 2 22, or_at x 22 21 13, or_at x 21 8 9,
      and_at x 27 3 26, or_at x 26 25 10, or_at x 25 7 9,
      and_at x 31 4 30, or_at x 30 29 11, or_at x 29 8 10,
      and_at x 35 5 34, or_at x 34 33 12, or_at x 33 9 11,
      and_at x 39 6 38, or_at x 38 37 13, or_at x 37 10 12]
  rw [in_at x 0 0, in_at x 1 1, in_at x 2 2, in_at x 3 3, in_at x 4 4, in_at x 5 5, in_at x 6 6,
      in_at x 7 7, in_at x 8 8, in_at x 9 9, in_at x 10 10, in_at x 11 11, in_at x 12 12, in_at x 13 13]
  rfl

lemma w101_eq (x : Fin 14 → Bool) : wval x 101 = gFano x (wval x 67) := by
  rw [or_at x 101 96 100, or_at x 96 91 95, or_at x 91 86 90, or_at x 86 81 85,
      or_at x 81 76 80, or_at x 76 71 75,
      and_at x 71 7 70, or_at x 70 69 3, or_at x 69 68 1, or_at x 68 67 0,
      and_at x 75 8 74, or_at x 74 73 4, or_at x 73 72 2, or_at x 72 67 1,
      and_at x 80 9 79, or_at x 79 78 5, or_at x 78 77 3, or_at x 77 67 2,
      and_at x 85 10 84, or_at x 84 83 6, or_at x 83 82 4, or_at x 82 67 3,
      and_at x 90 11 89, or_at x 89 88 5, or_at x 88 87 4, or_at x 87 67 0,
      and_at x 95 12 94, or_at x 94 93 6, or_at x 93 92 5, or_at x 92 67 1,
      and_at x 100 13 99, or_at x 99 98 6, or_at x 98 97 2, or_at x 97 67 0]
  rw [in_at x 0 0, in_at x 1 1, in_at x 2 2, in_at x 3 3, in_at x 4 4, in_at x 5 5, in_at x 6 6,
      in_at x 7 7, in_at x 8 8, in_at x 9 9, in_at x 10 10, in_at x 11 11, in_at x 12 12, in_at x 13 13]
  rfl

lemma fFano_imp_gFano (x : Fin 14 → Bool) (b : Bool) (h : fFano x = true) :
    gFano x b = true := by
  simp only [fFano, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ((((((⟨hp, hl⟩ | ⟨hp, hl⟩) | ⟨hp, hl⟩) | ⟨hp, hl⟩) | ⟨hp, hl⟩) | ⟨hp, hl⟩) | ⟨hp, hl⟩)
  · rcases hl with (hl | hl) | hl <;> simp [gFano, hp, hl]
  · rcases hl with (hl | hl) | hl <;> simp [gFano, hp, hl]
  · rcases hl with (hl | hl) | hl <;> simp [gFano, hp, hl]
  · rcases hl with (hl | hl) | hl <;> simp [gFano, hp, hl]
  · rcases hl with (hl | hl) | hl <;> simp [gFano, hp, hl]
  · rcases hl with (hl | hl) | hl <;> simp [gFano, hp, hl]
  · rcases hl with (hl | hl) | hl <;> simp [gFano, hp, hl]

lemma fFano_eq_edges (x : Fin 14 → Bool) :
    fFano x = decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro h
    simp only [fFano, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((((((⟨hp, hl⟩ | ⟨hp, hl⟩) | ⟨hp, hl⟩) | ⟨hp, hl⟩) | ⟨hp, hl⟩) | ⟨hp, hl⟩) | ⟨hp, hl⟩)
    · rcases hl with (hl | hl) | hl
      · exact ⟨(0, 7), by simp [edges], hp, hl⟩
      · exact ⟨(0, 11), by simp [edges], hp, hl⟩
      · exact ⟨(0, 13), by simp [edges], hp, hl⟩
    · rcases hl with (hl | hl) | hl
      · exact ⟨(1, 7), by simp [edges], hp, hl⟩
      · exact ⟨(1, 8), by simp [edges], hp, hl⟩
      · exact ⟨(1, 12), by simp [edges], hp, hl⟩
    · rcases hl with (hl | hl) | hl
      · exact ⟨(2, 8), by simp [edges], hp, hl⟩
      · exact ⟨(2, 9), by simp [edges], hp, hl⟩
      · exact ⟨(2, 13), by simp [edges], hp, hl⟩
    · rcases hl with (hl | hl) | hl
      · exact ⟨(3, 7), by simp [edges], hp, hl⟩
      · exact ⟨(3, 9), by simp [edges], hp, hl⟩
      · exact ⟨(3, 10), by simp [edges], hp, hl⟩
    · rcases hl with (hl | hl) | hl
      · exact ⟨(4, 8), by simp [edges], hp, hl⟩
      · exact ⟨(4, 10), by simp [edges], hp, hl⟩
      · exact ⟨(4, 11), by simp [edges], hp, hl⟩
    · rcases hl with (hl | hl) | hl
      · exact ⟨(5, 9), by simp [edges], hp, hl⟩
      · exact ⟨(5, 11), by simp [edges], hp, hl⟩
      · exact ⟨(5, 12), by simp [edges], hp, hl⟩
    · rcases hl with (hl | hl) | hl
      · exact ⟨(6, 10), by simp [edges], hp, hl⟩
      · exact ⟨(6, 12), by simp [edges], hp, hl⟩
      · exact ⟨(6, 13), by simp [edges], hp, hl⟩
  · rintro ⟨e, he, h1, h2⟩
    simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [fFano, h1, h2]

lemma circuitFun_eq (x : Fin 14 → Bool) :
    circuitFun 14 C0 x = decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true) := by
  change wval x 102 = _
  rw [and_at x 102 40 101, w40_eq, w101_eq, ← fFano_eq_edges]
  cases h : fFano x
  · rfl
  · simp [fFano_imp_gFano x (wval x 67) h]

def isLineOr (w : ℕ) : Bool :=
  w == 14 || w == 15 || w == 17 || w == 18 || w == 21 || w == 22 || w == 25 ||
  w == 26 || w == 29 || w == 30 || w == 33 || w == 34 || w == 37 || w == 38

def isHighEdge (w : ℕ) : Bool :=
  w == 71 || w == 75 || w == 76 || w == 80 || w == 81 || w == 85 || w == 86 ||
  w == 90 || w == 91 || w == 95 || w == 96 || w == 100 || w == 101

def lbOf (w : ℕ) : ℕ × ℕ :=
  if w < 7 then (1, 0)
  else if w < 14 then (0, 1)
  else if isLineOr w then (0, 1)
  else if w ≤ 40 then (1, 1)
  else if w ≤ 67 then (1, 0)
  else if isHighEdge w then (1, 1)
  else if w ≤ 101 then (1, 0)
  else (2, 2)

def checkLb (lb : ℕ → ℕ × ℕ) : ℕ → List Gate → Bool
  | _, [] => true
  | w, g :: gs =>
    (match g.op, g.inputs with
      | GateOp.or, [i, j] =>
        decide ((lb w).1 ≤ min (lb i).1 (lb j).1 ∧ (lb w).2 ≤ min (lb i).2 (lb j).2)
      | GateOp.and, [i, j] =>
        decide ((lb w).1 ≤ min ((lb i).1 + (lb j).1) 2 ∧ (lb w).2 ≤ min ((lb i).2 + (lb j).2) 2)
      | _, _ => false) && checkLb lb (w + 1) gs

lemma mem_foldl_insertNew {A acc : List (List ℕ)} {v : List ℕ}
    (hv : v ∈ A.foldl insertNew acc) : v ∈ acc ∨ v ∈ A := by
  induction A generalizing acc with
  | nil => left; exact hv
  | cons a as ih =>
    simp only [List.foldl_cons] at hv
    rcases ih hv with h | h
    · unfold insertNew at h
      split_ifs at h
      · left; exact h
      · simp only [List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · left; exact h
        · right; exact List.mem_cons_self
    · right; exact List.mem_cons_of_mem _ h

lemma mem_andStep {k : ℕ} {A B : List (List ℕ)} {w : List ℕ}
    (hw : w ∈ andStep k A B) : ∃ u ∈ A, ∃ v ∈ B, w = capAdd k u v := by
  unfold andStep at hw
  rcases mem_foldl_insertNew hw with h | h
  · cases h
  · simpa [List.mem_flatMap, List.mem_map, eq_comm] using h

def rvStep (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  let ins := g.inputs.map fun i => R.getD i []
  R ++ [match g.op with
    | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => ins.foldl (andStep 1) [S.map fun _ => 0]
    | _ => []]

lemma foldl_rv_lbOf (p l : ℕ) (lb : ℕ → ℕ × ℕ) (gs : List Gate) (R : List (List (List ℕ)))
    (hchk : checkLb lb R.length gs = true)
    (hinv : ∀ w : ℕ, ∀ v ∈ R.getD w [],
      v.length = 2 ∧ (lb w).1 ≤ v.getD 0 0 ∧ (lb w).2 ≤ v.getD 1 0) :
    ∀ w : ℕ, ∀ v ∈ (gs.foldl (rvStep [p, l]) R).getD w [],
      v.length = 2 ∧ (lb w).1 ≤ v.getD 0 0 ∧ (lb w).2 ≤ v.getD 1 0 := by
  induction gs generalizing R with
  | nil => exact hinv
  | cons g gs ih =>
    simp only [List.foldl_cons]
    simp only [checkLb, Bool.and_eq_true] at hchk
    rcases hchk with ⟨hg, hgs⟩
    have hlen : (rvStep [p, l] R g).length = R.length + 1 := by
      simp only [rvStep, List.length_append, List.length_cons, List.length_nil]
    apply ih (rvStep [p, l] R g) (by rw [hlen]; exact hgs)
    intro w v hv
    by_cases hw : w < R.length
    · simp only [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hw] at hv
      exact hinv w v hv
    · by_cases hweq : w = R.length
      · subst hweq
        simp only [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hv
        match hop : g.op, hgi : g.inputs with
        | GateOp.or, [i, j] =>
          rw [hop, hgi] at hg hv
          simp only [decide_eq_true_eq] at hg
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hv
          rcases mem_foldl_insertNew hv with h1 | h2
          · rcases mem_foldl_insertNew h1 with h0 | h1'
            · cases h0
            · have hi1 := hinv i v h1'
              exact ⟨hi1.1, by omega, by omega⟩
          · have hj2 := hinv j v h2
            exact ⟨hj2.1, by omega, by omega⟩
        | GateOp.and, [i, j] =>
          rw [hop, hgi] at hg hv
          simp only [decide_eq_true_eq] at hg
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hv
          rcases mem_andStep hv with ⟨w1, hw1, v2, hv2, rfl⟩
          rcases mem_andStep hw1 with ⟨v0, hv0, v1, hv1, rfl⟩
          simp only [List.mem_singleton] at hv0
          subst hv0
          have hi1 := hinv i v1 hv1
          have hj2 := hinv j v2 hv2
          match v1, hi1 with
          | [x1, y1], ⟨_, hx1, hy1⟩ =>
            match v2, hj2 with
            | [x2, y2], ⟨_, hx2, hy2⟩ =>
              simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil,
                List.length_cons, List.length_nil, List.getD_eq_getElem?_getD,
                List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hx1 hy1 hx2 hy2 ⊢
              refine ⟨trivial, ?_, ?_⟩ <;> omega
        | GateOp.or, [] => rw [hop, hgi] at hg; cases hg
        | GateOp.or, [_] => rw [hop, hgi] at hg; cases hg
        | GateOp.or, _ :: _ :: _ :: _ => rw [hop, hgi] at hg; cases hg
        | GateOp.and, [] => rw [hop, hgi] at hg; cases hg
        | GateOp.and, [_] => rw [hop, hgi] at hg; cases hg
        | GateOp.and, _ :: _ :: _ :: _ => rw [hop, hgi] at hg; cases hg
        | GateOp.not, _ => rw [hop, hgi] at hg; cases hg
        | GateOp.mod _, _ => rw [hop, hgi] at hg; cases hg
        | GateOp.maj, _ => rw [hop, hgi] at hg; cases hg
      · have hgt : (rvStep [p, l] R g).length ≤ w := by omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hgt, Option.getD_none,
          List.not_mem_nil] at hv

lemma checkLb_C0 : checkLb lbOf 14 C0.gates = true := by
  decide

lemma isAO2_C0 : IsAO2 14 C0 := by
  decide

lemma readTwice_of_split (p l : Fin 14) (hp : p.val < 7) (hl : 7 ≤ l.val) :
    ReadTwiceAt 14 C0 88 p l := by
  unfold ReadTwiceAt readsAtMost atGate
  simp only [List.any_eq_false]
  intro v hv
  have hbase : ∀ w : ℕ, ∀ u ∈ ((List.range 14).map (leafVectors [p.val, l.val] 1)).getD w [],
      u.length = 2 ∧ (lbOf w).1 ≤ u.getD 0 0 ∧ (lbOf w).2 ≤ u.getD 1 0 := by
    intro w u hu
    by_cases hw : w < 14
    · have hu' : u ∈ leafVectors [p.val, l.val] 1 w := by
        simpa [List.getD_eq_getElem?_getD, hw] using hu
      unfold leafVectors at hu'
      split_ifs at hu' with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton] at hu'
        subst hu'
        rcases hmem with rfl | rfl
        · have hne : l.val ≠ p.val := by omega
          have hlb : lbOf p.val = (1, 0) := by simp [lbOf, hp]
          rw [hlb]
          simp [hne]
        · have hne : p.val ≠ l.val := by omega
          have hlb : lbOf l.val = (0, 1) := by
            have h1 : ¬ l.val < 7 := by omega
            have h2 : l.val < 14 := l.isLt
            simp [lbOf, h1, h2]
          rw [hlb]
          simp [hne]
      · cases hu'
    · have hge : ((List.range 14).map (leafVectors [p.val, l.val] 1)).length ≤ w := by
        simp; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none,
        List.not_mem_nil] at hu
  have hlen0 : ((List.range 14).map (leafVectors [p.val, l.val] 1)).length = 14 := by simp
  have hinv := foldl_rv_lbOf p.val l.val lbOf C0.gates
    ((List.range 14).map (leafVectors [p.val, l.val] 1)) (by rw [hlen0]; exact checkLb_C0) hbase 102 v
  have hrv : readVectors { C0 with output := 14 + 88 } 14 [p.val, l.val] 1 =
      C0.gates.foldl (rvStep [p.val, l.val]) ((List.range 14).map (leafVectors [p.val, l.val] 1)) := rfl
  rw [hrv] at hv
  have h102 := hinv hv
  have hmc : lbOf 102 = (2, 2) := rfl
  rw [hmc] at h102
  match v, h102 with
  | [x0, x1], ⟨_, hx0, _⟩ =>
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some] at hx0
    have h0 : decide (x0 ≤ 1) = false := decide_eq_false (by omega)
    simp [h0]

lemma edges_split : ∀ e ∈ edges, e.1.val < 7 ∧ 7 ≤ e.2.val := by
  intro e he
  simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide⟩

end PEqualNP.Outside.L_meta_3748

theorem PEqualNP.Outside.L_meta_3748 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [41, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [48, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [49, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 50] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [52, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [56, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [57, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [60, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [61, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 62] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [64, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [65, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [63, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [69, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [72, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [73, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 74] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 75] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [76, 80] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [82, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [81, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [87, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 89] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [93, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 95] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [97, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [96, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 101] }], output := 102 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 89 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 11), (0, 13), (1, 7), (1, 8), (1, 12), (2, 8), (2, 9), (2, 13), (3, 7), (3, 9), (3, 10), (4, 8), (4, 10), (4, 11), (5, 9), (5, 11), (5, 12), (6, 10), (6, 12), (6, 13)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 11), (0, 13), (1, 7), (1, 8), (1, 12), (2, 8), (2, 9), (2, 13), (3, 7), (3, 9), (3, 10), (4, 8), (4, 10), (4, 11), (5, 9), (5, 11), (5, 12), (6, 10), (6, 12), (6, 13)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 11), (0, 13), (1, 7), (1, 8), (1, 12), (2, 8), (2, 9), (2, 13), (3, 7), (3, 9), (3, 10), (4, 8), (4, 10), (4, 11), (5, 9), (5, 11), (5, 12), (6, 10), (6, 12), (6, 13)] : List (Fin 14 × Fin 14))) := by
  intro C rfl
  refine ⟨PEqualNP.Outside.L_meta_3748.isAO2_C0, rfl, PEqualNP.Outside.L_meta_3748.circuitFun_eq, ?_⟩
  intro e he
  have hsp := PEqualNP.Outside.L_meta_3748.edges_split e he
  exact ⟨fun _ => he, fun _ => PEqualNP.Outside.L_meta_3748.readTwice_of_split e.1 e.2 hsp.1 hsp.2⟩
