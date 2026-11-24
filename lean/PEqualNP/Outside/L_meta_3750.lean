import PEqualNP.Defs

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace PEqualNP.Outside.L_meta_3750

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.Core

def C0 : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [38, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [54, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [58, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 59] }], output := 60 }

def edges : List (Fin 14 × Fin 14) :=
  [(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13),
    (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13),
    (6, 9), (6, 11), (6, 12)]

def reread : List (Fin 14 × Fin 14) :=
  [(0, 7), (0, 8), (1, 7), (1, 10), (2, 7), (3, 8), (3, 10), (4, 8), (5, 10)]

def ofBits (n : ℕ) : Fin 14 → Bool := fun i => Nat.testBit n i.val

def F (x : Fin 14 → Bool) : Bool :=
  decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true)

def evList (n : ℕ) : List Bool :=
  let w0 := Nat.testBit n 0
  let w1 := Nat.testBit n 1
  let w2 := Nat.testBit n 2
  let w3 := Nat.testBit n 3
  let w4 := Nat.testBit n 4
  let w5 := Nat.testBit n 5
  let w6 := Nat.testBit n 6
  let w7 := Nat.testBit n 7
  let w8 := Nat.testBit n 8
  let w9 := Nat.testBit n 9
  let w10 := Nat.testBit n 10
  let w11 := Nat.testBit n 11
  let w12 := Nat.testBit n 12
  let w13 := Nat.testBit n 13
  let w14 := w0 || w1
  let w15 := w14 || w3
  let w16 := w7 || w8
  let w17 := w16 || w10
  let w18 := w15 && w17
  let w19 := w7 || w10
  let w20 := w5 && w19
  let w21 := w18 || w20
  let w22 := w0 || w10
  let w23 := w1 || w5
  let w24 := w23 || w7
  let w25 := w22 && w24
  let w26 := w21 && w25
  let w27 := w7 || w8
  let w28 := w4 && w27
  let w29 := w18 || w28
  let w30 := w1 || w8
  let w31 := w0 || w3
  let w32 := w31 || w4
  let w33 := w30 && w32
  let w34 := w29 && w33
  let w35 := w26 || w34
  let w36 := w7 || w8
  let w37 := w2 && w36
  let w38 := w18 || w37
  let w39 := w3 || w7
  let w40 := w1 || w2
  let w41 := w40 || w10
  let w42 := w39 && w41
  let w43 := w38 && w42
  let w44 := w35 || w43
  let w45 := w0 || w5
  let w46 := w45 || w6
  let w47 := w46 && w9
  let w48 := w44 || w47
  let w49 := w1 || w4
  let w50 := w49 || w6
  let w51 := w50 && w11
  let w52 := w48 || w51
  let w53 := w2 || w3
  let w54 := w53 || w6
  let w55 := w54 && w12
  let w56 := w52 || w55
  let w57 := w2 || w4
  let w58 := w57 || w5
  let w59 := w58 && w13
  let w60 := w56 || w59
  [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60]

def ev (n : ℕ) : Bool := (evList n).getD 60 false

def Fbit (n : ℕ) : Bool :=
  edges.any fun e => Nat.testBit n e.1 && Nat.testBit n e.2

def checkFrom (start len : ℕ) : Bool :=
  (List.range len).all fun i => ev (start + i) == Fbit (start + i)

def toBits (x : Fin 14 → Bool) : ℕ :=
  Nat.bit (x 0) (Nat.bit (x 1) (Nat.bit (x 2) (Nat.bit (x 3) (Nat.bit (x 4) (Nat.bit (x 5) (Nat.bit (x 6) (Nat.bit (x 7) (Nat.bit (x 8) (Nat.bit (x 9) (Nat.bit (x 10) (Nat.bit (x 11) (Nat.bit (x 12) (Nat.bit (x 13) (0))))))))))))))

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ao : IsAO2 14 C0 ∧ C0.size = 47 := by decide +kernel

theorem evF_0 : checkFrom 0 4096 = true := by decide +kernel

theorem evF_1 : checkFrom 4096 4096 = true := by decide +kernel

theorem evF_2 : checkFrom 8192 4096 = true := by decide +kernel

theorem evF_3 : checkFrom 12288 4096 = true := by decide +kernel

theorem evF_all {n : ℕ} (hn : n < 16384) : ev n = Fbit n := by
  have hquot : n / 4096 < 4 := by omega
  have hchk : checkFrom (n / 4096 * 4096) 4096 = true := by
    interval_cases n / 4096
    · exact evF_0
    · exact evF_1
    · exact evF_2
    · exact evF_3
  have hi : n - n / 4096 * 4096 < 4096 := by omega
  have hmem : n - n / 4096 * 4096 ∈ List.range 4096 := List.mem_range.mpr hi
  have hb := List.all_eq_true.mp hchk _ hmem
  have heq : ev (n / 4096 * 4096 + (n - n / 4096 * 4096)) =
      Fbit (n / 4096 * 4096 + (n - n / 4096 * 4096)) := beq_iff_eq.mp hb
  convert heq <;> omega

theorem any_eq_exists (l : List (Fin 14 × Fin 14)) (p : Fin 14 × Fin 14 → Bool) :
    l.any p = decide (∃ e ∈ l, p e = true) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.any_cons]
    rw [ih]
    cases hp : p a
    · simp only [Bool.false_or]
      congr 1
      apply propext
      constructor
      · intro h
        rcases h with ⟨e, he, hpe⟩
        exact ⟨e, List.mem_cons_of_mem a he, hpe⟩
      · intro h
        rcases h with ⟨e, he, hpe⟩
        rcases List.mem_cons.mp he with h | h
        · subst e
          exact False.elim (Bool.false_ne_true (hp.symm.trans hpe))
        · exact ⟨e, h, hpe⟩
    · simp only [Bool.true_or]
      rw [eq_comm]
      exact decide_eq_true ⟨a, List.mem_cons_self, hp⟩

theorem Fbit_eq (n : ℕ) : Fbit n = F (ofBits n) := by
  unfold F Fbit ofBits
  have h := any_eq_exists edges (fun e => Nat.testBit n e.1 && Nat.testBit n e.2)
  refine h.trans ?_
  congr 1
  apply propext
  constructor
  · intro h
    rcases h with ⟨e, he, hp⟩
    exact ⟨e, he, (Bool.and_eq_true _ _).mp hp⟩
  · intro h
    rcases h with ⟨e, he, hp⟩
    exact ⟨e, he, (Bool.and_eq_true _ _).mpr hp⟩

theorem bit_lt {n k : ℕ} (b : Bool) (h : n < 2 ^ k) : Nat.bit b n < 2 ^ (k + 1) := by
  cases b <;> simp [Nat.bit] <;> omega

theorem toBits_lt (x : Fin 14 → Bool) : toBits x < 16384 := by
  unfold toBits
  have h13 : (0 : ℕ) < 2 ^ 0 := by decide
  have h12 := bit_lt (x 13) h13
  have h11 := bit_lt (x 12) h12
  have h10 := bit_lt (x 11) h11
  have h9 := bit_lt (x 10) h10
  have h8 := bit_lt (x 9) h9
  have h7 := bit_lt (x 8) h8
  have h6 := bit_lt (x 7) h7
  have h5 := bit_lt (x 6) h6
  have h4 := bit_lt (x 5) h5
  have h3 := bit_lt (x 4) h4
  have h2 := bit_lt (x 3) h3
  have h1 := bit_lt (x 2) h2
  have h0 := bit_lt (x 1) h1
  have h := bit_lt (x 0) h0
  simpa using h

theorem testBit_bit_zero' (b : Bool) (n : ℕ) : Nat.testBit (Nat.bit b n) 0 = b := by
  cases b
  · simp [Nat.bit, Nat.testBit_zero]
  · simp [Nat.bit, Nat.testBit_zero]

theorem testBit_bit_succ' (b : Bool) (n m : ℕ) :
    Nat.testBit (Nat.bit b n) (m + 1) = Nat.testBit n m := by
  cases b
  · change Nat.testBit (2 * n) (m + 1) = Nat.testBit n m
    rw [Nat.testBit_succ]
    have : (2 * n) / 2 = n := by omega
    rw [this]
  · change Nat.testBit (2 * n + 1) (m + 1) = Nat.testBit n m
    rw [Nat.testBit_succ]
    have : (2 * n + 1) / 2 = n := by omega
    rw [this]

theorem ofBits_toBits (x : Fin 14 → Bool) : ofBits (toBits x) = x := by
  funext i
  unfold ofBits toBits
  fin_cases i <;>
    repeat (first | rw [testBit_bit_zero'] | rw [testBit_bit_succ'] | rfl)

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW, List.length_append]
    omega

theorem foldl_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    (gs ++ [g]).foldl stepW w = stepW (gs.foldl stepW w) g := by
  simp [List.foldl_append, List.foldl_cons, List.foldl_nil]


theorem evList_len (n : ℕ) : (evList n).length = 61 := by simp [evList]

theorem ev_list (n : ℕ) : ev n = (evList n).getD 60 false := rfl

theorem evList_input (n i : ℕ) (hi : i < 14) :
    (evList n).getD i false = Nat.testBit n i := by
  interval_cases i <;> simp [evList]

theorem prefix0 (n : ℕ) :
    List.ofFn (ofBits n) = (evList n).take 14 := by
  apply List.ext_getElem
  · simp [evList, List.length_ofFn]
  · intro i h1 h2
    have hi : i < 14 := by simp [List.length_ofFn] at h1; exact h1
    have hlen : i < (evList n).length := by simp [evList]; omega
    rw [List.getElem_ofFn, List.getElem_take]
    have := evList_input n i hi
    rw [List.getD_eq_getElem (l := evList n) (n := i) false hlen] at this
    simp [ofBits]
    exact this.symm


theorem evg0 (n : ℕ) :
    (evList n).getD 14 false =
      GateOp.or.eval ([0, 1].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg1 (n : ℕ) :
    (evList n).getD 15 false =
      GateOp.or.eval ([14, 3].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg2 (n : ℕ) :
    (evList n).getD 16 false =
      GateOp.or.eval ([7, 8].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg3 (n : ℕ) :
    (evList n).getD 17 false =
      GateOp.or.eval ([16, 10].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg4 (n : ℕ) :
    (evList n).getD 18 false =
      GateOp.and.eval ([15, 17].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg5 (n : ℕ) :
    (evList n).getD 19 false =
      GateOp.or.eval ([7, 10].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg6 (n : ℕ) :
    (evList n).getD 20 false =
      GateOp.and.eval ([5, 19].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg7 (n : ℕ) :
    (evList n).getD 21 false =
      GateOp.or.eval ([18, 20].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg8 (n : ℕ) :
    (evList n).getD 22 false =
      GateOp.or.eval ([0, 10].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg9 (n : ℕ) :
    (evList n).getD 23 false =
      GateOp.or.eval ([1, 5].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg10 (n : ℕ) :
    (evList n).getD 24 false =
      GateOp.or.eval ([23, 7].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg11 (n : ℕ) :
    (evList n).getD 25 false =
      GateOp.and.eval ([22, 24].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg12 (n : ℕ) :
    (evList n).getD 26 false =
      GateOp.and.eval ([21, 25].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg13 (n : ℕ) :
    (evList n).getD 27 false =
      GateOp.or.eval ([7, 8].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg14 (n : ℕ) :
    (evList n).getD 28 false =
      GateOp.and.eval ([4, 27].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg15 (n : ℕ) :
    (evList n).getD 29 false =
      GateOp.or.eval ([18, 28].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg16 (n : ℕ) :
    (evList n).getD 30 false =
      GateOp.or.eval ([1, 8].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg17 (n : ℕ) :
    (evList n).getD 31 false =
      GateOp.or.eval ([0, 3].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg18 (n : ℕ) :
    (evList n).getD 32 false =
      GateOp.or.eval ([31, 4].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg19 (n : ℕ) :
    (evList n).getD 33 false =
      GateOp.and.eval ([30, 32].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg20 (n : ℕ) :
    (evList n).getD 34 false =
      GateOp.and.eval ([29, 33].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg21 (n : ℕ) :
    (evList n).getD 35 false =
      GateOp.or.eval ([26, 34].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg22 (n : ℕ) :
    (evList n).getD 36 false =
      GateOp.or.eval ([7, 8].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg23 (n : ℕ) :
    (evList n).getD 37 false =
      GateOp.and.eval ([2, 36].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg24 (n : ℕ) :
    (evList n).getD 38 false =
      GateOp.or.eval ([18, 37].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg25 (n : ℕ) :
    (evList n).getD 39 false =
      GateOp.or.eval ([3, 7].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg26 (n : ℕ) :
    (evList n).getD 40 false =
      GateOp.or.eval ([1, 2].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg27 (n : ℕ) :
    (evList n).getD 41 false =
      GateOp.or.eval ([40, 10].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg28 (n : ℕ) :
    (evList n).getD 42 false =
      GateOp.and.eval ([39, 41].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg29 (n : ℕ) :
    (evList n).getD 43 false =
      GateOp.and.eval ([38, 42].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg30 (n : ℕ) :
    (evList n).getD 44 false =
      GateOp.or.eval ([35, 43].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg31 (n : ℕ) :
    (evList n).getD 45 false =
      GateOp.or.eval ([0, 5].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg32 (n : ℕ) :
    (evList n).getD 46 false =
      GateOp.or.eval ([45, 6].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg33 (n : ℕ) :
    (evList n).getD 47 false =
      GateOp.and.eval ([46, 9].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg34 (n : ℕ) :
    (evList n).getD 48 false =
      GateOp.or.eval ([44, 47].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg35 (n : ℕ) :
    (evList n).getD 49 false =
      GateOp.or.eval ([1, 4].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg36 (n : ℕ) :
    (evList n).getD 50 false =
      GateOp.or.eval ([49, 6].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg37 (n : ℕ) :
    (evList n).getD 51 false =
      GateOp.and.eval ([50, 11].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg38 (n : ℕ) :
    (evList n).getD 52 false =
      GateOp.or.eval ([48, 51].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg39 (n : ℕ) :
    (evList n).getD 53 false =
      GateOp.or.eval ([2, 3].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg40 (n : ℕ) :
    (evList n).getD 54 false =
      GateOp.or.eval ([53, 6].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg41 (n : ℕ) :
    (evList n).getD 55 false =
      GateOp.and.eval ([54, 12].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg42 (n : ℕ) :
    (evList n).getD 56 false =
      GateOp.or.eval ([52, 55].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg43 (n : ℕ) :
    (evList n).getD 57 false =
      GateOp.or.eval ([2, 4].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg44 (n : ℕ) :
    (evList n).getD 58 false =
      GateOp.or.eval ([57, 5].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg45 (n : ℕ) :
    (evList n).getD 59 false =
      GateOp.and.eval ([58, 13].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evg46 (n : ℕ) :
    (evList n).getD 60 false =
      GateOp.or.eval ([56, 59].map fun i => (evList n).getD i false) := by
  dsimp [evList, GateOp.eval]
  simp [List.getD_eq_getElem?_getD]


theorem evList_gate (n k : ℕ) (hk : k < 47) :
    let g := C0.gates[k]?.getD ⟨GateOp.or, []⟩
    (evList n).getD (14 + k) false =
      g.op.eval (g.inputs.map fun i => (evList n).getD i false) := by
  interval_cases k
  · simp [C0]; exact evg0 n
  · simp [C0]; exact evg1 n
  · simp [C0]; exact evg2 n
  · simp [C0]; exact evg3 n
  · simp [C0]; exact evg4 n
  · simp [C0]; exact evg5 n
  · simp [C0]; exact evg6 n
  · simp [C0]; exact evg7 n
  · simp [C0]; exact evg8 n
  · simp [C0]; exact evg9 n
  · simp [C0]; exact evg10 n
  · simp [C0]; exact evg11 n
  · simp [C0]; exact evg12 n
  · simp [C0]; exact evg13 n
  · simp [C0]; exact evg14 n
  · simp [C0]; exact evg15 n
  · simp [C0]; exact evg16 n
  · simp [C0]; exact evg17 n
  · simp [C0]; exact evg18 n
  · simp [C0]; exact evg19 n
  · simp [C0]; exact evg20 n
  · simp [C0]; exact evg21 n
  · simp [C0]; exact evg22 n
  · simp [C0]; exact evg23 n
  · simp [C0]; exact evg24 n
  · simp [C0]; exact evg25 n
  · simp [C0]; exact evg26 n
  · simp [C0]; exact evg27 n
  · simp [C0]; exact evg28 n
  · simp [C0]; exact evg29 n
  · simp [C0]; exact evg30 n
  · simp [C0]; exact evg31 n
  · simp [C0]; exact evg32 n
  · simp [C0]; exact evg33 n
  · simp [C0]; exact evg34 n
  · simp [C0]; exact evg35 n
  · simp [C0]; exact evg36 n
  · simp [C0]; exact evg37 n
  · simp [C0]; exact evg38 n
  · simp [C0]; exact evg39 n
  · simp [C0]; exact evg40 n
  · simp [C0]; exact evg41 n
  · simp [C0]; exact evg42 n
  · simp [C0]; exact evg43 n
  · simp [C0]; exact evg44 n
  · simp [C0]; exact evg45 n
  · simp [C0]; exact evg46 n


theorem input_lt (k j : ℕ) (hk : k < 47)
    (hj : j ∈ (C0.gates[k]?.getD ⟨GateOp.or, []⟩).inputs) : j < 14 + k := by
  interval_cases k <;> simp [C0] at hj <;> omega

theorem take_getD (n m i : ℕ) (hi : i < m) (hm : m ≤ 61) :
    ((evList n).take m).getD i false = (evList n).getD i false := by
  have hmlen : ((evList n).take m).length = m := by
    rw [List.length_take, evList_len, min_eq_left hm]
  have : i < ((evList n).take m).length := by omega
  have hlen : i < (evList n).length := by rw [evList_len]; omega
  rw [List.getD_eq_getElem (l := (evList n).take m) (n := i) false this]
  rw [List.getD_eq_getElem (l := evList n) (n := i) false hlen]
  exact List.getElem_take

theorem take_eq (n : ℕ) : ∀ k, k ≤ 47 →
    (C0.gates.take k).foldl stepW (List.ofFn (ofBits n)) = (evList n).take (14 + k) := by
  intro k
  induction k with
  | zero =>
    intro _
    simpa using prefix0 n
  | succ k ih =>
    intro hk
    have hklt : k < 47 := by omega
    have hlen47 : C0.gates.length = 47 := ao.2
    have hlenK : k < C0.gates.length := by rw [hlen47]; exact hklt
    have htake : C0.gates.take (k + 1) =
        C0.gates.take k ++ [C0.gates[k]?.getD ⟨GateOp.or, []⟩] := by
      rw [List.take_succ_eq_append_getElem hlenK]
      simp [List.getElem?_eq_getElem hlenK]
    rw [htake, foldl_snoc, ih (by omega)]
    unfold stepW
    apply List.ext_getElem
    · have hL : ((evList n).take (14 + k)).length = 14 + k := by
        rw [List.length_take, evList_len, min_eq_left (by omega)]
      have hR : ((evList n).take (14 + (k + 1))).length = 14 + (k + 1) := by
        rw [List.length_take, evList_len, min_eq_left (by omega)]
      simp [List.length_append, List.length_cons, List.length_nil, hL, hR]
      omega
    · intro i h1 h2
      by_cases hlt : i < 14 + k
      · have hleft : i < ((evList n).take (14 + k)).length := by
          rw [List.length_take, evList_len, min_eq_left (by omega)]; exact hlt
        rw [List.getElem_append_left hleft]
        rw [List.getElem_take, List.getElem_take]
      · have htk : ((evList n).take (14 + k)).length = 14 + k := by
          rw [List.length_take, evList_len, min_eq_left (by omega)]
        have hi' : i = 14 + k := by
          have : i < ((evList n).take (14 + k)).length + 1 := by
            simpa [List.length_append, List.length_cons, List.length_nil] using h1
          rw [htk] at this
          omega
        subst i
        have hge : ((evList n).take (14 + k)).length ≤ 14 + k := by rw [htk]
        rw [List.getElem_append_right hge]
        have hidx : 14 + k - ((evList n).take (14 + k)).length = 0 := by
          rw [htk]; omega
        simp [hidx]
        have hg := evList_gate n k hklt
        have hlen' : 14 + k < (evList n).length := by rw [evList_len]; omega
        have hr : (evList n)[14 + k] = (evList n).getD (14 + k) false :=
          (List.getD_eq_getElem (l := evList n) (n := 14 + k) false hlen').symm
        rw [hr, hg]
        congr 1
        apply List.map_congr_left
        intro j hj
        have hj' : j < 14 + k := input_lt k j hklt hj
        exact take_getD n (14 + k) j hj' (by omega)

theorem ev_eq (n : ℕ) : ev n = circuitFun 14 C0 (ofBits n) := by
  unfold circuitFun Circuit.eval
  have hw : C0.wires (List.ofFn (ofBits n)) =
      C0.gates.foldl stepW (List.ofFn (ofBits n)) := rfl
  have hlen : C0.gates.length = 47 := by
    have := ao.2
    simpa [Circuit.size] using this
  have htake : C0.gates.take 47 = C0.gates := List.take_of_length_le (by omega)
  rw [hw, ← htake, take_eq n 47 (by omega), ev_list n]
  have h61 : (evList n).take 61 = evList n :=
    List.take_of_length_le (by rw [evList_len])
  rw [h61]
  simp [C0]

theorem rr (e : Fin 14 × Fin 14) (he : e ∈ edges) :
    ReadTwiceAt 14 C0 (C0.output - 14) e.1 e.2 ↔ e ∈ reread := by
  fin_cases he <;> decide +kernel

theorem result : ∀ C : Circuit, C = C0 →
    IsAO2 14 C ∧ C.size = 47 ∧
    (∀ x : Fin 14 → Bool, circuitFun 14 C x = F x) ∧
    (∀ e ∈ edges, ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ reread) := by
  intro C hC
  subst C
  refine ⟨ao.1, ao.2, ?_, rr⟩
  intro x
  have hx : ofBits (toBits x) = x := ofBits_toBits x
  have hn : toBits x < 16384 := toBits_lt x
  calc
    circuitFun 14 C0 x = circuitFun 14 C0 (ofBits (toBits x)) := by rw [hx]
    _ = ev (toBits x) := (ev_eq (toBits x)).symm
    _ = Fbit (toBits x) := evF_all hn
    _ = F (ofBits (toBits x)) := Fbit_eq (toBits x)
    _ = F x := by rw [hx]

end PEqualNP.Outside.L_meta_3750

theorem PEqualNP.Outside.L_meta_3750 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [38, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [54, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [58, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 59] }], output := 60 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 47 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (2, 7), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14))) := by
  intro C hC
  exact PEqualNP.Outside.L_meta_3750.result C hC
