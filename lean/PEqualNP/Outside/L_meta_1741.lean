import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1741

open PEqualNP.CircuitLowerBounds

def enc : List Bool → ℕ
  | [] => 0
  | b :: t => Nat.bit b (enc t)

theorem enc_testBit (w : List Bool) (i : ℕ) : (enc w).testBit i = w.getD i false := by
  induction w generalizing i with
  | nil => simp [enc]
  | cons b t ih =>
    cases i with
    | zero => simp [enc]
    | succ i => simp [enc, Nat.testBit_bit_succ, ih]

def run : List Gate → ℕ → ℕ → ℕ
  | [], _, W => W
  | g :: gs, k, W =>
    run gs (k + 1) (W ||| (bif g.op.eval (g.inputs.map fun i => W.testBit i) then 2 ^ k else 0))

theorem getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = (w.getD i false || (b && decide (w.length = i))) := by
  rcases lt_trichotomy i w.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h.ne']
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · obtain ⟨d, rfl⟩ : ∃ d, i = w.length + (d + 1) := ⟨i - w.length - 1, by omega⟩
    simp [List.getD_eq_getElem?_getD]

theorem run_rep (gs : List Gate) (w : List Bool) (W : ℕ)
    (h : ∀ i, W.testBit i = w.getD i false) (i : ℕ) :
    (run gs w.length W).testBit i =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
  induction gs generalizing w W i with
  | nil => simpa [run] using h i
  | cons g gs ih =>
    have hv : (g.inputs.map fun i => W.testBit i) = (g.inputs.map fun i => w.getD i false) := by
      congr 1
      funext j
      exact h j
    have hrep : ∀ j, (W ||| (bif g.op.eval (g.inputs.map fun i => w.getD i false) then 2 ^ w.length
        else 0)).testBit j
        = (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD j false := by
      intro j
      rw [getD_snoc, Nat.testBit_lor, h j]
      cases g.op.eval (g.inputs.map fun i => w.getD i false) <;> simp [Nat.testBit_two_pow]
    have key := ih _ _ hrep i
    simp only [List.length_append, List.length_singleton] at key
    simp only [run, List.foldl_cons, hv]
    exact key

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (run C.gates x.length (enc x)).testBit C.output := by
  unfold Circuit.eval Circuit.wires
  exact (run_rep C.gates x (enc x) (enc_testBit x) C.output).symm

theorem wire_eq (C : Circuit) (x : List Bool) (i : ℕ) :
    (C.wires x).getD i false = (run C.gates x.length (enc x)).testBit i := by
  unfold Circuit.wires
  exact (run_rep C.gates x (enc x) (enc_testBit x) i).symm

theorem eval26 (G : List Gate) (o : ℕ) (x : List Bool) (hx : x.length = 26) :
    Circuit.eval ⟨G, o⟩ x = (run G 26 (enc x)).testBit o := by
  rw [eval_eq, hx]

def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem isAO_iff (o : GateOp) (h : isAO o = true) : o = GateOp.and ∨ o = GateOp.or := by
  cases o <;> simp [isAO] at h ⊢

theorem ao2_of (gs : List Gate)
    (h : gs.all (fun g => isAO g.op && decide (g.inputs.length = 2)) = true) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  rw [Bool.and_eq_true] at h1
  exact ⟨isAO_iff _ h1.1, of_decide_eq_true h1.2⟩

def nl (u l : Fin 13) : Bool :=
  !(decide (u - l = 0) || decide (u - l = 1) || decide (u - l = 3) || decide (u - l = 9))

def row (a b c : Fin 13) : List Bool :=
  List.ofFn (fun u : Fin 13 => nl u a && nl u b && nl u c) ++
    List.ofFn (fun v : Fin 13 => decide (v = a) || decide (v = b) || decide (v = c))

def row0 : List Bool :=
  List.ofFn (fun _ : Fin 13 => true) ++ List.ofFn (fun _ : Fin 13 => false)

theorem row_len (a b c : Fin 13) : (row a b c).length = 26 := by
  simp [row]

theorem row0_len : row0.length = 26 := by
  simp [row0]

theorem row_eq (a b c : Fin 13) :
    (List.ofFn (fun u1 : Fin 13 => decide (∀ l ∈ ({a, b, c} : Finset (Fin 13)),
        u1 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))))
      ++ List.ofFn (fun v1 : Fin 13 => decide (v1 ∈ ({a, b, c} : Finset (Fin 13))))) = row a b c := by
  unfold row
  refine congrArg₂ (fun x y : List Bool => x ++ y) (congrArg List.ofFn (funext fun u => ?_))
    (congrArg List.ofFn (funext fun v => ?_))
  · rw [Bool.eq_iff_iff]
    simp [nl, and_assoc]
  · rw [Bool.eq_iff_iff]
    simp [or_assoc]

theorem row0_eq :
    (List.ofFn (fun u1 : Fin 13 => decide (∀ l ∈ (∅ : Finset (Fin 13)),
        u1 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))))
      ++ List.ofFn (fun v1 : Fin 13 => decide (v1 ∈ (∅ : Finset (Fin 13))))) = row0 := by
  unfold row0
  refine congrArg₂ (fun x y : List Bool => x ++ y) (congrArg List.ofFn (funext fun u => ?_))
    (congrArg List.ofFn (funext fun v => ?_))
  · simp
  · simp

theorem card_le3 (Y : Finset (Fin 13)) (h : Y.card ≤ 3) :
    Y = ∅ ∨ ∃ a b c : Fin 13, Y = {a, b, c} := by
  have h' : Y.card = 0 ∨ Y.card = 1 ∨ Y.card = 2 ∨ Y.card = 3 := by omega
  rcases h' with h0 | h1 | h2 | h3
  · exact Or.inl (Finset.card_eq_zero.mp h0)
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    exact Or.inr ⟨a, a, a, by simp⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h2
    exact Or.inr ⟨a, a, b, by simp⟩
  · obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp h3
    exact Or.inr ⟨a, b, c, rfl⟩

theorem neg_of (G : List Gate) (o : ℕ)
    (h0 : (run G 26 (enc row0)).testBit o = false)
    (h : ∀ a b c : Fin 13, (run G 26 (enc (row a b c))).testBit o = false) :
    ∀ Y : Finset (Fin 13), Y.card ≤ 3 →
      Circuit.eval ⟨G, o⟩ (List.ofFn (fun u1 : Fin 13 => decide (∀ l ∈ Y,
          u1 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))))
        ++ List.ofFn (fun v1 : Fin 13 => decide (v1 ∈ Y))) = false := by
  intro Y hY
  rcases card_le3 Y hY with rfl | ⟨a, b, c, rfl⟩
  · rw [row0_eq, eval26 G o _ row0_len]
    exact h0
  · rw [row_eq, eval26 G o _ (row_len a b c)]
    exact h a b c

theorem fin13 (P : Fin 13 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) : ∀ a, P a := by
  intro a
  fin_cases a
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

end PEqualNP.Outside.L_meta_1741

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1741 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [46, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [58, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [63, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [66, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 68] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [70, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [79, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [81, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [82, 53] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [84, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [85, 65] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [87, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 77] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 92] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 93] }], output := 94 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 69 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (13 + 13) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
     C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
  (∀ Y : Finset (Fin 13), Y.card ≤ 3 →
     C.eval (List.ofFn (fun u1 : Fin 13 => decide (∀ l ∈ Y, u1 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))))
             ++ List.ofFn (fun v1 : Fin 13 => decide (v1 ∈ Y))) = false) ∧
  (∀ l : Fin 13, (C.wires (List.replicate 13 false ++ List.ofFn (fun v2 : Fin 13 => decide (v2 = l)))).getD 92 false
       = decide (l = 0 ∨ l = 4)) ∧
  (C.wires (List.replicate 13 false ++ List.ofFn (fun v3 : Fin 13 => decide (v3 = 10 ∨ v3 = 12)))).getD 92 false = true := by
  intro C hC
  subst hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · refine PEqualNP.Outside.L_meta_1741.ao2_of _ ?_
    decide +kernel
  · intro p l h
    refine (PEqualNP.Outside.L_meta_1741.eval_eq _ _).trans ?_
    revert p l
    decide +kernel
  · refine PEqualNP.Outside.L_meta_1741.neg_of _ _ ?_ ?_
    · decide +kernel
    · refine PEqualNP.Outside.L_meta_1741.fin13 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
  · intro l
    refine (PEqualNP.Outside.L_meta_1741.wire_eq _ _ _).trans ?_
    revert l
    decide +kernel
  · refine (PEqualNP.Outside.L_meta_1741.wire_eq _ _ _).trans ?_
    decide +kernel
